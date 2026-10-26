import V185TrunkScan20Chunk145

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_888468 : List Nat := [2, 4, 2, 2, 2, 1, 2, 5]
def baseStart_888468 : Nat := 118140960795 + 888468 * 2 ^ 59
def prefixEnd_888468 : Nat := 4983230072969 + 3 ^ 40 * 888468 * 2
def baseEnd_888468 : Nat := 135173668189314103278227

theorem tailTrace_888468 : CollatzResearch.WordTrace tailWord_888468 prefixEnd_888468 135173668189314103278227 := by
  unfold tailWord_888468
  simp only [CollatzResearch.WordTrace]
  refine ⟨16202545072619824549505029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21603393430159766066006705 16202545072619824549505029)
  ·
    refine ⟨3037977201116217103032193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16202545072619824549505029 3037977201116217103032193)
    ·
      refine ⟨2278482900837162827274145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3037977201116217103032193 2278482900837162827274145)
      ·
        refine ⟨1708862175627872120455609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2278482900837162827274145 1708862175627872120455609)
        ·
          refine ⟨1281646631720904090341707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1708862175627872120455609 1281646631720904090341707)
          ·
            refine ⟨1922469947581356135512561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281646631720904090341707 1922469947581356135512561)
            ·
              refine ⟨1441852460686017101634421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1922469947581356135512561 1441852460686017101634421)
              ·
                refine ⟨135173668189314103278227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1441852460686017101634421 135173668189314103278227)
                ·
                  rfl

theorem cell20_888468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_888468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888468 prefixEnd_888468 := by exact prefixLift 888468
  have htrace : WordTrace (prefixWord ++ tailWord_888468) baseStart_888468 baseEnd_888468 := by
    simpa [prefixWord, tailWord_888468, baseEnd_888468] using wordTrace_append hprefix tailTrace_888468
  have hstable : (prefixWord ++ tailWord_888468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888468).length < 2 ^ (prefixWord ++ tailWord_888468).sum := by decide
  have hdescent : baseEnd_888468 < baseStart_888468 := by decide
  rcases family_descends (prefixWord ++ tailWord_888468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888472 : List Nat := [2, 1, 2, 4, 1, 2, 1, 7]
def baseStart_888472 : Nat := 118140960795 + 888472 * 2 ^ 59
def prefixEnd_888472 : Nat := 4983230072969 + 3 ^ 40 * 888472 * 2
def baseEnd_888472 : Nat := 135174276758978691233777

theorem tailTrace_888472 : CollatzResearch.WordTrace tailWord_888472 prefixEnd_888472 135174276758978691233777 := by
  unfold tailWord_888472
  simp only [CollatzResearch.WordTrace]
  refine ⟨16202618018612578891077835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21603490691483438521437113 16202618018612578891077835)
  ·
    refine ⟨24303927027918868336616753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16202618018612578891077835 24303927027918868336616753)
    ·
      refine ⟨18227945270939151252462565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24303927027918868336616753 18227945270939151252462565)
      ·
        refine ⟨3417739738301090859836731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18227945270939151252462565 3417739738301090859836731)
        ·
          refine ⟨5126609607451636289755097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3417739738301090859836731 5126609607451636289755097)
          ·
            refine ⟨3844957205588727217316323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5126609607451636289755097 3844957205588727217316323)
            ·
              refine ⟨5767435808383090825974485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3844957205588727217316323 5767435808383090825974485)
              ·
                refine ⟨135174276758978691233777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5767435808383090825974485 135174276758978691233777)
                ·
                  rfl

theorem cell20_888472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_888472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888472 prefixEnd_888472 := by exact prefixLift 888472
  have htrace : WordTrace (prefixWord ++ tailWord_888472) baseStart_888472 baseEnd_888472 := by
    simpa [prefixWord, tailWord_888472, baseEnd_888472] using wordTrace_append hprefix tailTrace_888472
  have hstable : (prefixWord ++ tailWord_888472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888472).length < 2 ^ (prefixWord ++ tailWord_888472).sum := by decide
  have hdescent : baseEnd_888472 < baseStart_888472 := by decide
  rcases family_descends (prefixWord ++ tailWord_888472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888510 : List Nat := [4, 2, 1, 1, 2, 10]
def baseStart_888510 : Nat := 118140960795 + 888510 * 2 ^ 59
def prefixEnd_888510 : Nat := 4983230072969 + 3 ^ 40 * 888510 * 2
def baseEnd_888510 : Nat := 15020006463421364090167

theorem tailTrace_888510 : CollatzResearch.WordTrace tailWord_888510 prefixEnd_888510 15020006463421364090167 := by
  unfold tailWord_888510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4050827751385936284004873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21604414674058326848025989 4050827751385936284004873)
  ·
    refine ⟨3038120813539452213003655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4050827751385936284004873 3038120813539452213003655)
    ·
      refine ⟨4557181220309178319505483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3038120813539452213003655 4557181220309178319505483)
      ·
        refine ⟨6835771830463767479258225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4557181220309178319505483 6835771830463767479258225)
        ·
          refine ⟨5126828872847825609443669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6835771830463767479258225 5126828872847825609443669)
          ·
            refine ⟨15020006463421364090167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5126828872847825609443669 15020006463421364090167)
            ·
              rfl

theorem cell20_888510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 10].length) (baseStart_888510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888510 prefixEnd_888510 := by exact prefixLift 888510
  have htrace : WordTrace (prefixWord ++ tailWord_888510) baseStart_888510 baseEnd_888510 := by
    simpa [prefixWord, tailWord_888510, baseEnd_888510] using wordTrace_append hprefix tailTrace_888510
  have hstable : (prefixWord ++ tailWord_888510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888510).length < 2 ^ (prefixWord ++ tailWord_888510).sum := by decide
  have hdescent : baseEnd_888510 < baseStart_888510 := by decide
  rcases family_descends (prefixWord ++ tailWord_888510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888520 : List Nat := [2, 1, 3, 1, 2, 2, 3, 4, 2]
def baseStart_888520 : Nat := 118140960795 + 888520 * 2 ^ 59
def prefixEnd_888520 : Nat := 4983230072969 + 3 ^ 40 * 888520 * 2
def baseEnd_888520 : Nat := 405544738784861240101135

theorem tailTrace_888520 : CollatzResearch.WordTrace tailWord_888520 prefixEnd_888520 405544738784861240101135 := by
  unfold tailWord_888520
  simp only [CollatzResearch.WordTrace]
  refine ⟨16203493370525630989951507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21604657827367507986602009 16203493370525630989951507)
  ·
    refine ⟨24305240055788446484927261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16203493370525630989951507 24305240055788446484927261)
    ·
      refine ⟨9114465020920667431847723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24305240055788446484927261 9114465020920667431847723)
      ·
        refine ⟨13671697531381001147771585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9114465020920667431847723 13671697531381001147771585)
        ·
          refine ⟨10253773148535750860828689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13671697531381001147771585 10253773148535750860828689)
          ·
            refine ⟨7690329861401813145621517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10253773148535750860828689 7690329861401813145621517)
            ·
              refine ⟨2883873698025679929608069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7690329861401813145621517 2883873698025679929608069)
              ·
                refine ⟨540726318379814986801513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2883873698025679929608069 540726318379814986801513)
                ·
                  refine ⟨405544738784861240101135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540726318379814986801513 405544738784861240101135)
                  ·
                    rfl

theorem cell20_888520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 2].length) (baseStart_888520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888520 prefixEnd_888520 := by exact prefixLift 888520
  have htrace : WordTrace (prefixWord ++ tailWord_888520) baseStart_888520 baseEnd_888520 := by
    simpa [prefixWord, tailWord_888520, baseEnd_888520] using wordTrace_append hprefix tailTrace_888520
  have hstable : (prefixWord ++ tailWord_888520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888520).length < 2 ^ (prefixWord ++ tailWord_888520).sum := by decide
  have hdescent : baseEnd_888520 < baseStart_888520 := by decide
  rcases family_descends (prefixWord ++ tailWord_888520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888613 : List Nat := [1, 3, 1, 2, 3, 4, 1, 3, 2]
def baseStart_888613 : Nat := 118140960795 + 888613 * 2 ^ 59
def prefixEnd_888613 : Nat := 4983230072969 + 3 ^ 40 * 888613 * 2
def baseEnd_888613 : Nat := 405587186518966250000755

theorem tailTrace_888613 : CollatzResearch.WordTrace tailWord_888613 prefixEnd_888613 405587186518966250000755 := by
  unfold tailWord_888613
  simp only [CollatzResearch.WordTrace]
  refine ⟨32410378729714338863038493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21606919153142892575358995 32410378729714338863038493)
  ·
    refine ⟨12153892023642877073639435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32410378729714338863038493 12153892023642877073639435)
    ·
      refine ⟨18230838035464315610459153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12153892023642877073639435 18230838035464315610459153)
      ·
        refine ⟨13673128526598236707844365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18230838035464315610459153 13673128526598236707844365)
        ·
          refine ⟨5127423197474338765441637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13673128526598236707844365 5127423197474338765441637)
          ·
            refine ⟨961391849526438518520307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5127423197474338765441637 961391849526438518520307)
            ·
              refine ⟨1442087774289657777780461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961391849526438518520307 1442087774289657777780461)
              ·
                refine ⟨540782915358621666667673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1442087774289657777780461 540782915358621666667673)
                ·
                  refine ⟨405587186518966250000755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540782915358621666667673 405587186518966250000755)
                  ·
                    rfl

theorem cell20_888613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_888613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888613 prefixEnd_888613 := by exact prefixLift 888613
  have htrace : WordTrace (prefixWord ++ tailWord_888613) baseStart_888613 baseEnd_888613 := by
    simpa [prefixWord, tailWord_888613, baseEnd_888613] using wordTrace_append hprefix tailTrace_888613
  have hstable : (prefixWord ++ tailWord_888613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888613).length < 2 ^ (prefixWord ++ tailWord_888613).sum := by decide
  have hdescent : baseEnd_888613 < baseStart_888613 := by decide
  rcases family_descends (prefixWord ++ tailWord_888613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888634 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 4]
def baseStart_888634 : Nat := 118140960795 + 888634 * 2 ^ 59
def prefixEnd_888634 : Nat := 4983230072969 + 3 ^ 40 * 888634 * 2
def baseEnd_888634 : Nat := 405596771491183510300669

theorem tailTrace_888634 : CollatzResearch.WordTrace tailWord_888634 prefixEnd_888634 405596771491183510300669 := by
  unfold tailWord_888634
  simp only [CollatzResearch.WordTrace]
  refine ⟨8102786165659564862388239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21607429775092172966368637 8102786165659564862388239)
  ·
    refine ⟨12154179248489347293582359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8102786165659564862388239 12154179248489347293582359)
    ·
      refine ⟨18231268872734020940373539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12154179248489347293582359 18231268872734020940373539)
      ·
        refine ⟨27346903309101031410560309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18231268872734020940373539 27346903309101031410560309)
        ·
          refine ⟨2563772185228221694740029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27346903309101031410560309 2563772185228221694740029)
          ·
            refine ⟨961414569460583135527511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2563772185228221694740029 961414569460583135527511)
            ·
              refine ⟨1442121854190874703291267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961414569460583135527511 1442121854190874703291267)
              ·
                refine ⟨2163182781286312054936901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442121854190874703291267 2163182781286312054936901)
                ·
                  refine ⟨405596771491183510300669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2163182781286312054936901 405596771491183510300669)
                  ·
                    rfl

theorem cell20_888634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_888634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888634 prefixEnd_888634 := by exact prefixLift 888634
  have htrace : WordTrace (prefixWord ++ tailWord_888634) baseStart_888634 baseEnd_888634 := by
    simpa [prefixWord, tailWord_888634, baseEnd_888634] using wordTrace_append hprefix tailTrace_888634
  have hstable : (prefixWord ++ tailWord_888634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888634).length < 2 ^ (prefixWord ++ tailWord_888634).sum := by decide
  have hdescent : baseEnd_888634 < baseStart_888634 := by decide
  rcases family_descends (prefixWord ++ tailWord_888634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888648 : List Nat := [2, 1, 3, 1, 1, 5, 1, 3, 3]
def baseStart_888648 : Nat := 118140960795 + 888648 * 2 ^ 59
def prefixEnd_888648 : Nat := 4983230072969 + 3 ^ 40 * 888648 * 2
def baseEnd_888648 : Nat := 405603161472661683833945

theorem tailTrace_888648 : CollatzResearch.WordTrace tailWord_888648 prefixEnd_888648 405603161472661683833945 := by
  unfold tailWord_888648
  simp only [CollatzResearch.WordTrace]
  refine ⟨16205827642293769920281299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21607770189725026560375065 16205827642293769920281299)
  ·
    refine ⟨24308741463440654880421949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16205827642293769920281299 24308741463440654880421949)
    ·
      refine ⟨9115778048790245580158231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24308741463440654880421949 9115778048790245580158231)
      ·
        refine ⟨13673667073185368370237347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9115778048790245580158231 13673667073185368370237347)
        ·
          refine ⟨20510500609778052555356021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13673667073185368370237347 20510500609778052555356021)
          ·
            refine ⟨1922859432166692427064627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20510500609778052555356021 1922859432166692427064627)
            ·
              refine ⟨2884289148250038640596941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1922859432166692427064627 2884289148250038640596941)
              ·
                refine ⟨1081608430593764490223853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2884289148250038640596941 1081608430593764490223853)
                ·
                  refine ⟨405603161472661683833945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081608430593764490223853 405603161472661683833945)
                  ·
                    rfl

theorem cell20_888648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_888648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888648 prefixEnd_888648 := by exact prefixLift 888648
  have htrace : WordTrace (prefixWord ++ tailWord_888648) baseStart_888648 baseEnd_888648 := by
    simpa [prefixWord, tailWord_888648, baseEnd_888648] using wordTrace_append hprefix tailTrace_888648
  have hstable : (prefixWord ++ tailWord_888648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888648).length < 2 ^ (prefixWord ++ tailWord_888648).sum := by decide
  have hdescent : baseEnd_888648 < baseStart_888648 := by decide
  rcases family_descends (prefixWord ++ tailWord_888648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888682 : List Nat := [3, 1, 3, 4, 1, 1, 2, 2, 3]
def baseStart_888682 : Nat := 118140960795 + 888682 * 2 ^ 59
def prefixEnd_888682 : Nat := 4983230072969 + 3 ^ 40 * 888682 * 2
def baseEnd_888682 : Nat := 405618679999108676700473

theorem tailTrace_888682 : CollatzResearch.WordTrace tailWord_888682 prefixEnd_888682 405618679999108676700473 := by
  unfold tailWord_888682
  simp only [CollatzResearch.WordTrace]
  refine ⟨8103223841616090911825075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21608596910976242431533533 8103223841616090911825075)
  ·
    refine ⟨12154835762424136367737613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8103223841616090911825075 12154835762424136367737613)
    ·
      refine ⟨4558063410909051137901605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12154835762424136367737613 4558063410909051137901605)
      ·
        refine ⟨854636889545447088356551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4558063410909051137901605 854636889545447088356551)
        ·
          refine ⟨1281955334318170632534827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854636889545447088356551 1281955334318170632534827)
          ·
            refine ⟨1922933001477255948802241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281955334318170632534827 1922933001477255948802241)
            ·
              refine ⟨1442199751107941961601681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1922933001477255948802241 1442199751107941961601681)
              ·
                refine ⟨1081649813330956471201261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1442199751107941961601681 1081649813330956471201261)
                ·
                  refine ⟨405618679999108676700473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081649813330956471201261 405618679999108676700473)
                  ·
                    rfl

theorem cell20_888682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_888682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888682 prefixEnd_888682 := by exact prefixLift 888682
  have htrace : WordTrace (prefixWord ++ tailWord_888682) baseStart_888682 baseEnd_888682 := by
    simpa [prefixWord, tailWord_888682, baseEnd_888682] using wordTrace_append hprefix tailTrace_888682
  have hstable : (prefixWord ++ tailWord_888682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888682).length < 2 ^ (prefixWord ++ tailWord_888682).sum := by decide
  have hdescent : baseEnd_888682 < baseStart_888682 := by decide
  rcases family_descends (prefixWord ++ tailWord_888682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888693 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 4]
def baseStart_888693 : Nat := 118140960795 + 888693 * 2 ^ 59
def prefixEnd_888693 : Nat := 4983230072969 + 3 ^ 40 * 888693 * 2
def baseEnd_888693 : Nat := 405623700698841527333761

theorem tailTrace_888693 : CollatzResearch.WordTrace tailWord_888693 prefixEnd_888693 405623700698841527333761 := by
  unfold tailWord_888693
  simp only [CollatzResearch.WordTrace]
  refine ⟨32413296569424512525950733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21608864379616341683967155 32413296569424512525950733)
  ·
    refine ⟨12154986213534192197231525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32413296569424512525950733 12154986213534192197231525)
    ·
      refine ⟨2279059915037661036980911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12154986213534192197231525 2279059915037661036980911)
      ·
        refine ⟨3418589872556491555471367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2279059915037661036980911 3418589872556491555471367)
        ·
          refine ⟨5127884808834737333207051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3418589872556491555471367 5127884808834737333207051)
          ·
            refine ⟨7691827213252105999810577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5127884808834737333207051 7691827213252105999810577)
            ·
              refine ⟨5768870409939079499857933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7691827213252105999810577 5768870409939079499857933)
              ·
                refine ⟨2163326403727154812446725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5768870409939079499857933 2163326403727154812446725)
                ·
                  refine ⟨405623700698841527333761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2163326403727154812446725 405623700698841527333761)
                  ·
                    rfl

theorem cell20_888693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_888693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888693 prefixEnd_888693 := by exact prefixLift 888693
  have htrace : WordTrace (prefixWord ++ tailWord_888693) baseStart_888693 baseEnd_888693 := by
    simpa [prefixWord, tailWord_888693, baseEnd_888693] using wordTrace_append hprefix tailTrace_888693
  have hstable : (prefixWord ++ tailWord_888693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888693).length < 2 ^ (prefixWord ++ tailWord_888693).sum := by decide
  have hdescent : baseEnd_888693 < baseStart_888693 := by decide
  rcases family_descends (prefixWord ++ tailWord_888693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888721 : List Nat := [1, 2, 2, 1, 1, 1, 4, 8]
def baseStart_888721 : Nat := 118140960795 + 888721 * 2 ^ 59
def prefixEnd_888721 : Nat := 4983230072969 + 3 ^ 40 * 888721 * 2
def baseEnd_888721 : Nat := 135212160220599291466771

theorem tailTrace_888721 : CollatzResearch.WordTrace tailWord_888721 prefixEnd_888721 135212160220599291466771 := by
  unfold tailWord_888721
  simp only [CollatzResearch.WordTrace]
  refine ⟨32414317813323073307970017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21609545208882048871980011 32414317813323073307970017)
  ·
    refine ⟨24310738359992304980977513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32414317813323073307970017 24310738359992304980977513)
    ·
      refine ⟨18233053769994228735733135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24310738359992304980977513 18233053769994228735733135)
      ·
        refine ⟨27349580654991343103599703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18233053769994228735733135 27349580654991343103599703)
        ·
          refine ⟨41024370982487014655399555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27349580654991343103599703 41024370982487014655399555)
          ·
            refine ⟨61536556473730521983099333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41024370982487014655399555 61536556473730521983099333)
            ·
              refine ⟨11538104338824472871831125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61536556473730521983099333 11538104338824472871831125)
              ·
                refine ⟨135212160220599291466771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11538104338824472871831125 135212160220599291466771)
                ·
                  rfl

theorem cell20_888721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 8].length) (baseStart_888721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888721 prefixEnd_888721 := by exact prefixLift 888721
  have htrace : WordTrace (prefixWord ++ tailWord_888721) baseStart_888721 baseEnd_888721 := by
    simpa [prefixWord, tailWord_888721, baseEnd_888721] using wordTrace_append hprefix tailTrace_888721
  have hstable : (prefixWord ++ tailWord_888721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888721).length < 2 ^ (prefixWord ++ tailWord_888721).sum := by decide
  have hdescent : baseEnd_888721 < baseStart_888721 := by decide
  rcases family_descends (prefixWord ++ tailWord_888721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888734 : List Nat := [4, 3, 1, 3, 1, 1, 7]
def baseStart_888734 : Nat := 118140960795 + 888734 * 2 ^ 59
def prefixEnd_888734 : Nat := 4983230072969 + 3 ^ 40 * 888734 * 2
def baseEnd_888734 : Nat := 45071379357336400774103

theorem tailTrace_888734 : CollatzResearch.WordTrace tailWord_888734 prefixEnd_888734 45071379357336400774103 := by
  unfold tailWord_888734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4051848995284497066024157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21609861308183984352128837 4051848995284497066024157)
  ·
    refine ⟨1519443373231686399759059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4051848995284497066024157 1519443373231686399759059)
    ·
      refine ⟨2279165059847529599638589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1519443373231686399759059 2279165059847529599638589)
      ·
        refine ⟨854686897442823599864471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2279165059847529599638589 854686897442823599864471)
        ·
          refine ⟨1282030346164235399796707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854686897442823599864471 1282030346164235399796707)
          ·
            refine ⟨1923045519246353099695061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282030346164235399796707 1923045519246353099695061)
            ·
              refine ⟨45071379357336400774103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1923045519246353099695061 45071379357336400774103)
              ·
                rfl

theorem cell20_888734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 7].length) (baseStart_888734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888734 prefixEnd_888734 := by exact prefixLift 888734
  have htrace : WordTrace (prefixWord ++ tailWord_888734) baseStart_888734 baseEnd_888734 := by
    simpa [prefixWord, tailWord_888734, baseEnd_888734] using wordTrace_append hprefix tailTrace_888734
  have hstable : (prefixWord ++ tailWord_888734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888734).length < 2 ^ (prefixWord ++ tailWord_888734).sum := by decide
  have hdescent : baseEnd_888734 < baseStart_888734 := by decide
  rcases family_descends (prefixWord ++ tailWord_888734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888745 : List Nat := [1, 2, 1, 1, 1, 1, 4, 6, 3]
def baseStart_888745 : Nat := 118140960795 + 888745 * 2 ^ 59
def prefixEnd_888745 : Nat := 4983230072969 + 3 ^ 40 * 888745 * 2
def baseEnd_888745 : Nat := 405647434915760457600215

theorem tailTrace_888745 : CollatzResearch.WordTrace tailWord_888745 prefixEnd_888745 405647434915760457600215 := by
  unfold tailWord_888745
  simp only [CollatzResearch.WordTrace]
  refine ⟨32415193165236125406843689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21610128776824083604562459 32415193165236125406843689)
  ·
    refine ⟨24311394873927094055132767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32415193165236125406843689 24311394873927094055132767)
    ·
      refine ⟨36467092310890641082699151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24311394873927094055132767 36467092310890641082699151)
      ·
        refine ⟨54700638466335961624048727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36467092310890641082699151 54700638466335961624048727)
        ·
          refine ⟨82050957699503942436073091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54700638466335961624048727 82050957699503942436073091)
          ·
            refine ⟨123076436549255913654109637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82050957699503942436073091 123076436549255913654109637)
            ·
              refine ⟨23076831852985483810145557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123076436549255913654109637 23076831852985483810145557)
              ·
                refine ⟨1081726493108694553600573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23076831852985483810145557 1081726493108694553600573)
                ·
                  refine ⟨405647434915760457600215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081726493108694553600573 405647434915760457600215)
                  ·
                    rfl

theorem cell20_888745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_888745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888745 prefixEnd_888745 := by exact prefixLift 888745
  have htrace : WordTrace (prefixWord ++ tailWord_888745) baseStart_888745 baseEnd_888745 := by
    simpa [prefixWord, tailWord_888745, baseEnd_888745] using wordTrace_append hprefix tailTrace_888745
  have hstable : (prefixWord ++ tailWord_888745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888745).length < 2 ^ (prefixWord ++ tailWord_888745).sum := by decide
  have hdescent : baseEnd_888745 < baseStart_888745 := by decide
  rcases family_descends (prefixWord ++ tailWord_888745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888759 : List Nat := [1, 1, 3, 1, 3, 1, 1, 9]
def baseStart_888759 : Nat := 118140960795 + 888759 * 2 ^ 59
def prefixEnd_888759 : Nat := 4983230072969 + 3 ^ 40 * 888759 * 2
def baseEnd_888759 : Nat := 135217941632412877044497

theorem tailTrace_888759 : CollatzResearch.WordTrace tailWord_888759 prefixEnd_888759 135217941632412877044497 := by
  unfold tailWord_888759
  simp only [CollatzResearch.WordTrace]
  refine ⟨32415703787185405797853331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21610469191456937198568887 32415703787185405797853331)
  ·
    refine ⟨48623555680778108696779997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32415703787185405797853331 48623555680778108696779997)
    ·
      refine ⟨18233833380291790761292499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48623555680778108696779997 18233833380291790761292499)
      ·
        refine ⟨27350750070437686141938749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18233833380291790761292499 27350750070437686141938749)
        ·
          refine ⟨10256531276414132303227031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27350750070437686141938749 10256531276414132303227031)
          ·
            refine ⟨15384796914621198454840547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10256531276414132303227031 15384796914621198454840547)
            ·
              refine ⟨23077195371931797682260821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15384796914621198454840547 23077195371931797682260821)
              ·
                refine ⟨135217941632412877044497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23077195371931797682260821 135217941632412877044497)
                ·
                  rfl

theorem cell20_888759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 9].length) (baseStart_888759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888759 prefixEnd_888759 := by exact prefixLift 888759
  have htrace : WordTrace (prefixWord ++ tailWord_888759) baseStart_888759 baseEnd_888759 := by
    simpa [prefixWord, tailWord_888759, baseEnd_888759] using wordTrace_append hprefix tailTrace_888759
  have hstable : (prefixWord ++ tailWord_888759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888759).length < 2 ^ (prefixWord ++ tailWord_888759).sum := by decide
  have hdescent : baseEnd_888759 < baseStart_888759 := by decide
  rcases family_descends (prefixWord ++ tailWord_888759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888776 : List Nat := [2, 1, 3, 1, 4, 2, 1, 6]
def baseStart_888776 : Nat := 118140960795 + 888776 * 2 ^ 59
def prefixEnd_888776 : Nat := 4983230072969 + 3 ^ 40 * 888776 * 2
def baseEnd_888776 : Nat := 135220528053487375855585

theorem tailTrace_888776 : CollatzResearch.WordTrace tailWord_888776 prefixEnd_888776 135220528053487375855585 := by
  unfold tailWord_888776
  simp only [CollatzResearch.WordTrace]
  refine ⟨16208161914061908850611091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21610882552082545134148121 16208161914061908850611091)
  ·
    refine ⟨24312242871092863275916637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16208161914061908850611091 24312242871092863275916637)
    ·
      refine ⟨9117091076659823728468739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24312242871092863275916637 9117091076659823728468739)
      ·
        refine ⟨13675636614989735592703109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9117091076659823728468739 13675636614989735592703109)
        ·
          refine ⟨2564181865310575423631833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13675636614989735592703109 2564181865310575423631833)
          ·
            refine ⟨1923136398982931567723875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2564181865310575423631833 1923136398982931567723875)
            ·
              refine ⟨2884704598474397351585813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923136398982931567723875 2884704598474397351585813)
              ·
                refine ⟨135220528053487375855585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2884704598474397351585813 135220528053487375855585)
                ·
                  rfl

theorem cell20_888776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_888776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888776 prefixEnd_888776 := by exact prefixLift 888776
  have htrace : WordTrace (prefixWord ++ tailWord_888776) baseStart_888776 baseEnd_888776 := by
    simpa [prefixWord, tailWord_888776, baseEnd_888776] using wordTrace_append hprefix tailTrace_888776
  have hstable : (prefixWord ++ tailWord_888776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888776).length < 2 ^ (prefixWord ++ tailWord_888776).sum := by decide
  have hdescent : baseEnd_888776 < baseStart_888776 := by decide
  rcases family_descends (prefixWord ++ tailWord_888776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888793 : List Nat := [1, 2, 1, 2, 7, 1, 6]
def baseStart_888793 : Nat := 118140960795 + 888793 * 2 ^ 59
def prefixEnd_888793 : Nat := 4983230072969 + 3 ^ 40 * 888793 * 2
def baseEnd_888793 : Nat := 45074371491520624888891

theorem tailTrace_888793 : CollatzResearch.WordTrace tailWord_888793 prefixEnd_888793 45074371491520624888891 := by
  unfold tailWord_888793
  simp only [CollatzResearch.WordTrace]
  refine ⟨32416943869062229604591033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21611295912708153069727355 32416943869062229604591033)
  ·
    refine ⟨24312707901796672203443275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32416943869062229604591033 24312707901796672203443275)
    ·
      refine ⟨36469061852695008305164913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24312707901796672203443275 36469061852695008305164913)
      ·
        refine ⟨27351796389521256228873685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36469061852695008305164913 27351796389521256228873685)
        ·
          refine ⟨641057727879404442864227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27351796389521256228873685 641057727879404442864227)
          ·
            refine ⟨961586591819106664296341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641057727879404442864227 961586591819106664296341)
            ·
              refine ⟨45074371491520624888891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 961586591819106664296341 45074371491520624888891)
              ·
                rfl

theorem cell20_888793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 6].length) (baseStart_888793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888793 prefixEnd_888793 := by exact prefixLift 888793
  have htrace : WordTrace (prefixWord ++ tailWord_888793) baseStart_888793 baseEnd_888793 := by
    simpa [prefixWord, tailWord_888793, baseEnd_888793] using wordTrace_append hprefix tailTrace_888793
  have hstable : (prefixWord ++ tailWord_888793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888793).length < 2 ^ (prefixWord ++ tailWord_888793).sum := by decide
  have hdescent : baseEnd_888793 < baseStart_888793 := by decide
  rcases family_descends (prefixWord ++ tailWord_888793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888803 : List Nat := [1, 1, 1, 6, 1, 3, 3, 2, 2]
def baseStart_888803 : Nat := 118140960795 + 888803 * 2 ^ 59
def prefixEnd_888803 : Nat := 4983230072969 + 3 ^ 40 * 888803 * 2
def baseEnd_888803 : Nat := 405673907696170033666645

theorem tailTrace_888803 : CollatzResearch.WordTrace tailWord_888803 prefixEnd_888803 405673907696170033666645 := by
  unfold tailWord_888803
  simp only [CollatzResearch.WordTrace]
  refine ⟨32417308599026001312455063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21611539066017334208303375 32417308599026001312455063)
  ·
    refine ⟨48625962898539001968682595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32417308599026001312455063 48625962898539001968682595)
    ·
      refine ⟨72938944347808502953023893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48625962898539001968682595 72938944347808502953023893)
      ·
        refine ⟨3419013016303523575922995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72938944347808502953023893 3419013016303523575922995)
        ·
          refine ⟨5128519524455285363884493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3419013016303523575922995 5128519524455285363884493)
          ·
            refine ⟨1923194821670732011456685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5128519524455285363884493 1923194821670732011456685)
            ·
              refine ⟨721198058126524504296257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1923194821670732011456685 721198058126524504296257)
              ·
                refine ⟨540898543594893378222193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 721198058126524504296257 540898543594893378222193)
                ·
                  refine ⟨405673907696170033666645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540898543594893378222193 405673907696170033666645)
                  ·
                    rfl

theorem cell20_888803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 2].length) (baseStart_888803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888803 prefixEnd_888803 := by exact prefixLift 888803
  have htrace : WordTrace (prefixWord ++ tailWord_888803) baseStart_888803 baseEnd_888803 := by
    simpa [prefixWord, tailWord_888803, baseEnd_888803] using wordTrace_append hprefix tailTrace_888803
  have hstable : (prefixWord ++ tailWord_888803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888803).length < 2 ^ (prefixWord ++ tailWord_888803).sum := by decide
  have hdescent : baseEnd_888803 < baseStart_888803 := by decide
  rcases family_descends (prefixWord ++ tailWord_888803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888813 : List Nat := [1, 5, 1, 4, 1, 2, 2, 1, 3]
def baseStart_888813 : Nat := 118140960795 + 888813 * 2 ^ 59
def prefixEnd_888813 : Nat := 4983230072969 + 3 ^ 40 * 888813 * 2
def baseEnd_888813 : Nat := 405678471968654443333271

theorem tailTrace_888813 : CollatzResearch.WordTrace tailWord_888813 prefixEnd_888813 405678471968654443333271 := by
  unfold tailWord_888813
  simp only [CollatzResearch.WordTrace]
  refine ⟨32417673328989773020319093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21611782219326515346879395 32417673328989773020319093)
  ·
    refine ⟨3039156874592791220654915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32417673328989773020319093 3039156874592791220654915)
    ·
      refine ⟨4558735311889186830982373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3039156874592791220654915 4558735311889186830982373)
      ·
        refine ⟨854762870979222530809195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4558735311889186830982373 854762870979222530809195)
        ·
          refine ⟨1282144306468833796213793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854762870979222530809195 1282144306468833796213793)
          ·
            refine ⟨961608229851625347160345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1282144306468833796213793 961608229851625347160345)
            ·
              refine ⟨721206172388719010370259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 961608229851625347160345 721206172388719010370259)
              ·
                refine ⟨1081809258583078515555389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721206172388719010370259 1081809258583078515555389)
                ·
                  refine ⟨405678471968654443333271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081809258583078515555389 405678471968654443333271)
                  ·
                    rfl

theorem cell20_888813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_888813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888813 prefixEnd_888813 := by exact prefixLift 888813
  have htrace : WordTrace (prefixWord ++ tailWord_888813) baseStart_888813 baseEnd_888813 := by
    simpa [prefixWord, tailWord_888813, baseEnd_888813] using wordTrace_append hprefix tailTrace_888813
  have hstable : (prefixWord ++ tailWord_888813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888813).length < 2 ^ (prefixWord ++ tailWord_888813).sum := by decide
  have hdescent : baseEnd_888813 < baseStart_888813 := by decide
  rcases family_descends (prefixWord ++ tailWord_888813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888814 : List Nat := [4, 1, 2, 1, 3, 1, 1, 7]
def baseStart_888814 : Nat := 118140960795 + 888814 * 2 ^ 59
def prefixEnd_888814 : Nat := 4983230072969 + 3 ^ 40 * 888814 * 2
def baseEnd_888814 : Nat := 135226309465300961433311

theorem tailTrace_888814 : CollatzResearch.WordTrace tailWord_888814 prefixEnd_888814 135226309465300961433311 := by
  unfold tailWord_888814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4052213725248268773888187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21611806534657433460736997 4052213725248268773888187)
  ·
    refine ⟨6078320587872403160832281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4052213725248268773888187 6078320587872403160832281)
    ·
      refine ⟨4558740440904302370624211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6078320587872403160832281 4558740440904302370624211)
      ·
        refine ⟨6838110661356453555936317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4558740440904302370624211 6838110661356453555936317)
        ·
          refine ⟨2564291498008670083476119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6838110661356453555936317 2564291498008670083476119)
          ·
            refine ⟨3846437247013005125214179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2564291498008670083476119 3846437247013005125214179)
            ·
              refine ⟨5769655870519507687821269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3846437247013005125214179 5769655870519507687821269)
              ·
                refine ⟨135226309465300961433311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5769655870519507687821269 135226309465300961433311)
                ·
                  rfl

theorem cell20_888814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_888814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888814 prefixEnd_888814 := by exact prefixLift 888814
  have htrace : WordTrace (prefixWord ++ tailWord_888814) baseStart_888814 baseEnd_888814 := by
    simpa [prefixWord, tailWord_888814, baseEnd_888814] using wordTrace_append hprefix tailTrace_888814
  have hstable : (prefixWord ++ tailWord_888814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888814).length < 2 ^ (prefixWord ++ tailWord_888814).sum := by decide
  have hdescent : baseEnd_888814 < baseStart_888814 := by decide
  rcases family_descends (prefixWord ++ tailWord_888814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888828 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 6]
def baseStart_888828 : Nat := 118140960795 + 888828 * 2 ^ 59
def prefixEnd_888828 : Nat := 4983230072969 + 3 ^ 40 * 888828 * 2
def baseEnd_888828 : Nat := 405685318377381057833209

theorem tailTrace_888828 : CollatzResearch.WordTrace tailWord_888828 prefixEnd_888828 405685318377381057833209 := by
  unfold tailWord_888828
  simp only [CollatzResearch.WordTrace]
  refine ⟨16209110211967715291057569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21612146949290287054743425 16209110211967715291057569)
  ·
    refine ⟨12156832658975786468293177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16209110211967715291057569 12156832658975786468293177)
    ·
      refine ⟨9117624494231839851219883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12156832658975786468293177 9117624494231839851219883)
      ·
        refine ⟨13676436741347759776829825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9117624494231839851219883 13676436741347759776829825)
        ·
          refine ⟨10257327556010819832622369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13676436741347759776829825 10257327556010819832622369)
          ·
            refine ⟨7692995667008114874466777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10257327556010819832622369 7692995667008114874466777)
            ·
              refine ⟨5769746750256086155850083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7692995667008114874466777 5769746750256086155850083)
              ·
                refine ⟨8654620125384129233775125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5769746750256086155850083 8654620125384129233775125)
                ·
                  refine ⟨405685318377381057833209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8654620125384129233775125 405685318377381057833209)
                  ·
                    rfl

theorem cell20_888828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_888828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888828 prefixEnd_888828 := by exact prefixLift 888828
  have htrace : WordTrace (prefixWord ++ tailWord_888828) baseStart_888828 baseEnd_888828 := by
    simpa [prefixWord, tailWord_888828, baseEnd_888828] using wordTrace_append hprefix tailTrace_888828
  have hstable : (prefixWord ++ tailWord_888828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888828).length < 2 ^ (prefixWord ++ tailWord_888828).sum := by decide
  have hdescent : baseEnd_888828 < baseStart_888828 := by decide
  rcases family_descends (prefixWord ++ tailWord_888828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888855 : List Nat := [1, 1, 3, 5, 2, 1, 2, 2, 3]
def baseStart_888855 : Nat := 118140960795 + 888855 * 2 ^ 59
def prefixEnd_888855 : Nat := 4983230072969 + 3 ^ 40 * 888855 * 2
def baseEnd_888855 : Nat := 405697641913088963933099

theorem tailTrace_888855 : CollatzResearch.WordTrace tailWord_888855 prefixEnd_888855 405697641913088963933099 := by
  unfold tailWord_888855
  simp only [CollatzResearch.WordTrace]
  refine ⟨32419205194837614193348019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21612803463225076128898679 32419205194837614193348019)
  ·
    refine ⟨48628807792256421290022029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32419205194837614193348019 48628807792256421290022029)
    ·
      refine ⟨18235802922096157983758261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48628807792256421290022029 18235802922096157983758261)
      ·
        refine ⟨1709606523946514810977337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18235802922096157983758261 1709606523946514810977337)
        ·
          refine ⟨1282204892959886108233003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1709606523946514810977337 1282204892959886108233003)
          ·
            refine ⟨1923307339439829162349505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282204892959886108233003 1923307339439829162349505)
            ·
              refine ⟨1442480504579871871762129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1923307339439829162349505 1442480504579871871762129)
              ·
                refine ⟨1081860378434903903821597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1442480504579871871762129 1081860378434903903821597)
                ·
                  refine ⟨405697641913088963933099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081860378434903903821597 405697641913088963933099)
                  ·
                    rfl

theorem cell20_888855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 3].length) (baseStart_888855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888855 prefixEnd_888855 := by exact prefixLift 888855
  have htrace : WordTrace (prefixWord ++ tailWord_888855) baseStart_888855 baseEnd_888855 := by
    simpa [prefixWord, tailWord_888855, baseEnd_888855] using wordTrace_append hprefix tailTrace_888855
  have hstable : (prefixWord ++ tailWord_888855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888855).length < 2 ^ (prefixWord ++ tailWord_888855).sum := by decide
  have hdescent : baseEnd_888855 < baseStart_888855 := by decide
  rcases family_descends (prefixWord ++ tailWord_888855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888914 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 5]
def baseStart_888914 : Nat := 118140960795 + 888914 * 2 ^ 59
def prefixEnd_888914 : Nat := 4983230072969 + 3 ^ 40 * 888914 * 2
def baseEnd_888914 : Nat := 405724571120746980966191

theorem tailTrace_888914 : CollatzResearch.WordTrace tailWord_888914 prefixEnd_888914 405724571120746980966191 := by
  unfold tailWord_888914
  simp only [CollatzResearch.WordTrace]
  refine ⟨8105339275405966817436449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21614238067749244846497197 8105339275405966817436449)
  ·
    refine ⟨6079004456554475113077337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8105339275405966817436449 6079004456554475113077337)
    ·
      refine ⟨4559253342415856334808003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6079004456554475113077337 4559253342415856334808003)
      ·
        refine ⟨6838880013623784502212005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4559253342415856334808003 6838880013623784502212005)
        ·
          refine ⟨1282290002554459594164751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6838880013623784502212005 1282290002554459594164751)
          ·
            refine ⟨1923435003831689391247127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282290002554459594164751 1923435003831689391247127)
            ·
              refine ⟨2885152505747534086870691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923435003831689391247127 2885152505747534086870691)
              ·
                refine ⟨4327728758621301130306037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885152505747534086870691 4327728758621301130306037)
                ·
                  refine ⟨405724571120746980966191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4327728758621301130306037 405724571120746980966191)
                  ·
                    rfl

theorem cell20_888914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_888914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888914 prefixEnd_888914 := by exact prefixLift 888914
  have htrace : WordTrace (prefixWord ++ tailWord_888914) baseStart_888914 baseEnd_888914 := by
    simpa [prefixWord, tailWord_888914, baseEnd_888914] using wordTrace_append hprefix tailTrace_888914
  have hstable : (prefixWord ++ tailWord_888914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888914).length < 2 ^ (prefixWord ++ tailWord_888914).sum := by decide
  have hdescent : baseEnd_888914 < baseStart_888914 := by decide
  rcases family_descends (prefixWord ++ tailWord_888914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888921 : List Nat := [1, 2, 1, 2, 2, 1, 3, 6, 2]
def baseStart_888921 : Nat := 118140960795 + 888921 * 2 ^ 59
def prefixEnd_888921 : Nat := 4983230072969 + 3 ^ 40 * 888921 * 2
def baseEnd_888921 : Nat := 405727766111486067732829

theorem tailTrace_888921 : CollatzResearch.WordTrace tailWord_888921 prefixEnd_888921 405727766111486067732829 := by
  unfold tailWord_888921
  simp only [CollatzResearch.WordTrace]
  refine ⟨32421612412598507465250617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21614408275065671643500411 32421612412598507465250617)
  ·
    refine ⟨24316209309448880598937963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32421612412598507465250617 24316209309448880598937963)
    ·
      refine ⟨36474313964173320898406945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24316209309448880598937963 36474313964173320898406945)
      ·
        refine ⟨27355735473129990673805209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36474313964173320898406945 27355735473129990673805209)
        ·
          refine ⟨20516801604847493005353907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27355735473129990673805209 20516801604847493005353907)
          ·
            refine ⟨30775202407271239508030861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20516801604847493005353907 30775202407271239508030861)
            ·
              refine ⟨11540700902726714815511573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30775202407271239508030861 11540700902726714815511573)
              ·
                refine ⟨540970354815314756977105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11540700902726714815511573 540970354815314756977105)
                ·
                  refine ⟨405727766111486067732829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540970354815314756977105 405727766111486067732829)
                  ·
                    rfl

theorem cell20_888921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 2].length) (baseStart_888921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888921 prefixEnd_888921 := by exact prefixLift 888921
  have htrace : WordTrace (prefixWord ++ tailWord_888921) baseStart_888921 baseEnd_888921 := by
    simpa [prefixWord, tailWord_888921, baseEnd_888921] using wordTrace_append hprefix tailTrace_888921
  have hstable : (prefixWord ++ tailWord_888921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888921).length < 2 ^ (prefixWord ++ tailWord_888921).sum := by decide
  have hdescent : baseEnd_888921 < baseStart_888921 := by decide
  rcases family_descends (prefixWord ++ tailWord_888921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888976 : List Nat := [2, 1, 1, 1, 1, 1, 9, 2, 2]
def baseStart_888976 : Nat := 118140960795 + 888976 * 2 ^ 59
def prefixEnd_888976 : Nat := 4983230072969 + 3 ^ 40 * 888976 * 2
def baseEnd_888976 : Nat := 405752869610150320899271

theorem tailTrace_888976 : CollatzResearch.WordTrace tailWord_888976 prefixEnd_888976 405752869610150320899271 := by
  unfold tailWord_888976
  simp only [CollatzResearch.WordTrace]
  refine ⟨16211809213699625929251391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21615745618266167905668521 16211809213699625929251391)
  ·
    refine ⟨24317713820549438893877087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16211809213699625929251391 24317713820549438893877087)
    ·
      refine ⟨36476570730824158340815631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24317713820549438893877087 36476570730824158340815631)
      ·
        refine ⟨54714856096236237511223447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36476570730824158340815631 54714856096236237511223447)
        ·
          refine ⟨82072284144354356266835171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54714856096236237511223447 82072284144354356266835171)
          ·
            refine ⟨123108426216531534400252757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82072284144354356266835171 123108426216531534400252757)
            ·
              refine ⟨721338434862489459376481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 123108426216531534400252757 721338434862489459376481)
              ·
                refine ⟨541003826146867094532361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 721338434862489459376481 541003826146867094532361)
                ·
                  refine ⟨405752869610150320899271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541003826146867094532361 405752869610150320899271)
                  ·
                    rfl

theorem cell20_888976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 2].length) (baseStart_888976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888976 prefixEnd_888976 := by exact prefixLift 888976
  have htrace : WordTrace (prefixWord ++ tailWord_888976) baseStart_888976 baseEnd_888976 := by
    simpa [prefixWord, tailWord_888976, baseEnd_888976] using wordTrace_append hprefix tailTrace_888976
  have hstable : (prefixWord ++ tailWord_888976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888976).length < 2 ^ (prefixWord ++ tailWord_888976).sum := by decide
  have hdescent : baseEnd_888976 < baseStart_888976 := by decide
  rcases family_descends (prefixWord ++ tailWord_888976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888982 : List Nat := [5, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_888982 : Nat := 118140960795 + 888982 * 2 ^ 59
def prefixEnd_888982 : Nat := 4983230072969 + 3 ^ 40 * 888982 * 2
def baseEnd_888982 : Nat := 405755608173640966699247

theorem tailTrace_888982 : CollatzResearch.WordTrace tailWord_888982 prefixEnd_888982 405755608173640966699247 := by
  unfold tailWord_888982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2026489829086094680201325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21615891510251676588814133 2026489829086094680201325)
  ·
    refine ⟨759933685907285505075497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2026489829086094680201325 759933685907285505075497)
    ·
      refine ⟨569950264430464128806623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 759933685907285505075497 569950264430464128806623)
      ·
        refine ⟨854925396645696193209935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569950264430464128806623 854925396645696193209935)
        ·
          refine ⟨1282388094968544289814903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854925396645696193209935 1282388094968544289814903)
          ·
            refine ⟨1923582142452816434722355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282388094968544289814903 1923582142452816434722355)
            ·
              refine ⟨2885373213679224652083533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923582142452816434722355 2885373213679224652083533)
              ·
                refine ⟨1082014955129709244531325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2885373213679224652083533 1082014955129709244531325)
                ·
                  refine ⟨405755608173640966699247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082014955129709244531325 405755608173640966699247)
                  ·
                    rfl

theorem cell20_888982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_888982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888982 prefixEnd_888982 := by exact prefixLift 888982
  have htrace : WordTrace (prefixWord ++ tailWord_888982) baseStart_888982 baseEnd_888982 := by
    simpa [prefixWord, tailWord_888982, baseEnd_888982] using wordTrace_append hprefix tailTrace_888982
  have hstable : (prefixWord ++ tailWord_888982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888982).length < 2 ^ (prefixWord ++ tailWord_888982).sum := by decide
  have hdescent : baseEnd_888982 < baseStart_888982 := by decide
  rcases family_descends (prefixWord ++ tailWord_888982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888986 : List Nat := [3, 1, 1, 5, 2, 2, 2, 1, 3]
def baseStart_888986 : Nat := 118140960795 + 888986 * 2 ^ 59
def prefixEnd_888986 : Nat := 4983230072969 + 3 ^ 40 * 888986 * 2
def baseEnd_888986 : Nat := 405757433882634730565897

theorem tailTrace_888986 : CollatzResearch.WordTrace tailWord_888986 prefixEnd_888986 405757433882634730565897 := by
  unfold tailWord_888986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8105995789340755891591703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21615988771575349044244541 8105995789340755891591703)
  ·
    refine ⟨12158993684011133837387555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8105995789340755891591703 12158993684011133837387555)
    ·
      refine ⟨18238490526016700756081333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12158993684011133837387555 18238490526016700756081333)
      ·
        refine ⟨1709858486814065695882625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18238490526016700756081333 1709858486814065695882625)
        ·
          refine ⟨1282393865110549271911969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1709858486814065695882625 1282393865110549271911969)
          ·
            refine ⟨961795398832911953933977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1282393865110549271911969 961795398832911953933977)
            ·
              refine ⟨721346549124683965450483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 961795398832911953933977 721346549124683965450483)
              ·
                refine ⟨1082019823687025948175725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721346549124683965450483 1082019823687025948175725)
                ·
                  refine ⟨405757433882634730565897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082019823687025948175725 405757433882634730565897)
                  ·
                    rfl

theorem cell20_888986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_888986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888986 prefixEnd_888986 := by exact prefixLift 888986
  have htrace : WordTrace (prefixWord ++ tailWord_888986) baseStart_888986 baseEnd_888986 := by
    simpa [prefixWord, tailWord_888986, baseEnd_888986] using wordTrace_append hprefix tailTrace_888986
  have hstable : (prefixWord ++ tailWord_888986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888986).length < 2 ^ (prefixWord ++ tailWord_888986).sum := by decide
  have hdescent : baseEnd_888986 < baseStart_888986 := by decide
  rcases family_descends (prefixWord ++ tailWord_888986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889028 : List Nat := [2, 3, 3, 1, 2, 1, 1, 4, 3]
def baseStart_889028 : Nat := 118140960795 + 889028 * 2 ^ 59
def prefixEnd_889028 : Nat := 4983230072969 + 3 ^ 40 * 889028 * 2
def baseEnd_889028 : Nat := 405776603827069251165725

theorem tailTrace_889028 : CollatzResearch.WordTrace tailWord_889028 prefixEnd_889028 405776603827069251165725 := by
  unfold tailWord_889028
  simp only [CollatzResearch.WordTrace]
  refine ⟨16212757511605432369697869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21617010015473909826263825 16212757511605432369697869)
  ·
    refine ⟨6079784066852037138636701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16212757511605432369697869 6079784066852037138636701)
    ·
      refine ⟨2279919025069513926988763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6079784066852037138636701 2279919025069513926988763)
      ·
        refine ⟨3419878537604270890483145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2279919025069513926988763 3419878537604270890483145)
        ·
          refine ⟨2564908903203203167862359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3419878537604270890483145 2564908903203203167862359)
          ·
            refine ⟨3847363354804804751793539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2564908903203203167862359 3847363354804804751793539)
            ·
              refine ⟨5771045032207207127690309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3847363354804804751793539 5771045032207207127690309)
              ·
                refine ⟨1082070943538851336441933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5771045032207207127690309 1082070943538851336441933)
                ·
                  refine ⟨405776603827069251165725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082070943538851336441933 405776603827069251165725)
                  ·
                    rfl

theorem cell20_889028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_889028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889028 prefixEnd_889028 := by exact prefixLift 889028
  have htrace : WordTrace (prefixWord ++ tailWord_889028) baseStart_889028 baseEnd_889028 := by
    simpa [prefixWord, tailWord_889028, baseEnd_889028] using wordTrace_append hprefix tailTrace_889028
  have hstable : (prefixWord ++ tailWord_889028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889028).length < 2 ^ (prefixWord ++ tailWord_889028).sum := by decide
  have hdescent : baseEnd_889028 < baseStart_889028 := by decide
  rcases family_descends (prefixWord ++ tailWord_889028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889035 : List Nat := [1, 1, 1, 1, 3, 2, 5, 4, 2]
def baseStart_889035 : Nat := 118140960795 + 889035 * 2 ^ 59
def prefixEnd_889035 : Nat := 4983230072969 + 3 ^ 40 * 889035 * 2
def baseEnd_889035 : Nat := 405779798817808337932363

theorem tailTrace_889035 : CollatzResearch.WordTrace tailWord_889035 prefixEnd_889035 405779798817808337932363 := by
  unfold tailWord_889035
  simp only [CollatzResearch.WordTrace]
  refine ⟨32425770334185504934900559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21617180222790336623267039 32425770334185504934900559)
  ·
    refine ⟨48638655501278257402350839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32425770334185504934900559 48638655501278257402350839)
    ·
      refine ⟨72957983251917386103526259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48638655501278257402350839 72957983251917386103526259)
      ·
        refine ⟨109436974877876079155289389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72957983251917386103526259 109436974877876079155289389)
        ·
          refine ⟨41038865579203529683233521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109436974877876079155289389 41038865579203529683233521)
          ·
            refine ⟨30779149184402647262425141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41038865579203529683233521 30779149184402647262425141)
            ·
              refine ⟨2885545236037748180852357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30779149184402647262425141 2885545236037748180852357)
              ·
                refine ⟨541039731757077783909817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2885545236037748180852357 541039731757077783909817)
                ·
                  refine ⟨405779798817808337932363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541039731757077783909817 405779798817808337932363)
                  ·
                    rfl

theorem cell20_889035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 2].length) (baseStart_889035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889035 prefixEnd_889035 := by exact prefixLift 889035
  have htrace : WordTrace (prefixWord ++ tailWord_889035) baseStart_889035 baseEnd_889035 := by
    simpa [prefixWord, tailWord_889035, baseEnd_889035] using wordTrace_append hprefix tailTrace_889035
  have hstable : (prefixWord ++ tailWord_889035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889035).length < 2 ^ (prefixWord ++ tailWord_889035).sum := by decide
  have hdescent : baseEnd_889035 < baseStart_889035 := by decide
  rcases family_descends (prefixWord ++ tailWord_889035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889042 : List Nat := [3, 2, 2, 2, 1, 2, 3, 5]
def baseStart_889042 : Nat := 118140960795 + 889042 * 2 ^ 59
def prefixEnd_889042 : Nat := 4983230072969 + 3 ^ 40 * 889042 * 2
def baseEnd_889042 : Nat := 135260997936182474899667

theorem tailTrace_889042 : CollatzResearch.WordTrace tailWord_889042 prefixEnd_889042 135260997936182474899667 := by
  unfold tailWord_889042
  simp only [CollatzResearch.WordTrace]
  refine ⟨8106506411290036282601345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21617350430106763420270253 8106506411290036282601345)
  ·
    refine ⟨6079879808467527211951009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8106506411290036282601345 6079879808467527211951009)
    ·
      refine ⟨4559909856350645408963257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6079879808467527211951009 4559909856350645408963257)
      ·
        refine ⟨3419932392262984056722443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4559909856350645408963257 3419932392262984056722443)
        ·
          refine ⟨5129898588394476085083665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3419932392262984056722443 5129898588394476085083665)
          ·
            refine ⟨3847423941295857063812749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5129898588394476085083665 3847423941295857063812749)
            ·
              refine ⟨1442783977985946398929781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3847423941295857063812749 1442783977985946398929781)
              ·
                refine ⟨135260997936182474899667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1442783977985946398929781 135260997936182474899667)
                ·
                  rfl

theorem cell20_889042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_889042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889042 prefixEnd_889042 := by exact prefixLift 889042
  have htrace : WordTrace (prefixWord ++ tailWord_889042) baseStart_889042 baseEnd_889042 := by
    simpa [prefixWord, tailWord_889042, baseEnd_889042] using wordTrace_append hprefix tailTrace_889042
  have hstable : (prefixWord ++ tailWord_889042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889042).length < 2 ^ (prefixWord ++ tailWord_889042).sum := by decide
  have hdescent : baseEnd_889042 < baseStart_889042 := by decide
  rcases family_descends (prefixWord ++ tailWord_889042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889049 : List Nat := [1, 2, 1, 2, 3, 1, 4, 3, 3]
def baseStart_889049 : Nat := 118140960795 + 889049 * 2 ^ 59
def prefixEnd_889049 : Nat := 4983230072969 + 3 ^ 40 * 889049 * 2
def baseEnd_889049 : Nat := 405786188799286511465639

theorem tailTrace_889049 : CollatzResearch.WordTrace tailWord_889049 prefixEnd_889049 405786188799286511465639 := by
  unfold tailWord_889049
  simp only [CollatzResearch.WordTrace]
  refine ⟨32426280956134785325910201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21617520637423190217273467 32426280956134785325910201)
  ·
    refine ⟨24319710717101088994432651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32426280956134785325910201 24319710717101088994432651)
    ·
      refine ⟨36479566075651633491648977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24319710717101088994432651 36479566075651633491648977)
      ·
        refine ⟨27359674556738725118736733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36479566075651633491648977 27359674556738725118736733)
        ·
          refine ⟨10259877958777021919526275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27359674556738725118736733 10259877958777021919526275)
          ·
            refine ⟨15389816938165532879289413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10259877958777021919526275 15389816938165532879289413)
            ·
              refine ⟨2885590675906037414866765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15389816938165532879289413 2885590675906037414866765)
              ·
                refine ⟨1082096503464764030575037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2885590675906037414866765 1082096503464764030575037)
                ·
                  refine ⟨405786188799286511465639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082096503464764030575037 405786188799286511465639)
                  ·
                    rfl

theorem cell20_889049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_889049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889049 prefixEnd_889049 := by exact prefixLift 889049
  have htrace : WordTrace (prefixWord ++ tailWord_889049) baseStart_889049 baseEnd_889049 := by
    simpa [prefixWord, tailWord_889049, baseEnd_889049] using wordTrace_append hprefix tailTrace_889049
  have hstable : (prefixWord ++ tailWord_889049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889049).length < 2 ^ (prefixWord ++ tailWord_889049).sum := by decide
  have hdescent : baseEnd_889049 < baseStart_889049 := by decide
  rcases family_descends (prefixWord ++ tailWord_889049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889056 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 4]
def baseStart_889056 : Nat := 118140960795 + 889056 * 2 ^ 59
def prefixEnd_889056 : Nat := 4983230072969 + 3 ^ 40 * 889056 * 2
def baseEnd_889056 : Nat := 405789383790025598232277

theorem tailTrace_889056 : CollatzResearch.WordTrace tailWord_889056 prefixEnd_889056 405789383790025598232277 := by
  unfold tailWord_889056
  simp only [CollatzResearch.WordTrace]
  refine ⟨16213268133554712760707511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21617690844739617014276681 16213268133554712760707511)
  ·
    refine ⟨24319902200332069141061267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16213268133554712760707511 24319902200332069141061267)
    ·
      refine ⟨36479853300498103711591901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24319902200332069141061267 36479853300498103711591901)
      ·
        refine ⟨13679944987686788891846963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36479853300498103711591901 13679944987686788891846963)
        ·
          refine ⟨20519917481530183337770445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13679944987686788891846963 20519917481530183337770445)
          ·
            refine ⟨7694969055573818751663917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20519917481530183337770445 7694969055573818751663917)
            ·
              refine ⟨2885613395840182031873969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7694969055573818751663917 2885613395840182031873969)
              ·
                refine ⟨2164210046880136523905477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2885613395840182031873969 2164210046880136523905477)
                ·
                  refine ⟨405789383790025598232277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2164210046880136523905477 405789383790025598232277)
                  ·
                    rfl

theorem cell20_889056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_889056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889056 prefixEnd_889056 := by exact prefixLift 889056
  have htrace : WordTrace (prefixWord ++ tailWord_889056) baseStart_889056 baseEnd_889056 := by
    simpa [prefixWord, tailWord_889056, baseEnd_889056] using wordTrace_append hprefix tailTrace_889056
  have hstable : (prefixWord ++ tailWord_889056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889056).length < 2 ^ (prefixWord ++ tailWord_889056).sum := by decide
  have hdescent : baseEnd_889056 < baseStart_889056 := by decide
  rcases family_descends (prefixWord ++ tailWord_889056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889069 : List Nat := [1, 5, 1, 2, 3, 1, 2, 3, 2]
def baseStart_889069 : Nat := 118140960795 + 889069 * 2 ^ 59
def prefixEnd_889069 : Nat := 4983230072969 + 3 ^ 40 * 889069 * 2
def baseEnd_889069 : Nat := 405795317344255330798891

theorem tailTrace_889069 : CollatzResearch.WordTrace tailWord_889069 prefixEnd_889069 405795317344255330798891 := by
  unfold tailWord_889069
  simp only [CollatzResearch.WordTrace]
  refine ⟨32427010416062328741638261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21618006944041552494425507 32427010416062328741638261)
  ·
    refine ⟨3040032226505843319528587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32427010416062328741638261 3040032226505843319528587)
    ·
      refine ⟨4560048339758764979292881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3040032226505843319528587 4560048339758764979292881)
      ·
        refine ⟨3420036254819073734469661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4560048339758764979292881 3420036254819073734469661)
        ·
          refine ⟨1282513595557152650426123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3420036254819073734469661 1282513595557152650426123)
          ·
            refine ⟨1923770393335728975639185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282513595557152650426123 1923770393335728975639185)
            ·
              refine ⟨1442827795001796731729389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1923770393335728975639185 1442827795001796731729389)
              ·
                refine ⟨541060423125673774398521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1442827795001796731729389 541060423125673774398521)
                ·
                  refine ⟨405795317344255330798891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541060423125673774398521 405795317344255330798891)
                  ·
                    rfl

theorem cell20_889069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_889069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889069 prefixEnd_889069 := by exact prefixLift 889069
  have htrace : WordTrace (prefixWord ++ tailWord_889069) baseStart_889069 baseEnd_889069 := by
    simpa [prefixWord, tailWord_889069, baseEnd_889069] using wordTrace_append hprefix tailTrace_889069
  have hstable : (prefixWord ++ tailWord_889069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889069).length < 2 ^ (prefixWord ++ tailWord_889069).sum := by decide
  have hdescent : baseEnd_889069 < baseStart_889069 := by decide
  rcases family_descends (prefixWord ++ tailWord_889069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889073 : List Nat := [1, 2, 2, 2, 2, 1, 3, 5, 2]
def baseStart_889073 : Nat := 118140960795 + 889073 * 2 ^ 59
def prefixEnd_889073 : Nat := 4983230072969 + 3 ^ 40 * 889073 * 2
def baseEnd_889073 : Nat := 405797143053249094665541

theorem tailTrace_889073 : CollatzResearch.WordTrace tailWord_889073 prefixEnd_889073 405797143053249094665541 := by
  unfold tailWord_889073
  simp only [CollatzResearch.WordTrace]
  refine ⟨32427156308047837424783873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21618104205365224949855915 32427156308047837424783873)
  ·
    refine ⟨24320367231035878068587905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32427156308047837424783873 24320367231035878068587905)
    ·
      refine ⟨18240275423276908551440929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24320367231035878068587905 18240275423276908551440929)
      ·
        refine ⟨13680206567457681413580697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18240275423276908551440929 13680206567457681413580697)
        ·
          refine ⟨10260154925593261060185523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13680206567457681413580697 10260154925593261060185523)
          ·
            refine ⟨15390232388389891590278285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10260154925593261060185523 15390232388389891590278285)
            ·
              refine ⟨5771337145646209346354357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15390232388389891590278285 5771337145646209346354357)
              ·
                refine ⟨541062857404332126220721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5771337145646209346354357 541062857404332126220721)
                ·
                  refine ⟨405797143053249094665541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541062857404332126220721 405797143053249094665541)
                  ·
                    rfl

theorem cell20_889073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 2].length) (baseStart_889073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889073 prefixEnd_889073 := by exact prefixLift 889073
  have htrace : WordTrace (prefixWord ++ tailWord_889073) baseStart_889073 baseEnd_889073 := by
    simpa [prefixWord, tailWord_889073, baseEnd_889073] using wordTrace_append hprefix tailTrace_889073
  have hstable : (prefixWord ++ tailWord_889073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889073).length < 2 ^ (prefixWord ++ tailWord_889073).sum := by decide
  have hdescent : baseEnd_889073 < baseStart_889073 := by decide
  rcases family_descends (prefixWord ++ tailWord_889073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889090 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_889090 : Nat := 118140960795 + 889090 * 2 ^ 59
def prefixEnd_889090 : Nat := 4983230072969 + 3 ^ 40 * 889090 * 2
def baseEnd_889090 : Nat := 405804902316472591098805

theorem tailTrace_889090 : CollatzResearch.WordTrace tailWord_889090 prefixEnd_889090 405804902316472591098805 := by
  unfold tailWord_889090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8106944087246562332038181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21618517565990832885435149 8106944087246562332038181)
  ·
    refine ⟨1520052016358730437257159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8106944087246562332038181 1520052016358730437257159)
    ·
      refine ⟨2280078024538095655885739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1520052016358730437257159 2280078024538095655885739)
      ·
        refine ⟨3420117036807143483828609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2280078024538095655885739 3420117036807143483828609)
        ·
          refine ⟨2565087777605357612871457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3420117036807143483828609 2565087777605357612871457)
          ·
            refine ⟨1923815833204018209653593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2565087777605357612871457 1923815833204018209653593)
            ·
              refine ⟨1442861874903013657240195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1923815833204018209653593 1442861874903013657240195)
              ·
                refine ⟨2164292812354520485860293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442861874903013657240195 2164292812354520485860293)
                ·
                  refine ⟨405804902316472591098805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2164292812354520485860293 405804902316472591098805)
                  ·
                    rfl

theorem cell20_889090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_889090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889090 prefixEnd_889090 := by exact prefixLift 889090
  have htrace : WordTrace (prefixWord ++ tailWord_889090) baseStart_889090 baseEnd_889090 := by
    simpa [prefixWord, tailWord_889090, baseEnd_889090] using wordTrace_append hprefix tailTrace_889090
  have hstable : (prefixWord ++ tailWord_889090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889090).length < 2 ^ (prefixWord ++ tailWord_889090).sum := by decide
  have hdescent : baseEnd_889090 < baseStart_889090 := by decide
  rcases family_descends (prefixWord ++ tailWord_889090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889114 : List Nat := [3, 1, 1, 3, 5, 1, 2, 4]
def baseStart_889114 : Nat := 118140960795 + 889114 * 2 ^ 59
def prefixEnd_889114 : Nat := 4983230072969 + 3 ^ 40 * 889114 * 2
def baseEnd_889114 : Nat := 135271952190145058099569

theorem tailTrace_889114 : CollatzResearch.WordTrace tailWord_889114 prefixEnd_889114 135271952190145058099569 := by
  unfold tailWord_889114
  simp only [CollatzResearch.WordTrace]
  refine ⟨8107162925224825356756599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21619101133932867618017597 8107162925224825356756599)
  ·
    refine ⟨12160744387837238035134899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8107162925224825356756599 12160744387837238035134899)
    ·
      refine ⟨18241116581755857052702349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12160744387837238035134899 18241116581755857052702349)
      ·
        refine ⟨6840418718158446394763381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18241116581755857052702349 6840418718158446394763381)
        ·
          refine ⟨641289254827354349509067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6840418718158446394763381 641289254827354349509067)
          ·
            refine ⟨961933882241031524263601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641289254827354349509067 961933882241031524263601)
            ·
              refine ⟨721450411680773643197701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 961933882241031524263601 721450411680773643197701)
              ·
                refine ⟨135271952190145058099569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 721450411680773643197701 135271952190145058099569)
                ·
                  rfl

theorem cell20_889114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_889114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889114 prefixEnd_889114 := by exact prefixLift 889114
  have htrace : WordTrace (prefixWord ++ tailWord_889114) baseStart_889114 baseEnd_889114 := by
    simpa [prefixWord, tailWord_889114, baseEnd_889114] using wordTrace_append hprefix tailTrace_889114
  have hstable : (prefixWord ++ tailWord_889114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889114).length < 2 ^ (prefixWord ++ tailWord_889114).sum := by decide
  have hdescent : baseEnd_889114 < baseStart_889114 := by decide
  rcases family_descends (prefixWord ++ tailWord_889114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889145 : List Nat := [1, 2, 1, 6, 1, 2, 3, 2, 2]
def baseStart_889145 : Nat := 118140960795 + 889145 * 2 ^ 59
def prefixEnd_889145 : Nat := 4983230072969 + 3 ^ 40 * 889145 * 2
def baseEnd_889145 : Nat := 405830005815136844265247

theorem tailTrace_889145 : CollatzResearch.WordTrace tailWord_889145 prefixEnd_889145 405830005815136844265247 := by
  unfold tailWord_889145
  simp only [CollatzResearch.WordTrace]
  refine ⟨32429782363786993721404889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21619854909191329147603259 32429782363786993721404889)
  ·
    refine ⟨24322336772840245291053667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32429782363786993721404889 24322336772840245291053667)
    ·
      refine ⟨36483505159260367936580501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24322336772840245291053667 36483505159260367936580501)
      ·
        refine ⟨1710164304340329747027211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36483505159260367936580501 1710164304340329747027211)
        ·
          refine ⟨2565246456510494620540817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1710164304340329747027211 2565246456510494620540817)
          ·
            refine ⟨1923934842382870965405613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2565246456510494620540817 1923934842382870965405613)
            ·
              refine ⟨721475565893576612027105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1923934842382870965405613 721475565893576612027105)
              ·
                refine ⟨541106674420182459020329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 721475565893576612027105 541106674420182459020329)
                ·
                  refine ⟨405830005815136844265247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541106674420182459020329 405830005815136844265247)
                  ·
                    rfl

theorem cell20_889145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 2].length) (baseStart_889145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889145 prefixEnd_889145 := by exact prefixLift 889145
  have htrace : WordTrace (prefixWord ++ tailWord_889145) baseStart_889145 baseEnd_889145 := by
    simpa [prefixWord, tailWord_889145, baseEnd_889145] using wordTrace_append hprefix tailTrace_889145
  have hstable : (prefixWord ++ tailWord_889145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889145).length < 2 ^ (prefixWord ++ tailWord_889145).sum := by decide
  have hdescent : baseEnd_889145 < baseStart_889145 := by decide
  rcases family_descends (prefixWord ++ tailWord_889145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889170 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_889170 : Nat := 118140960795 + 889170 * 2 ^ 59
def prefixEnd_889170 : Nat := 4983230072969 + 3 ^ 40 * 889170 * 2
def baseEnd_889170 : Nat := 405841416496347868431811

theorem tailTrace_889170 : CollatzResearch.WordTrace tailWord_889170 prefixEnd_889170 405841416496347868431811 := by
  unfold tailWord_889170
  simp only [CollatzResearch.WordTrace]
  refine ⟨8107673547174105747766241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21620462792464281994043309 8107673547174105747766241)
  ·
    refine ⟨6080755160380579310824681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8107673547174105747766241 6080755160380579310824681)
    ·
      refine ⟨4560566370285434483118511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6080755160380579310824681 4560566370285434483118511)
      ·
        refine ⟨6840849555428151724677767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4560566370285434483118511 6840849555428151724677767)
        ·
          refine ⟨10261274333142227587016651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6840849555428151724677767 10261274333142227587016651)
          ·
            refine ⟨15391911499713341380524977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10261274333142227587016651 15391911499713341380524977)
            ·
              refine ⟨11543933624785006035393733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15391911499713341380524977 11543933624785006035393733)
              ·
                refine ⟨2164487554647188631636325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11543933624785006035393733 2164487554647188631636325)
                ·
                  refine ⟨405841416496347868431811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2164487554647188631636325 405841416496347868431811)
                  ·
                    rfl

theorem cell20_889170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_889170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889170 prefixEnd_889170 := by exact prefixLift 889170
  have htrace : WordTrace (prefixWord ++ tailWord_889170) baseStart_889170 baseEnd_889170 := by
    simpa [prefixWord, tailWord_889170, baseEnd_889170] using wordTrace_append hprefix tailTrace_889170
  have hstable : (prefixWord ++ tailWord_889170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889170).length < 2 ^ (prefixWord ++ tailWord_889170).sum := by decide
  have hdescent : baseEnd_889170 < baseStart_889170 := by decide
  rcases family_descends (prefixWord ++ tailWord_889170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889187 : List Nat := [1, 1, 1, 5, 2, 1, 2, 5, 2]
def baseStart_889187 : Nat := 118140960795 + 889187 * 2 ^ 59
def prefixEnd_889187 : Nat := 4983230072969 + 3 ^ 40 * 889187 * 2
def baseEnd_889187 : Nat := 405849175759571364865075

theorem tailTrace_889187 : CollatzResearch.WordTrace tailWord_889187 prefixEnd_889187 405849175759571364865075 := by
  unfold tailWord_889187
  simp only [CollatzResearch.WordTrace]
  refine ⟨32431314229634834894433815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21620876153089889929622543 32431314229634834894433815)
  ·
    refine ⟨48646971344452252341650723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32431314229634834894433815 48646971344452252341650723)
    ·
      refine ⟨72970457016678378512476085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48646971344452252341650723 72970457016678378512476085)
      ·
        refine ⟨6840980345313597985544633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72970457016678378512476085 6840980345313597985544633)
        ·
          refine ⟨5130735258985198489158475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6840980345313597985544633 5130735258985198489158475)
          ·
            refine ⟨7696102888477797733737713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5130735258985198489158475 7696102888477797733737713)
            ·
              refine ⟨5772077166358348300303285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7696102888477797733737713 5772077166358348300303285)
              ·
                refine ⟨541132234346095153153433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5772077166358348300303285 541132234346095153153433)
                ·
                  refine ⟨405849175759571364865075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541132234346095153153433 405849175759571364865075)
                  ·
                    rfl

theorem cell20_889187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 2].length) (baseStart_889187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889187 prefixEnd_889187 := by exact prefixLift 889187
  have htrace : WordTrace (prefixWord ++ tailWord_889187) baseStart_889187 baseEnd_889187 := by
    simpa [prefixWord, tailWord_889187, baseEnd_889187] using wordTrace_append hprefix tailTrace_889187
  have hstable : (prefixWord ++ tailWord_889187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889187).length < 2 ^ (prefixWord ++ tailWord_889187).sum := by decide
  have hdescent : baseEnd_889187 < baseStart_889187 := by decide
  rcases family_descends (prefixWord ++ tailWord_889187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889242 : List Nat := [3, 1, 1, 4, 1, 3, 2, 3, 2]
def baseStart_889242 : Nat := 118140960795 + 889242 * 2 ^ 59
def prefixEnd_889242 : Nat := 4983230072969 + 3 ^ 40 * 889242 * 2
def baseEnd_889242 : Nat := 405874279258235618031517

theorem tailTrace_889242 : CollatzResearch.WordTrace tailWord_889242 prefixEnd_889242 405874279258235618031517 := by
  unfold tailWord_889242
  simp only [CollatzResearch.WordTrace]
  refine ⟨8108330061108894821921495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21622213496290386191790653 8108330061108894821921495)
  ·
    refine ⟨12162495091663342232882243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8108330061108894821921495 12162495091663342232882243)
    ·
      refine ⟨18243742637495013349323365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12162495091663342232882243 18243742637495013349323365)
      ·
        refine ⟨3420701744530315002998131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18243742637495013349323365 3420701744530315002998131)
        ·
          refine ⟨5131052616795472504497197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3420701744530315002998131 5131052616795472504497197)
          ·
            refine ⟨1924144731298302189186449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5131052616795472504497197 1924144731298302189186449)
            ·
              refine ⟨1443108548473726641889837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1924144731298302189186449 1443108548473726641889837)
              ·
                refine ⟨541165705677647490708689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1443108548473726641889837 541165705677647490708689)
                ·
                  refine ⟨405874279258235618031517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541165705677647490708689 405874279258235618031517)
                  ·
                    rfl

theorem cell20_889242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_889242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889242 prefixEnd_889242 := by exact prefixLift 889242
  have htrace : WordTrace (prefixWord ++ tailWord_889242) baseStart_889242 baseEnd_889242 := by
    simpa [prefixWord, tailWord_889242, baseEnd_889242] using wordTrace_append hprefix tailTrace_889242
  have hstable : (prefixWord ++ tailWord_889242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889242).length < 2 ^ (prefixWord ++ tailWord_889242).sum := by decide
  have hdescent : baseEnd_889242 < baseStart_889242 := by decide
  rcases family_descends (prefixWord ++ tailWord_889242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889256 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 5]
def baseStart_889256 : Nat := 118140960795 + 889256 * 2 ^ 59
def prefixEnd_889256 : Nat := 4983230072969 + 3 ^ 40 * 889256 * 2
def baseEnd_889256 : Nat := 405880669239713791564793

theorem tailTrace_889256 : CollatzResearch.WordTrace tailWord_889256 prefixEnd_889256 405880669239713791564793 := by
  unfold tailWord_889256
  simp only [CollatzResearch.WordTrace]
  refine ⟨16216915433192429839347811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21622553910923239785797081 16216915433192429839347811)
  ·
    refine ⟨24325373149788644759021717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16216915433192429839347811 24325373149788644759021717)
    ·
      refine ⟨1140251866396342723079143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24325373149788644759021717 1140251866396342723079143)
      ·
        refine ⟨1710377799594514084618715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1140251866396342723079143 1710377799594514084618715)
        ·
          refine ⟨2565566699391771126928073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1710377799594514084618715 2565566699391771126928073)
          ·
            refine ⟨1924175024543828345196055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2565566699391771126928073 1924175024543828345196055)
            ·
              refine ⟨2886262536815742517794083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1924175024543828345196055 2886262536815742517794083)
              ·
                refine ⟨4329393805223613776691125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886262536815742517794083 4329393805223613776691125)
                ·
                  refine ⟨405880669239713791564793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4329393805223613776691125 405880669239713791564793)
                  ·
                    rfl

theorem cell20_889256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_889256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889256 prefixEnd_889256 := by exact prefixLift 889256
  have htrace : WordTrace (prefixWord ++ tailWord_889256) baseStart_889256 baseEnd_889256 := by
    simpa [prefixWord, tailWord_889256, baseEnd_889256] using wordTrace_append hprefix tailTrace_889256
  have hstable : (prefixWord ++ tailWord_889256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889256).length < 2 ^ (prefixWord ++ tailWord_889256).sum := by decide
  have hdescent : baseEnd_889256 < baseStart_889256 := by decide
  rcases family_descends (prefixWord ++ tailWord_889256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889314 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 4]
def baseStart_889314 : Nat := 118140960795 + 889314 * 2 ^ 59
def prefixEnd_889314 : Nat := 4983230072969 + 3 ^ 40 * 889314 * 2
def baseEnd_889314 : Nat := 405907142020123367631223

theorem tailTrace_889314 : CollatzResearch.WordTrace tailWord_889314 prefixEnd_889314 405907142020123367631223 := by
  unfold tailWord_889314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8108986575043683896076749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21623964200116490389537997 8108986575043683896076749)
  ·
    refine ⟨3040869965641381461028781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8108986575043683896076749 3040869965641381461028781)
    ·
      refine ⟨1140326237115518047885793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3040869965641381461028781 1140326237115518047885793)
      ·
        refine ⟨855244677836638535914345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1140326237115518047885793 855244677836638535914345)
        ·
          refine ⟨641433508377478901935759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 855244677836638535914345 641433508377478901935759)
          ·
            refine ⟨962150262566218352903639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641433508377478901935759 962150262566218352903639)
            ·
              refine ⟨1443225393849327529355459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962150262566218352903639 1443225393849327529355459)
              ·
                refine ⟨2164838090773991294033189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443225393849327529355459 2164838090773991294033189)
                ·
                  refine ⟨405907142020123367631223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2164838090773991294033189 405907142020123367631223)
                  ·
                    rfl

theorem cell20_889314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_889314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889314 prefixEnd_889314 := by exact prefixLift 889314
  have htrace : WordTrace (prefixWord ++ tailWord_889314) baseStart_889314 baseEnd_889314 := by
    simpa [prefixWord, tailWord_889314, baseEnd_889314] using wordTrace_append hprefix tailTrace_889314
  have hstable : (prefixWord ++ tailWord_889314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889314).length < 2 ^ (prefixWord ++ tailWord_889314).sum := by decide
  have hdescent : baseEnd_889314 < baseStart_889314 := by decide
  rcases family_descends (prefixWord ++ tailWord_889314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889329 : List Nat := [1, 2, 2, 2, 3, 1, 4, 5]
def baseStart_889329 : Nat := 118140960795 + 889329 * 2 ^ 59
def prefixEnd_889329 : Nat := 4983230072969 + 3 ^ 40 * 889329 * 2
def baseEnd_889329 : Nat := 135304662809616660710387

theorem tailTrace_889329 : CollatzResearch.WordTrace tailWord_889329 prefixEnd_889329 135304662809616660710387 := by
  unfold tailWord_889329
  simp only [CollatzResearch.WordTrace]
  refine ⟨32436493395120393146103041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21624328930080262097402027 32436493395120393146103041)
  ·
    refine ⟨24327370046340294859577281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32436493395120393146103041 24327370046340294859577281)
    ·
      refine ⟨18245527534755221144682961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24327370046340294859577281 18245527534755221144682961)
      ·
        refine ⟨13684145651066415858512221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18245527534755221144682961 13684145651066415858512221)
        ·
          refine ⟨5131554619149905946942083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13684145651066415858512221 5131554619149905946942083)
          ·
            refine ⟨7697331928724858920413125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5131554619149905946942083 7697331928724858920413125)
            ·
              refine ⟨1443249736635911047577461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7697331928724858920413125 1443249736635911047577461)
              ·
                refine ⟨135304662809616660710387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1443249736635911047577461 135304662809616660710387)
                ·
                  rfl

theorem cell20_889329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 5].length) (baseStart_889329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889329 prefixEnd_889329 := by exact prefixLift 889329
  have htrace : WordTrace (prefixWord ++ tailWord_889329) baseStart_889329 baseEnd_889329 := by
    simpa [prefixWord, tailWord_889329, baseEnd_889329] using wordTrace_append hprefix tailTrace_889329
  have hstable : (prefixWord ++ tailWord_889329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889329).length < 2 ^ (prefixWord ++ tailWord_889329).sum := by decide
  have hdescent : baseEnd_889329 < baseStart_889329 := by decide
  rcases family_descends (prefixWord ++ tailWord_889329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889343 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 6]
def baseStart_889343 : Nat := 118140960795 + 889343 * 2 ^ 59
def prefixEnd_889343 : Nat := 4983230072969 + 3 ^ 40 * 889343 * 2
def baseEnd_889343 : Nat := 405920378410328155664437

theorem tailTrace_889343 : CollatzResearch.WordTrace tailWord_889343 prefixEnd_889343 405920378410328155664437 := by
  unfold tailWord_889343
  simp only [CollatzResearch.WordTrace]
  refine ⟨32437004017069673537112683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21624669344713115691408455 32437004017069673537112683)
  ·
    refine ⟨48655506025604510305669025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32437004017069673537112683 48655506025604510305669025)
    ·
      refine ⟨36491629519203382729251769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48655506025604510305669025 36491629519203382729251769)
      ·
        refine ⟨27368722139402537046938827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36491629519203382729251769 27368722139402537046938827)
        ·
          refine ⟨41053083209103805570408241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27368722139402537046938827 41053083209103805570408241)
          ·
            refine ⟨30789812406827854177806181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41053083209103805570408241 30789812406827854177806181)
            ·
              refine ⟨5773089826280222658338659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30789812406827854177806181 5773089826280222658338659)
              ·
                refine ⟨8659634739420333987507989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5773089826280222658338659 8659634739420333987507989)
                ·
                  refine ⟨405920378410328155664437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8659634739420333987507989 405920378410328155664437)
                  ·
                    rfl

theorem cell20_889343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_889343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889343 prefixEnd_889343 := by exact prefixLift 889343
  have htrace : WordTrace (prefixWord ++ tailWord_889343) baseStart_889343 baseEnd_889343 := by
    simpa [prefixWord, tailWord_889343, baseEnd_889343] using wordTrace_append hprefix tailTrace_889343
  have hstable : (prefixWord ++ tailWord_889343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889343).length < 2 ^ (prefixWord ++ tailWord_889343).sum := by decide
  have hdescent : baseEnd_889343 < baseStart_889343 := by decide
  rcases family_descends (prefixWord ++ tailWord_889343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889367 : List Nat := [1, 1, 3, 6, 9]
def baseStart_889367 : Nat := 118140960795 + 889367 * 2 ^ 59
def prefixEnd_889367 : Nat := 4983230072969 + 3 ^ 40 * 889367 * 2
def baseEnd_889367 : Nat := 5011497934127046158819

theorem tailTrace_889367 : CollatzResearch.WordTrace tailWord_889367 prefixEnd_889367 5011497934127046158819 := by
  unfold tailWord_889367
  simp only [CollatzResearch.WordTrace]
  refine ⟨32437879368982725635986355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21625252912655150423990903 32437879368982725635986355)
  ·
    refine ⟨48656819053474088453979533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32437879368982725635986355 48656819053474088453979533)
    ·
      refine ⟨18246307145052783170242325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48656819053474088453979533 18246307145052783170242325)
      ·
        refine ⟨855295647424349211105109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18246307145052783170242325 855295647424349211105109)
        ·
          refine ⟨5011497934127046158819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 855295647424349211105109 5011497934127046158819)
          ·
            rfl

theorem cell20_889367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 9].length) (baseStart_889367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889367 prefixEnd_889367 := by exact prefixLift 889367
  have htrace : WordTrace (prefixWord ++ tailWord_889367) baseStart_889367 baseEnd_889367 := by
    simpa [prefixWord, tailWord_889367, baseEnd_889367] using wordTrace_append hprefix tailTrace_889367
  have hstable : (prefixWord ++ tailWord_889367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889367).length < 2 ^ (prefixWord ++ tailWord_889367).sum := by decide
  have hdescent : baseEnd_889367 < baseStart_889367 := by decide
  rcases family_descends (prefixWord ++ tailWord_889367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889373 : List Nat := [1, 4, 2, 2, 1, 4, 2, 2, 2]
def baseStart_889373 : Nat := 118140960795 + 889373 * 2 ^ 59
def prefixEnd_889373 : Nat := 4983230072969 + 3 ^ 40 * 889373 * 2
def baseEnd_889373 : Nat := 405934071227781384664315

theorem tailTrace_889373 : CollatzResearch.WordTrace tailWord_889373 prefixEnd_889373 405934071227781384664315 := by
  unfold tailWord_889373
  simp only [CollatzResearch.WordTrace]
  refine ⟨32438098206960988660704773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21625398804640659107136515 32438098206960988660704773)
  ·
    refine ⟨6082143413805185373882145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32438098206960988660704773 6082143413805185373882145)
    ·
      refine ⟨4561607560353889030411609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6082143413805185373882145 4561607560353889030411609)
      ·
        refine ⟨3421205670265416772808707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4561607560353889030411609 3421205670265416772808707)
        ·
          refine ⟨5131808505398125159213061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3421205670265416772808707 5131808505398125159213061)
          ·
            refine ⟨962214094762148467352449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5131808505398125159213061 962214094762148467352449)
            ·
              refine ⟨721660571071611350514337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 962214094762148467352449 721660571071611350514337)
              ·
                refine ⟨541245428303708512885753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 721660571071611350514337 541245428303708512885753)
                ·
                  refine ⟨405934071227781384664315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541245428303708512885753 405934071227781384664315)
                  ·
                    rfl

theorem cell20_889373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_889373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889373 prefixEnd_889373 := by exact prefixLift 889373
  have htrace : WordTrace (prefixWord ++ tailWord_889373) baseStart_889373 baseEnd_889373 := by
    simpa [prefixWord, tailWord_889373, baseEnd_889373] using wordTrace_append hprefix tailTrace_889373
  have hstable : (prefixWord ++ tailWord_889373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889373).length < 2 ^ (prefixWord ++ tailWord_889373).sum := by decide
  have hdescent : baseEnd_889373 < baseStart_889373 := by decide
  rcases family_descends (prefixWord ++ tailWord_889373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889377 : List Nat := [1, 2, 3, 2, 2, 1, 3, 4, 2]
def baseStart_889377 : Nat := 118140960795 + 889377 * 2 ^ 59
def prefixEnd_889377 : Nat := 4983230072969 + 3 ^ 40 * 889377 * 2
def baseEnd_889377 : Nat := 405935896936775148530965

theorem tailTrace_889377 : CollatzResearch.WordTrace tailWord_889377 prefixEnd_889377 405935896936775148530965 := by
  unfold tailWord_889377
  simp only [CollatzResearch.WordTrace]
  refine ⟨32438244098946497343850385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21625496065964331562566923 32438244098946497343850385)
  ·
    refine ⟨24328683074209873007887789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32438244098946497343850385 24328683074209873007887789)
    ·
      refine ⟨9123256152828702377957921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24328683074209873007887789 9123256152828702377957921)
      ·
        refine ⟨6842442114621526783468441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9123256152828702377957921 6842442114621526783468441)
        ·
          refine ⟨5131831585966145087601331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6842442114621526783468441 5131831585966145087601331)
          ·
            refine ⟨7697747378949217631401997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5131831585966145087601331 7697747378949217631401997)
            ·
              refine ⟨2886655267105956611775749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7697747378949217631401997 2886655267105956611775749)
              ·
                refine ⟨541247862582366864707953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2886655267105956611775749 541247862582366864707953)
                ·
                  refine ⟨405935896936775148530965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541247862582366864707953 405935896936775148530965)
                  ·
                    rfl

theorem cell20_889377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 2].length) (baseStart_889377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889377 prefixEnd_889377 := by exact prefixLift 889377
  have htrace : WordTrace (prefixWord ++ tailWord_889377) baseStart_889377 baseEnd_889377 := by
    simpa [prefixWord, tailWord_889377, baseEnd_889377] using wordTrace_append hprefix tailTrace_889377
  have hstable : (prefixWord ++ tailWord_889377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889377).length < 2 ^ (prefixWord ++ tailWord_889377).sum := by decide
  have hdescent : baseEnd_889377 < baseStart_889377 := by decide
  rcases family_descends (prefixWord ++ tailWord_889377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889380 : List Nat := [2, 3, 1, 5, 2, 1, 1, 5]
def baseStart_889380 : Nat := 118140960795 + 889380 * 2 ^ 59
def prefixEnd_889380 : Nat := 4983230072969 + 3 ^ 40 * 889380 * 2
def baseEnd_889380 : Nat := 135312422072840157143651

theorem tailTrace_889380 : CollatzResearch.WordTrace tailWord_889380 prefixEnd_889380 135312422072840157143651 := by
  unfold tailWord_889380
  simp only [CollatzResearch.WordTrace]
  refine ⟨16219176758967814428104797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21625569011957085904139729 16219176758967814428104797)
  ·
    refine ⟨6082191284612930410539299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16219176758967814428104797 6082191284612930410539299)
    ·
      refine ⟨9123286926919395615808949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6082191284612930410539299 9123286926919395615808949)
      ·
        refine ⟨855308149398693338982089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9123286926919395615808949 855308149398693338982089)
        ·
          refine ⟨641481112049020004236567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 855308149398693338982089 641481112049020004236567)
          ·
            refine ⟨962221668073530006354851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641481112049020004236567 962221668073530006354851)
            ·
              refine ⟨1443332502110295009532277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962221668073530006354851 1443332502110295009532277)
              ·
                refine ⟨135312422072840157143651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1443332502110295009532277 135312422072840157143651)
                ·
                  rfl

theorem cell20_889380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_889380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889380 prefixEnd_889380 := by exact prefixLift 889380
  have htrace : WordTrace (prefixWord ++ tailWord_889380) baseStart_889380 baseEnd_889380 := by
    simpa [prefixWord, tailWord_889380, baseEnd_889380] using wordTrace_append hprefix tailTrace_889380
  have hstable : (prefixWord ++ tailWord_889380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889380).length < 2 ^ (prefixWord ++ tailWord_889380).sum := by decide
  have hdescent : baseEnd_889380 < baseStart_889380 := by decide
  rcases family_descends (prefixWord ++ tailWord_889380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889384 : List Nat := [2, 1, 5, 2, 1, 1, 3, 5]
def baseStart_889384 : Nat := 118140960795 + 889384 * 2 ^ 59
def prefixEnd_889384 : Nat := 4983230072969 + 3 ^ 40 * 889384 * 2
def baseEnd_889384 : Nat := 135313030642504745099201

theorem tailTrace_889384 : CollatzResearch.WordTrace tailWord_889384 prefixEnd_889384 135313030642504745099201 := by
  unfold tailWord_889384
  simp only [CollatzResearch.WordTrace]
  refine ⟨16219249704960568769677603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21625666273280758359570137 16219249704960568769677603)
  ·
    refine ⟨24328874557440853154516405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16219249704960568769677603 24328874557440853154516405)
    ·
      refine ⟨2280831989760079983235913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24328874557440853154516405 2280831989760079983235913)
      ·
        refine ⟨1710623992320059987426935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2280831989760079983235913 1710623992320059987426935)
        ·
          refine ⟨2565935988480089981140403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1710623992320059987426935 2565935988480089981140403)
          ·
            refine ⟨3848903982720134971710605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2565935988480089981140403 3848903982720134971710605)
            ·
              refine ⟨1443338993520050614391477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3848903982720134971710605 1443338993520050614391477)
              ·
                refine ⟨135313030642504745099201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1443338993520050614391477 135313030642504745099201)
                ·
                  rfl

theorem cell20_889384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_889384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889384 prefixEnd_889384 := by exact prefixLift 889384
  have htrace : WordTrace (prefixWord ++ tailWord_889384) baseStart_889384 baseEnd_889384 := by
    simpa [prefixWord, tailWord_889384, baseEnd_889384] using wordTrace_append hprefix tailTrace_889384
  have hstable : (prefixWord ++ tailWord_889384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889384).length < 2 ^ (prefixWord ++ tailWord_889384).sum := by decide
  have hdescent : baseEnd_889384 < baseStart_889384 := by decide
  rcases family_descends (prefixWord ++ tailWord_889384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889415 : List Nat := [1, 1, 4, 1, 4, 1, 1, 5, 2]
def baseStart_889415 : Nat := 118140960795 + 889415 * 2 ^ 59
def prefixEnd_889415 : Nat := 4983230072969 + 3 ^ 40 * 889415 * 2
def baseEnd_889415 : Nat := 405953241172215905264143

theorem tailTrace_889415 : CollatzResearch.WordTrace tailWord_889415 prefixEnd_889415 405953241172215905264143 := by
  unfold tailWord_889415
  simp only [CollatzResearch.WordTrace]
  refine ⟨32439630072808829833733699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21626420048539219889155799 32439630072808829833733699)
  ·
    refine ⟨48659445109213244750600549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32439630072808829833733699 48659445109213244750600549)
    ·
      refine ⟨9123645957977483390737603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48659445109213244750600549 9123645957977483390737603)
      ·
        refine ⟨13685468936966225086106405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9123645957977483390737603 13685468936966225086106405)
        ·
          refine ⟨2566025425681167203644951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13685468936966225086106405 2566025425681167203644951)
          ·
            refine ⟨3849038138521750805467427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566025425681167203644951 3849038138521750805467427)
            ·
              refine ⟨5773557207782626208201141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3849038138521750805467427 5773557207782626208201141)
              ·
                refine ⟨541270988229621207018857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5773557207782626208201141 541270988229621207018857)
                ·
                  refine ⟨405953241172215905264143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541270988229621207018857 405953241172215905264143)
                  ·
                    rfl

theorem cell20_889415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 2].length) (baseStart_889415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889415 prefixEnd_889415 := by exact prefixLift 889415
  have htrace : WordTrace (prefixWord ++ tailWord_889415) baseStart_889415 baseEnd_889415 := by
    simpa [prefixWord, tailWord_889415, baseEnd_889415] using wordTrace_append hprefix tailTrace_889415
  have hstable : (prefixWord ++ tailWord_889415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889415).length < 2 ^ (prefixWord ++ tailWord_889415).sum := by decide
  have hdescent : baseEnd_889415 < baseStart_889415 := by decide
  rcases family_descends (prefixWord ++ tailWord_889415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889429 : List Nat := [1, 3, 2, 2, 1, 1, 5, 2, 3]
def baseStart_889429 : Nat := 118140960795 + 889429 * 2 ^ 59
def prefixEnd_889429 : Nat := 4983230072969 + 3 ^ 40 * 889429 * 2
def baseEnd_889429 : Nat := 405959631153694078797419

theorem tailTrace_889429 : CollatzResearch.WordTrace tailWord_889429 prefixEnd_889429 405959631153694078797419 := by
  unfold tailWord_889429
  simp only [CollatzResearch.WordTrace]
  refine ⟨32440140694758110224743341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21626760463172073483162227 32440140694758110224743341)
  ·
    refine ⟨12165052760534291334278753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32440140694758110224743341 12165052760534291334278753)
    ·
      refine ⟨9123789570400718500709065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12165052760534291334278753 9123789570400718500709065)
      ·
        refine ⟨6842842177800538875531799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9123789570400718500709065 6842842177800538875531799)
        ·
          refine ⟨10264263266700808313297699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6842842177800538875531799 10264263266700808313297699)
          ·
            refine ⟨15396394900051212469946549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10264263266700808313297699 15396394900051212469946549)
            ·
              refine ⟨1443412021879801169057489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15396394900051212469946549 1443412021879801169057489)
              ·
                refine ⟨1082559016409850876793117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1443412021879801169057489 1082559016409850876793117)
                ·
                  refine ⟨405959631153694078797419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082559016409850876793117 405959631153694078797419)
                  ·
                    rfl

theorem cell20_889429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_889429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889429 prefixEnd_889429 := by exact prefixLift 889429
  have htrace : WordTrace (prefixWord ++ tailWord_889429) baseStart_889429 baseEnd_889429 := by
    simpa [prefixWord, tailWord_889429, baseEnd_889429] using wordTrace_append hprefix tailTrace_889429
  have hstable : (prefixWord ++ tailWord_889429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889429).length < 2 ^ (prefixWord ++ tailWord_889429).sum := by decide
  have hdescent : baseEnd_889429 < baseStart_889429 := by decide
  rcases family_descends (prefixWord ++ tailWord_889429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889442 : List Nat := [3, 3, 2, 3, 1, 1, 3, 1, 3]
def baseStart_889442 : Nat := 118140960795 + 889442 * 2 ^ 59
def prefixEnd_889442 : Nat := 4983230072969 + 3 ^ 40 * 889442 * 2
def baseEnd_889442 : Nat := 405965564707923811364033

theorem tailTrace_889442 : CollatzResearch.WordTrace tailWord_889442 prefixEnd_889442 405965564707923811364033 := by
  unfold tailWord_889442
  simp only [CollatzResearch.WordTrace]
  refine ⟨8110153710927753361241645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21627076562474008963311053 8110153710927753361241645)
  ·
    refine ⟨3041307641597907510465617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8110153710927753361241645 3041307641597907510465617)
    ·
      refine ⟨2280980731198430632849213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3041307641597907510465617 2280980731198430632849213)
      ·
        refine ⟨855367774199411487318455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2280980731198430632849213 855367774199411487318455)
        ·
          refine ⟨1283051661299117230977683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855367774199411487318455 1283051661299117230977683)
          ·
            refine ⟨1924577491948675846466525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283051661299117230977683 1924577491948675846466525)
            ·
              refine ⟨721716559480753442424947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1924577491948675846466525 721716559480753442424947)
              ·
                refine ⟨1082574839221130163637421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721716559480753442424947 1082574839221130163637421)
                ·
                  refine ⟨405965564707923811364033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082574839221130163637421 405965564707923811364033)
                  ·
                    rfl

theorem cell20_889442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_889442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889442 prefixEnd_889442 := by exact prefixLift 889442
  have htrace : WordTrace (prefixWord ++ tailWord_889442) baseStart_889442 baseEnd_889442 := by
    simpa [prefixWord, tailWord_889442, baseEnd_889442] using wordTrace_append hprefix tailTrace_889442
  have hstable : (prefixWord ++ tailWord_889442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889442).length < 2 ^ (prefixWord ++ tailWord_889442).sum := by decide
  have hdescent : baseEnd_889442 < baseStart_889442 := by decide
  rcases family_descends (prefixWord ++ tailWord_889442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889464 : List Nat := [2, 1, 2, 1, 1, 1, 2, 10]
def baseStart_889464 : Nat := 118140960795 + 889464 * 2 ^ 59
def prefixEnd_889464 : Nat := 4983230072969 + 3 ^ 40 * 889464 * 2
def baseEnd_889464 : Nat := 135325202035796504210203

theorem tailTrace_889464 : CollatzResearch.WordTrace tailWord_889464 prefixEnd_889464 135325202035796504210203 := by
  unfold tailWord_889464
  simp only [CollatzResearch.WordTrace]
  refine ⟨16220708624815655601133723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21627611499754207468178297 16220708624815655601133723)
  ·
    refine ⟨24331062937223483401700585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16220708624815655601133723 24331062937223483401700585)
    ·
      refine ⟨18248297202917612551275439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24331062937223483401700585 18248297202917612551275439)
      ·
        refine ⟨27372445804376418826913159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18248297202917612551275439 27372445804376418826913159)
        ·
          refine ⟨41058668706564628240369739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27372445804376418826913159 41058668706564628240369739)
          ·
            refine ⟨61588003059846942360554609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41058668706564628240369739 61588003059846942360554609)
            ·
              refine ⟨46191002294885206770415957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61588003059846942360554609 46191002294885206770415957)
              ·
                refine ⟨135325202035796504210203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46191002294885206770415957 135325202035796504210203)
                ·
                  rfl

theorem cell20_889464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_889464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889464 prefixEnd_889464 := by exact prefixLift 889464
  have htrace : WordTrace (prefixWord ++ tailWord_889464) baseStart_889464 baseEnd_889464 := by
    simpa [prefixWord, tailWord_889464, baseEnd_889464] using wordTrace_append hprefix tailTrace_889464
  have hstable : (prefixWord ++ tailWord_889464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889464).length < 2 ^ (prefixWord ++ tailWord_889464).sum := by decide
  have hdescent : baseEnd_889464 < baseStart_889464 := by decide
  rcases family_descends (prefixWord ++ tailWord_889464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889542 : List Nat := [6, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_889542 : Nat := 118140960795 + 889542 * 2 ^ 59
def prefixEnd_889542 : Nat := 4983230072969 + 3 ^ 40 * 889542 * 2
def baseEnd_889542 : Nat := 406011207432767908030291

theorem tailTrace_889542 : CollatzResearch.WordTrace tailWord_889542 prefixEnd_889542 406011207432767908030291 := by
  unfold tailWord_889542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1013883191979647828862715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21629508095565820349071253 1013883191979647828862715)
  ·
    refine ⟨1520824787969471743294073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1013883191979647828862715 1520824787969471743294073)
    ·
      refine ⟨1140618590977103807470555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1520824787969471743294073 1140618590977103807470555)
      ·
        refine ⟨1710927886465655711205833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1140618590977103807470555 1710927886465655711205833)
        ·
          refine ⟨1283195914849241783404375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1710927886465655711205833 1283195914849241783404375)
          ·
            refine ⟨1924793872273862675106563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283195914849241783404375 1924793872273862675106563)
            ·
              refine ⟨2887190808410794012659845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1924793872273862675106563 2887190808410794012659845)
              ·
                refine ⟨541348276577023877373721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2887190808410794012659845 541348276577023877373721)
                ·
                  refine ⟨406011207432767908030291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541348276577023877373721 406011207432767908030291)
                  ·
                    rfl

theorem cell20_889542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_889542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889542 prefixEnd_889542 := by exact prefixLift 889542
  have htrace : WordTrace (prefixWord ++ tailWord_889542) baseStart_889542 baseEnd_889542 := by
    simpa [prefixWord, tailWord_889542, baseEnd_889542] using wordTrace_append hprefix tailTrace_889542
  have hstable : (prefixWord ++ tailWord_889542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889542).length < 2 ^ (prefixWord ++ tailWord_889542).sum := by decide
  have hdescent : baseEnd_889542 < baseStart_889542 := by decide
  rcases family_descends (prefixWord ++ tailWord_889542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889546 : List Nat := [3, 1, 2, 1, 4, 1, 4, 2, 2]
def baseStart_889546 : Nat := 118140960795 + 889546 * 2 ^ 59
def prefixEnd_889546 : Nat := 4983230072969 + 3 ^ 40 * 889546 * 2
def baseEnd_889546 : Nat := 406013033141761671896941

theorem tailTrace_889546 : CollatzResearch.WordTrace tailWord_889546 prefixEnd_889546 406013033141761671896941 := by
  unfold tailWord_889546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8111102008833559801688123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21629605356889492804501661 8111102008833559801688123)
  ·
    refine ⟨12166653013250339702532185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8111102008833559801688123 12166653013250339702532185)
    ·
      refine ⟨9124989759937754776899139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12166653013250339702532185 9124989759937754776899139)
      ·
        refine ⟨13687484639906632165348709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9124989759937754776899139 13687484639906632165348709)
        ·
          refine ⟨2566403369982493531002883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13687484639906632165348709 2566403369982493531002883)
          ·
            refine ⟨3849605054973740296504325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566403369982493531002883 3849605054973740296504325)
            ·
              refine ⟨721800947807576305594561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3849605054973740296504325 721800947807576305594561)
              ·
                refine ⟨541350710855682229195921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 721800947807576305594561 541350710855682229195921)
                ·
                  refine ⟨406013033141761671896941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541350710855682229195921 406013033141761671896941)
                  ·
                    rfl

theorem cell20_889546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_889546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889546 prefixEnd_889546 := by exact prefixLift 889546
  have htrace : WordTrace (prefixWord ++ tailWord_889546) baseStart_889546 baseEnd_889546 := by
    simpa [prefixWord, tailWord_889546, baseEnd_889546] using wordTrace_append hprefix tailTrace_889546
  have hstable : (prefixWord ++ tailWord_889546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889546).length < 2 ^ (prefixWord ++ tailWord_889546).sum := by decide
  have hdescent : baseEnd_889546 < baseStart_889546 := by decide
  rcases family_descends (prefixWord ++ tailWord_889546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889598 : List Nat := [4, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_889598 : Nat := 118140960795 + 889598 * 2 ^ 59
def prefixEnd_889598 : Nat := 4983230072969 + 3 ^ 40 * 889598 * 2
def baseEnd_889598 : Nat := 406036767358680602163395

theorem tailTrace_889598 : CollatzResearch.WordTrace tailWord_889598 prefixEnd_889598 406036767358680602163395 := by
  unfold tailWord_889598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4055788078893231510955681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21630869754097234725096965 4055788078893231510955681)
  ·
    refine ⟨3041841059169923633216761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4055788078893231510955681 3041841059169923633216761)
    ·
      refine ⟨2281380794377442724912571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3041841059169923633216761 2281380794377442724912571)
      ·
        refine ⟨3422071191566164087368857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2281380794377442724912571 3422071191566164087368857)
        ·
          refine ⟨2566553393674623065526643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3422071191566164087368857 2566553393674623065526643)
          ·
            refine ⟨3849830090511934598289965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566553393674623065526643 3849830090511934598289965)
            ·
              refine ⟨1443686283941975474358737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3849830090511934598289965 1443686283941975474358737)
              ·
                refine ⟨1082764712956481605769053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1443686283941975474358737 1082764712956481605769053)
                ·
                  refine ⟨406036767358680602163395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082764712956481605769053 406036767358680602163395)
                  ·
                    rfl

theorem cell20_889598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_889598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889598 prefixEnd_889598 := by exact prefixLift 889598
  have htrace : WordTrace (prefixWord ++ tailWord_889598) baseStart_889598 baseEnd_889598 := by
    simpa [prefixWord, tailWord_889598, baseEnd_889598] using wordTrace_append hprefix tailTrace_889598
  have hstable : (prefixWord ++ tailWord_889598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889598).length < 2 ^ (prefixWord ++ tailWord_889598).sum := by decide
  have hdescent : baseEnd_889598 < baseStart_889598 := by decide
  rcases family_descends (prefixWord ++ tailWord_889598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889609 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 4]
def baseStart_889609 : Nat := 118140960795 + 889609 * 2 ^ 59
def prefixEnd_889609 : Nat := 4983230072969 + 3 ^ 40 * 889609 * 2
def baseEnd_889609 : Nat := 406041788058413452796683

theorem tailTrace_889609 : CollatzResearch.WordTrace tailWord_889609 prefixEnd_889609 406041788058413452796683 := by
  unfold tailWord_889609
  simp only [CollatzResearch.WordTrace]
  refine ⟨32446705834106000966295881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21631137222737333977530587 32446705834106000966295881)
  ·
    refine ⟨24335029375579500724721911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32446705834106000966295881 24335029375579500724721911)
    ·
      refine ⟨36502544063369251087082867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24335029375579500724721911 36502544063369251087082867)
      ·
        refine ⟨54753816095053876630624301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36502544063369251087082867 54753816095053876630624301)
        ·
          refine ⟨20532681035645203736484113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54753816095053876630624301 20532681035645203736484113)
          ·
            refine ⟨15399510776733902802363085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20532681035645203736484113 15399510776733902802363085)
            ·
              refine ⟨5774816541275213550886157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15399510776733902802363085 5774816541275213550886157)
              ·
                refine ⟨2165556202978205081582309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5774816541275213550886157 2165556202978205081582309)
                ·
                  refine ⟨406041788058413452796683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2165556202978205081582309 406041788058413452796683)
                  ·
                    rfl

theorem cell20_889609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_889609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889609 prefixEnd_889609 := by exact prefixLift 889609
  have htrace : WordTrace (prefixWord ++ tailWord_889609) baseStart_889609 baseEnd_889609 := by
    simpa [prefixWord, tailWord_889609, baseEnd_889609] using wordTrace_append hprefix tailTrace_889609
  have hstable : (prefixWord ++ tailWord_889609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889609).length < 2 ^ (prefixWord ++ tailWord_889609).sum := by decide
  have hdescent : baseEnd_889609 < baseStart_889609 := by decide
  rcases family_descends (prefixWord ++ tailWord_889609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889619 : List Nat := [1, 1, 1, 2, 1, 3, 7, 1, 3]
def baseStart_889619 : Nat := 118140960795 + 889619 * 2 ^ 59
def prefixEnd_889619 : Nat := 4983230072969 + 3 ^ 40 * 889619 * 2
def baseEnd_889619 : Nat := 406046352330897862463309

theorem tailTrace_889619 : CollatzResearch.WordTrace tailWord_889619 prefixEnd_889619 406046352330897862463309 := by
  unfold tailWord_889619
  simp only [CollatzResearch.WordTrace]
  refine ⟨32447070564069772674159911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21631380376046515116106607 32447070564069772674159911)
  ·
    refine ⟨48670605846104659011239867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32447070564069772674159911 48670605846104659011239867)
    ·
      refine ⟨73005908769156988516859801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48670605846104659011239867 73005908769156988516859801)
      ·
        refine ⟨54754431576867741387644851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73005908769156988516859801 54754431576867741387644851)
        ·
          refine ⟨82131647365301612081467277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54754431576867741387644851 82131647365301612081467277)
          ·
            refine ⟨30799367761988104530550229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82131647365301612081467277 30799367761988104530550229)
            ·
              refine ⟨721860181921596199934771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30799367761988104530550229 721860181921596199934771)
              ·
                refine ⟨1082790272882394299902157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721860181921596199934771 1082790272882394299902157)
                ·
                  refine ⟨406046352330897862463309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082790272882394299902157 406046352330897862463309)
                  ·
                    rfl

theorem cell20_889619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 3].length) (baseStart_889619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889619 prefixEnd_889619 := by exact prefixLift 889619
  have htrace : WordTrace (prefixWord ++ tailWord_889619) baseStart_889619 baseEnd_889619 := by
    simpa [prefixWord, tailWord_889619, baseEnd_889619] using wordTrace_append hprefix tailTrace_889619
  have hstable : (prefixWord ++ tailWord_889619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889619).length < 2 ^ (prefixWord ++ tailWord_889619).sum := by decide
  have hdescent : baseEnd_889619 < baseStart_889619 := by decide
  rcases family_descends (prefixWord ++ tailWord_889619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889640 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 7]
def baseStart_889640 : Nat := 118140960795 + 889640 * 2 ^ 59
def prefixEnd_889640 : Nat := 4983230072969 + 3 ^ 40 * 889640 * 2
def baseEnd_889640 : Nat := 406055937303115122763223

theorem tailTrace_889640 : CollatzResearch.WordTrace tailWord_889640 prefixEnd_889640 406055937303115122763223 := by
  unfold tailWord_889640
  simp only [CollatzResearch.WordTrace]
  refine ⟨16223918248496846630337187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21631890997995795507116249 16223918248496846630337187)
  ·
    refine ⟨24335877372745269945505781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16223918248496846630337187 24335877372745269945505781)
    ·
      refine ⟨2281488503694869057391167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24335877372745269945505781 2281488503694869057391167)
      ·
        refine ⟨3422232755542303586086751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2281488503694869057391167 3422232755542303586086751)
        ·
          refine ⟨5133349133313455379130127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3422232755542303586086751 5133349133313455379130127)
          ·
            refine ⟨7700023699970183068695191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5133349133313455379130127 7700023699970183068695191)
            ·
              refine ⟨11550035549955274603042787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7700023699970183068695191 11550035549955274603042787)
              ·
                refine ⟨17325053324932911904564181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11550035549955274603042787 17325053324932911904564181)
                ·
                  refine ⟨406055937303115122763223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17325053324932911904564181 406055937303115122763223)
                  ·
                    rfl

theorem cell20_889640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_889640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889640 prefixEnd_889640 := by exact prefixLift 889640
  have htrace : WordTrace (prefixWord ++ tailWord_889640) baseStart_889640 baseEnd_889640 := by
    simpa [prefixWord, tailWord_889640, baseEnd_889640] using wordTrace_append hprefix tailTrace_889640
  have hstable : (prefixWord ++ tailWord_889640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889640).length < 2 ^ (prefixWord ++ tailWord_889640).sum := by decide
  have hdescent : baseEnd_889640 < baseStart_889640 := by decide
  rcases family_descends (prefixWord ++ tailWord_889640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889664 : List Nat := [2, 1, 1, 2, 2, 1, 1, 8, 2]
def baseStart_889664 : Nat := 118140960795 + 889664 * 2 ^ 59
def prefixEnd_889664 : Nat := 4983230072969 + 3 ^ 40 * 889664 * 2
def baseEnd_889664 : Nat := 406066891557077705963125

theorem tailTrace_889664 : CollatzResearch.WordTrace tailWord_889664 prefixEnd_889664 406066891557077705963125 := by
  unfold tailWord_889664
  simp only [CollatzResearch.WordTrace]
  refine ⟨16224355924453372679774023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21632474565937830239698697 16224355924453372679774023)
  ·
    refine ⟨24336533886680059019661035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16224355924453372679774023 24336533886680059019661035)
    ·
      refine ⟨36504800830020088529491553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24336533886680059019661035 36504800830020088529491553)
      ·
        refine ⟨27378600622515066397118665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36504800830020088529491553 27378600622515066397118665)
        ·
          refine ⟨20533950466886299797838999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27378600622515066397118665 20533950466886299797838999)
          ·
            refine ⟨30800925700329449696758499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20533950466886299797838999 30800925700329449696758499)
            ·
              refine ⟨46201388550494174545137749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30800925700329449696758499 46201388550494174545137749)
              ·
                refine ⟨541422522076103607950833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 46201388550494174545137749 541422522076103607950833)
                ·
                  refine ⟨406066891557077705963125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541422522076103607950833 406066891557077705963125)
                  ·
                    rfl

theorem cell20_889664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 2].length) (baseStart_889664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889664 prefixEnd_889664 := by exact prefixLift 889664
  have htrace : WordTrace (prefixWord ++ tailWord_889664) baseStart_889664 baseEnd_889664 := by
    simpa [prefixWord, tailWord_889664, baseEnd_889664] using wordTrace_append hprefix tailTrace_889664
  have hstable : (prefixWord ++ tailWord_889664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889664).length < 2 ^ (prefixWord ++ tailWord_889664).sum := by decide
  have hdescent : baseEnd_889664 < baseStart_889664 := by decide
  rcases family_descends (prefixWord ++ tailWord_889664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889685 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 6]
def baseStart_889685 : Nat := 118140960795 + 889685 * 2 ^ 59
def prefixEnd_889685 : Nat := 4983230072969 + 3 ^ 40 * 889685 * 2
def baseEnd_889685 : Nat := 406076476529294966263039

theorem tailTrace_889685 : CollatzResearch.WordTrace tailWord_889685 prefixEnd_889685 406076476529294966263039 := by
  unfold tailWord_889685
  simp only [CollatzResearch.WordTrace]
  refine ⟨32449477781830665946062509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21632985187887110630708339 32449477781830665946062509)
  ·
    refine ⟨12168554168186499729773441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32449477781830665946062509 12168554168186499729773441)
    ·
      refine ⟨9126415626139874797330081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12168554168186499729773441 9126415626139874797330081)
      ·
        refine ⟨6844811719604906097997561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9126415626139874797330081 6844811719604906097997561)
        ·
          refine ⟨5133608789703679573498171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6844811719604906097997561 5133608789703679573498171)
          ·
            refine ⟨7700413184555519360247257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5133608789703679573498171 7700413184555519360247257)
            ·
              refine ⟨5775309888416639520185443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7700413184555519360247257 5775309888416639520185443)
              ·
                refine ⟨8662964832624959280278165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5775309888416639520185443 8662964832624959280278165)
                ·
                  refine ⟨406076476529294966263039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8662964832624959280278165 406076476529294966263039)
                  ·
                    rfl

theorem cell20_889685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_889685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889685 prefixEnd_889685 := by exact prefixLift 889685
  have htrace : WordTrace (prefixWord ++ tailWord_889685) baseStart_889685 baseEnd_889685 := by
    simpa [prefixWord, tailWord_889685, baseEnd_889685] using wordTrace_append hprefix tailTrace_889685
  have hstable : (prefixWord ++ tailWord_889685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889685).length < 2 ^ (prefixWord ++ tailWord_889685).sum := by decide
  have hdescent : baseEnd_889685 < baseStart_889685 := by decide
  rcases family_descends (prefixWord ++ tailWord_889685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889757 : List Nat := [1, 4, 2, 1, 2, 1, 4, 3, 2]
def baseStart_889757 : Nat := 118140960795 + 889757 * 2 ^ 59
def prefixEnd_889757 : Nat := 4983230072969 + 3 ^ 40 * 889757 * 2
def baseEnd_889757 : Nat := 406109339291182715862745

theorem tailTrace_889757 : CollatzResearch.WordTrace tailWord_889757 prefixEnd_889757 406109339291182715862745 := by
  unfold tailWord_889757
  simp only [CollatzResearch.WordTrace]
  refine ⟨32452103837569822242683525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21634735891713214828455683 32452103837569822242683525)
  ·
    refine ⟨6084769469544341670503161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32452103837569822242683525 6084769469544341670503161)
    ·
      refine ⟨4563577102158256252877371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6084769469544341670503161 4563577102158256252877371)
      ·
        refine ⟨6845365653237384379316057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4563577102158256252877371 6845365653237384379316057)
        ·
          refine ⟨5134024239928038284487043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6845365653237384379316057 5134024239928038284487043)
          ·
            refine ⟨7701036359892057426730565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5134024239928038284487043 7701036359892057426730565)
            ·
              refine ⟨1443944317479760767511981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7701036359892057426730565 1443944317479760767511981)
              ·
                refine ⟨541479119054910287816993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1443944317479760767511981 541479119054910287816993)
                ·
                  refine ⟨406109339291182715862745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541479119054910287816993 406109339291182715862745)
                  ·
                    rfl

theorem cell20_889757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_889757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889757 prefixEnd_889757 := by exact prefixLift 889757
  have htrace : WordTrace (prefixWord ++ tailWord_889757) baseStart_889757 baseEnd_889757 := by
    simpa [prefixWord, tailWord_889757, baseEnd_889757] using wordTrace_append hprefix tailTrace_889757
  have hstable : (prefixWord ++ tailWord_889757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889757).length < 2 ^ (prefixWord ++ tailWord_889757).sum := by decide
  have hdescent : baseEnd_889757 < baseStart_889757 := by decide
  rcases family_descends (prefixWord ++ tailWord_889757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889767 : List Nat := [1, 1, 6, 1, 4, 1, 1, 2, 3]
def baseStart_889767 : Nat := 118140960795 + 889767 * 2 ^ 59
def prefixEnd_889767 : Nat := 4983230072969 + 3 ^ 40 * 889767 * 2
def baseEnd_889767 : Nat := 406113903563667125529371

theorem tailTrace_889767 : CollatzResearch.WordTrace tailWord_889767 prefixEnd_889767 406113903563667125529371 := by
  unfold tailWord_889767
  simp only [CollatzResearch.WordTrace]
  refine ⟨32452468567533593950547555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21634979045022395967031703 32452468567533593950547555)
  ·
    refine ⟨48678702851300390925821333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32452468567533593950547555 48678702851300390925821333)
    ·
      refine ⟨2281814196154705824647875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48678702851300390925821333 2281814196154705824647875)
      ·
        refine ⟨3422721294232058736971813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2281814196154705824647875 3422721294232058736971813)
        ·
          refine ⟨641760242668511013182215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3422721294232058736971813 641760242668511013182215)
          ·
            refine ⟨962640364002766519773323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641760242668511013182215 962640364002766519773323)
            ·
              refine ⟨1443960546004149779659985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962640364002766519773323 1443960546004149779659985)
              ·
                refine ⟨1082970409503112334744989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1443960546004149779659985 1082970409503112334744989)
                ·
                  refine ⟨406113903563667125529371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082970409503112334744989 406113903563667125529371)
                  ·
                    rfl

theorem cell20_889767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 3].length) (baseStart_889767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889767 prefixEnd_889767 := by exact prefixLift 889767
  have htrace : WordTrace (prefixWord ++ tailWord_889767) baseStart_889767 baseEnd_889767 := by
    simpa [prefixWord, tailWord_889767, baseEnd_889767] using wordTrace_append hprefix tailTrace_889767
  have hstable : (prefixWord ++ tailWord_889767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889767).length < 2 ^ (prefixWord ++ tailWord_889767).sum := by decide
  have hdescent : baseEnd_889767 < baseStart_889767 := by decide
  rcases family_descends (prefixWord ++ tailWord_889767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889799 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 4]
def baseStart_889799 : Nat := 118140960795 + 889799 * 2 ^ 59
def prefixEnd_889799 : Nat := 4983230072969 + 3 ^ 40 * 889799 * 2
def baseEnd_889799 : Nat := 406128509235617236462573

theorem tailTrace_889799 : CollatzResearch.WordTrace tailWord_889799 prefixEnd_889799 406128509235617236462573 := by
  unfold tailWord_889799
  simp only [CollatzResearch.WordTrace]
  refine ⟨32453635703417663415712451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21635757135611775610474967 32453635703417663415712451)
  ·
    refine ⟨48680453555126495123568677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32453635703417663415712451 48680453555126495123568677)
    ·
      refine ⟨9127585041586217835669127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48680453555126495123568677 9127585041586217835669127)
      ·
        refine ⟨13691377562379326753503691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9127585041586217835669127 13691377562379326753503691)
        ·
          refine ⟨20537066343568990130255537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13691377562379326753503691 20537066343568990130255537)
          ·
            refine ⟨15402799757676742597691653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20537066343568990130255537 15402799757676742597691653)
            ·
              refine ⟨2888024954564389237067185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15402799757676742597691653 2888024954564389237067185)
              ·
                refine ⟨2166018715923291927800389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2888024954564389237067185 2166018715923291927800389)
                ·
                  refine ⟨406128509235617236462573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2166018715923291927800389 406128509235617236462573)
                  ·
                    rfl

theorem cell20_889799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_889799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889799 prefixEnd_889799 := by exact prefixLift 889799
  have htrace : WordTrace (prefixWord ++ tailWord_889799) baseStart_889799 baseEnd_889799 := by
    simpa [prefixWord, tailWord_889799, baseEnd_889799] using wordTrace_append hprefix tailTrace_889799
  have hstable : (prefixWord ++ tailWord_889799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889799).length < 2 ^ (prefixWord ++ tailWord_889799).sum := by decide
  have hdescent : baseEnd_889799 < baseStart_889799 := by decide
  rcases family_descends (prefixWord ++ tailWord_889799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889812 : List Nat := [2, 4, 1, 2, 1, 4, 1, 3, 2]
def baseStart_889812 : Nat := 118140960795 + 889812 * 2 ^ 59
def prefixEnd_889812 : Nat := 4983230072969 + 3 ^ 40 * 889812 * 2
def baseEnd_889812 : Nat := 406134442789846969029187

theorem tailTrace_889812 : CollatzResearch.WordTrace tailWord_889812 prefixEnd_889812 406134442789846969029187 := by
  unfold tailWord_889812
  simp only [CollatzResearch.WordTrace]
  refine ⟨16227054926185283317967845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21636073234913711090623793 16227054926185283317967845)
  ·
    refine ⟨3042572798659740622118971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16227054926185283317967845 3042572798659740622118971)
    ·
      refine ⟨4563859197989610933178457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3042572798659740622118971 4563859197989610933178457)
      ·
        refine ⟨3422894398492208199883843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4563859197989610933178457 3422894398492208199883843)
        ·
          refine ⟨5134341597738312299825765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3422894398492208199883843 5134341597738312299825765)
          ·
            refine ⟨962689049575933556217331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5134341597738312299825765 962689049575933556217331)
            ·
              refine ⟨1444033574363900334325997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962689049575933556217331 1444033574363900334325997)
              ·
                refine ⟨541512590386462625372249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1444033574363900334325997 541512590386462625372249)
                ·
                  refine ⟨406134442789846969029187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541512590386462625372249 406134442789846969029187)
                  ·
                    rfl

theorem cell20_889812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_889812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889812 prefixEnd_889812 := by exact prefixLift 889812
  have htrace : WordTrace (prefixWord ++ tailWord_889812) baseStart_889812 baseEnd_889812 := by
    simpa [prefixWord, tailWord_889812, baseEnd_889812] using wordTrace_append hprefix tailTrace_889812
  have hstable : (prefixWord ++ tailWord_889812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889812).length < 2 ^ (prefixWord ++ tailWord_889812).sum := by decide
  have hdescent : baseEnd_889812 < baseStart_889812 := by decide
  rcases family_descends (prefixWord ++ tailWord_889812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889823 : List Nat := [1, 1, 2, 3, 5, 2, 6]
def baseStart_889823 : Nat := 118140960795 + 889823 * 2 ^ 59
def prefixEnd_889823 : Nat := 4983230072969 + 3 ^ 40 * 889823 * 2
def baseEnd_889823 : Nat := 45126607054397757740275

theorem tailTrace_889823 : CollatzResearch.WordTrace tailWord_889823 prefixEnd_889823 45126607054397757740275 := by
  unfold tailWord_889823
  simp only [CollatzResearch.WordTrace]
  refine ⟨32454511055330715514586123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21636340703553810343057415 32454511055330715514586123)
  ·
    refine ⟨48681766582996073271879185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32454511055330715514586123 48681766582996073271879185)
    ·
      refine ⟨36511324937247054953909389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48681766582996073271879185 36511324937247054953909389)
      ·
        refine ⟨13691746851467645607716021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36511324937247054953909389 13691746851467645607716021)
        ·
          refine ⟨1283601267325091775723377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13691746851467645607716021 1283601267325091775723377)
          ·
            refine ⟨962700950493818831792533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1283601267325091775723377 962700950493818831792533)
            ·
              refine ⟨45126607054397757740275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 962700950493818831792533 45126607054397757740275)
              ·
                rfl

theorem cell20_889823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 6].length) (baseStart_889823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889823 prefixEnd_889823 := by exact prefixLift 889823
  have htrace : WordTrace (prefixWord ++ tailWord_889823) baseStart_889823 baseEnd_889823 := by
    simpa [prefixWord, tailWord_889823, baseEnd_889823] using wordTrace_append hprefix tailTrace_889823
  have hstable : (prefixWord ++ tailWord_889823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889823).length < 2 ^ (prefixWord ++ tailWord_889823).sum := by decide
  have hdescent : baseEnd_889823 < baseStart_889823 := by decide
  rcases family_descends (prefixWord ++ tailWord_889823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889829 : List Nat := [1, 3, 1, 6, 1, 1, 3, 2, 2]
def baseStart_889829 : Nat := 118140960795 + 889829 * 2 ^ 59
def prefixEnd_889829 : Nat := 4983230072969 + 3 ^ 40 * 889829 * 2
def baseEnd_889829 : Nat := 406142202053070465462451

theorem tailTrace_889829 : CollatzResearch.WordTrace tailWord_889829 prefixEnd_889829 406142202053070465462451 := by
  unfold tailWord_889829
  simp only [CollatzResearch.WordTrace]
  refine ⟨32454729893308978539304541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21636486595539319026203027 32454729893308978539304541)
  ·
    refine ⟨12170523709990866952239203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32454729893308978539304541 12170523709990866952239203)
    ·
      refine ⟨18255785564986300428358805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12170523709990866952239203 18255785564986300428358805)
      ·
        refine ⟨855739948358732832579319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18255785564986300428358805 855739948358732832579319)
        ·
          refine ⟨1283609922538099248868979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855739948358732832579319 1283609922538099248868979)
          ·
            refine ⟨1925414883807148873303469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283609922538099248868979 1925414883807148873303469)
            ·
              refine ⟨722030581427680827488801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1925414883807148873303469 722030581427680827488801)
              ·
                refine ⟨541522936070760620616601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 722030581427680827488801 541522936070760620616601)
                ·
                  refine ⟨406142202053070465462451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541522936070760620616601 406142202053070465462451)
                  ·
                    rfl

theorem cell20_889829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_889829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889829 prefixEnd_889829 := by exact prefixLift 889829
  have htrace : WordTrace (prefixWord ++ tailWord_889829) baseStart_889829 baseEnd_889829 := by
    simpa [prefixWord, tailWord_889829, baseEnd_889829] using wordTrace_append hprefix tailTrace_889829
  have hstable : (prefixWord ++ tailWord_889829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889829).length < 2 ^ (prefixWord ++ tailWord_889829).sum := by decide
  have hdescent : baseEnd_889829 < baseStart_889829 := by decide
  rcases family_descends (prefixWord ++ tailWord_889829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889888 : List Nat := [2, 1, 1, 7, 1, 1, 1, 4, 2]
def baseStart_889888 : Nat := 118140960795 + 889888 * 2 ^ 59
def prefixEnd_889888 : Nat := 4983230072969 + 3 ^ 40 * 889888 * 2
def baseEnd_889888 : Nat := 406169131260728482495543

theorem tailTrace_889888 : CollatzResearch.WordTrace tailWord_889888 prefixEnd_889888 406169131260728482495543 := by
  unfold tailWord_889888
  simp only [CollatzResearch.WordTrace]
  refine ⟨16228440900047615807851159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21637921200063487743801545 16228440900047615807851159)
  ·
    refine ⟨24342661350071423711776739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16228440900047615807851159 24342661350071423711776739)
    ·
      refine ⟨36513992025107135567665109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24342661350071423711776739 36513992025107135567665109)
      ·
        refine ⟨855796688088448489867151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 36513992025107135567665109 855796688088448489867151)
        ·
          refine ⟨1283695032132672734800727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855796688088448489867151 1283695032132672734800727)
          ·
            refine ⟨1925542548199009102201091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283695032132672734800727 1925542548199009102201091)
            ·
              refine ⟨2888313822298513653301637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925542548199009102201091 2888313822298513653301637)
              ·
                refine ⟨541558841680971309994057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2888313822298513653301637 541558841680971309994057)
                ·
                  refine ⟨406169131260728482495543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541558841680971309994057 406169131260728482495543)
                  ·
                    rfl

theorem cell20_889888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 2].length) (baseStart_889888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889888 prefixEnd_889888 := by exact prefixLift 889888
  have htrace : WordTrace (prefixWord ++ tailWord_889888) baseStart_889888 baseEnd_889888 := by
    simpa [prefixWord, tailWord_889888, baseEnd_889888] using wordTrace_append hprefix tailTrace_889888
  have hstable : (prefixWord ++ tailWord_889888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889888).length < 2 ^ (prefixWord ++ tailWord_889888).sum := by decide
  have hdescent : baseEnd_889888 < baseStart_889888 := by decide
  rcases family_descends (prefixWord ++ tailWord_889888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889906 : List Nat := [3, 2, 1, 1, 2, 2, 1, 5, 3]
def baseStart_889906 : Nat := 118140960795 + 889906 * 2 ^ 59
def prefixEnd_889906 : Nat := 4983230072969 + 3 ^ 40 * 889906 * 2
def baseEnd_889906 : Nat := 406177346951200419895469

theorem tailTrace_889906 : CollatzResearch.WordTrace tailWord_889906 prefixEnd_889906 406177346951200419895469 := by
  unfold tailWord_889906
  simp only [CollatzResearch.WordTrace]
  refine ⟨8114384578507505172464393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21638358876020013793238381 8114384578507505172464393)
  ·
    refine ⟨6085788433880628879348295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8114384578507505172464393 6085788433880628879348295)
    ·
      refine ⟨9128682650820943319022443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6085788433880628879348295 9128682650820943319022443)
      ·
        refine ⟨13693023976231414978533665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9128682650820943319022443 13693023976231414978533665)
        ·
          refine ⟨10269767982173561233900249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13693023976231414978533665 10269767982173561233900249)
          ·
            refine ⟨7702325986630170925425187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10269767982173561233900249 7702325986630170925425187)
            ·
              refine ⟨11553488979945256388137781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7702325986630170925425187 11553488979945256388137781)
              ·
                refine ⟨1083139591869867786387917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11553488979945256388137781 1083139591869867786387917)
                ·
                  refine ⟨406177346951200419895469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083139591869867786387917 406177346951200419895469)
                  ·
                    rfl

theorem cell20_889906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_889906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889906 prefixEnd_889906 := by exact prefixLift 889906
  have htrace : WordTrace (prefixWord ++ tailWord_889906) baseStart_889906 baseEnd_889906 := by
    simpa [prefixWord, tailWord_889906, baseEnd_889906] using wordTrace_append hprefix tailTrace_889906
  have hstable : (prefixWord ++ tailWord_889906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889906).length < 2 ^ (prefixWord ++ tailWord_889906).sum := by decide
  have hdescent : baseEnd_889906 < baseStart_889906 := by decide
  rcases family_descends (prefixWord ++ tailWord_889906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889913 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 6]
def baseStart_889913 : Nat := 118140960795 + 889913 * 2 ^ 59
def prefixEnd_889913 : Nat := 4983230072969 + 3 ^ 40 * 889913 * 2
def baseEnd_889913 : Nat := 406180541941939506662107

theorem tailTrace_889913 : CollatzResearch.WordTrace tailWord_889913 prefixEnd_889913 406180541941939506662107 := by
  unfold tailWord_889913
  simp only [CollatzResearch.WordTrace]
  refine ⟨32457793625004660885362393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21638529083336440590241595 32457793625004660885362393)
  ·
    refine ⟨24343345218753495664021795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32457793625004660885362393 24343345218753495664021795)
    ·
      refine ⟨36515017828130243496032693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24343345218753495664021795 36515017828130243496032693)
      ·
        refine ⟨3423282921387210327753065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36515017828130243496032693 3423282921387210327753065)
        ·
          refine ⟨2567462191040407745814799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3423282921387210327753065 2567462191040407745814799)
          ·
            refine ⟨3851193286560611618722199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567462191040407745814799 3851193286560611618722199)
            ·
              refine ⟨5776789929840917428083299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851193286560611618722199 5776789929840917428083299)
              ·
                refine ⟨8665184894761376142124949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5776789929840917428083299 8665184894761376142124949)
                ·
                  refine ⟨406180541941939506662107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8665184894761376142124949 406180541941939506662107)
                  ·
                    rfl

theorem cell20_889913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_889913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889913 prefixEnd_889913 := by exact prefixLift 889913
  have htrace : WordTrace (prefixWord ++ tailWord_889913) baseStart_889913 baseEnd_889913 := by
    simpa [prefixWord, tailWord_889913, baseEnd_889913] using wordTrace_append hprefix tailTrace_889913
  have hstable : (prefixWord ++ tailWord_889913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889913).length < 2 ^ (prefixWord ++ tailWord_889913).sum := by decide
  have hdescent : baseEnd_889913 < baseStart_889913 := by decide
  rcases family_descends (prefixWord ++ tailWord_889913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889926 : List Nat := [6, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_889926 : Nat := 118140960795 + 889926 * 2 ^ 59
def prefixEnd_889926 : Nat := 4983230072969 + 3 ^ 40 * 889926 * 2
def baseEnd_889926 : Nat := 406186475496169239228721

theorem tailTrace_889926 : CollatzResearch.WordTrace tailWord_889926 prefixEnd_889926 406186475496169239228721 := by
  unfold tailWord_889926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1014320867936173878299551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21638845182638376070390421 1014320867936173878299551)
  ·
    refine ⟨1521481301904260817449327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1014320867936173878299551 1521481301904260817449327)
    ·
      refine ⟨2282221952856391226173991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1521481301904260817449327 2282221952856391226173991)
      ·
        refine ⟨3423332929284586839260987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2282221952856391226173991 3423332929284586839260987)
        ·
          refine ⟨5134999393926880258891481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3423332929284586839260987 5134999393926880258891481)
          ·
            refine ⟨3851249545445160194168611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5134999393926880258891481 3851249545445160194168611)
            ·
              refine ⟨5776874318167740291252917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851249545445160194168611 5776874318167740291252917)
              ·
                refine ⟨541581967328225652304961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5776874318167740291252917 541581967328225652304961)
                ·
                  refine ⟨406186475496169239228721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541581967328225652304961 406186475496169239228721)
                  ·
                    rfl

theorem cell20_889926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_889926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889926 prefixEnd_889926 := by exact prefixLift 889926
  have htrace : WordTrace (prefixWord ++ tailWord_889926) baseStart_889926 baseEnd_889926 := by
    simpa [prefixWord, tailWord_889926, baseEnd_889926] using wordTrace_append hprefix tailTrace_889926
  have hstable : (prefixWord ++ tailWord_889926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889926).length < 2 ^ (prefixWord ++ tailWord_889926).sum := by decide
  have hdescent : baseEnd_889926 < baseStart_889926 := by decide
  rcases family_descends (prefixWord ++ tailWord_889926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889930 : List Nat := [3, 1, 2, 1, 1, 2, 3, 5, 2]
def baseStart_889930 : Nat := 118140960795 + 889930 * 2 ^ 59
def prefixEnd_889930 : Nat := 4983230072969 + 3 ^ 40 * 889930 * 2
def baseEnd_889930 : Nat := 406188301205163003095371

theorem tailTrace_889930 : CollatzResearch.WordTrace tailWord_889930 prefixEnd_889930 406188301205163003095371 := by
  unfold tailWord_889930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8114603416485768197182811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21638942443962048525820829 8114603416485768197182811)
  ·
    refine ⟨12171905124728652295774217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8114603416485768197182811 12171905124728652295774217)
    ·
      refine ⟨9128928843546489221830663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12171905124728652295774217 9128928843546489221830663)
      ·
        refine ⟨13693393265319733832745995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9128928843546489221830663 13693393265319733832745995)
        ·
          refine ⟨20540089897979600749118993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13693393265319733832745995 20540089897979600749118993)
          ·
            refine ⟨15405067423484700561839245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20540089897979600749118993 15405067423484700561839245)
            ·
              refine ⟨5776900283806762710689717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15405067423484700561839245 5776900283806762710689717)
              ·
                refine ⟨541584401606884004127161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5776900283806762710689717 541584401606884004127161)
                ·
                  refine ⟨406188301205163003095371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541584401606884004127161 406188301205163003095371)
                  ·
                    rfl

theorem cell20_889930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_889930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889930 prefixEnd_889930 := by exact prefixLift 889930
  have htrace : WordTrace (prefixWord ++ tailWord_889930) baseStart_889930 baseEnd_889930 := by
    simpa [prefixWord, tailWord_889930, baseEnd_889930] using wordTrace_append hprefix tailTrace_889930
  have hstable : (prefixWord ++ tailWord_889930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889930).length < 2 ^ (prefixWord ++ tailWord_889930).sum := by decide
  have hdescent : baseEnd_889930 < baseStart_889930 := by decide
  rcases family_descends (prefixWord ++ tailWord_889930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889951 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 4]
def baseStart_889951 : Nat := 118140960795 + 889951 * 2 ^ 59
def prefixEnd_889951 : Nat := 4983230072969 + 3 ^ 40 * 889951 * 2
def baseEnd_889951 : Nat := 406197886177380263395285

theorem tailTrace_889951 : CollatzResearch.WordTrace tailWord_889951 prefixEnd_889951 406197886177380263395285 := by
  unfold tailWord_889951
  simp only [CollatzResearch.WordTrace]
  refine ⟨32459179598866993375245707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21639453065911328916830471 32459179598866993375245707)
  ·
    refine ⟨48688769398300490062868561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32459179598866993375245707 48688769398300490062868561)
    ·
      refine ⟨36516577048725367547151421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48688769398300490062868561 36516577048725367547151421)
      ·
        refine ⟨13693716393272012830181783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36516577048725367547151421 13693716393272012830181783)
        ·
          refine ⟨20540574589908019245272675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13693716393272012830181783 20540574589908019245272675)
          ·
            refine ⟨30810861884862028867909013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20540574589908019245272675 30810861884862028867909013)
            ·
              refine ⟨1444259150852907603183235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30810861884862028867909013 1444259150852907603183235)
              ·
                refine ⟨2166388726279361404774853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444259150852907603183235 2166388726279361404774853)
                ·
                  refine ⟨406197886177380263395285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2166388726279361404774853 406197886177380263395285)
                  ·
                    rfl

theorem cell20_889951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 4].length) (baseStart_889951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889951 prefixEnd_889951 := by exact prefixLift 889951
  have htrace : WordTrace (prefixWord ++ tailWord_889951) baseStart_889951 baseEnd_889951 := by
    simpa [prefixWord, tailWord_889951, baseEnd_889951] using wordTrace_append hprefix tailTrace_889951
  have hstable : (prefixWord ++ tailWord_889951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889951).length < 2 ^ (prefixWord ++ tailWord_889951).sum := by decide
  have hdescent : baseEnd_889951 < baseStart_889951 := by decide
  rcases family_descends (prefixWord ++ tailWord_889951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889961 : List Nat := [1, 2, 1, 1, 1, 7, 3, 1, 3]
def baseStart_889961 : Nat := 118140960795 + 889961 * 2 ^ 59
def prefixEnd_889961 : Nat := 4983230072969 + 3 ^ 40 * 889961 * 2
def baseEnd_889961 : Nat := 406202450449864673061911

theorem tailTrace_889961 : CollatzResearch.WordTrace tailWord_889961 prefixEnd_889961 406202450449864673061911 := by
  unfold tailWord_889961
  simp only [CollatzResearch.WordTrace]
  refine ⟨32459544328830765083109737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21639696219220510055406491 32459544328830765083109737)
  ·
    refine ⟨24344658246623073812332303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32459544328830765083109737 24344658246623073812332303)
    ·
      refine ⟨36516987369934610718498455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24344658246623073812332303 36516987369934610718498455)
      ·
        refine ⟨54775481054901916077747683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36516987369934610718498455 54775481054901916077747683)
        ·
          refine ⟨82163221582352874116621525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54775481054901916077747683 82163221582352874116621525)
          ·
            refine ⟨1925700505836395487108317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 82163221582352874116621525 1925700505836395487108317)
            ·
              refine ⟨722137689688648307665619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1925700505836395487108317 722137689688648307665619)
              ·
                refine ⟨1083206534532972461498429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722137689688648307665619 1083206534532972461498429)
                ·
                  refine ⟨406202450449864673061911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083206534532972461498429 406202450449864673061911)
                  ·
                    rfl

theorem cell20_889961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_889961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889961 prefixEnd_889961 := by exact prefixLift 889961
  have htrace : WordTrace (prefixWord ++ tailWord_889961) baseStart_889961 baseEnd_889961 := by
    simpa [prefixWord, tailWord_889961, baseEnd_889961] using wordTrace_append hprefix tailTrace_889961
  have hstable : (prefixWord ++ tailWord_889961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889961).length < 2 ^ (prefixWord ++ tailWord_889961).sum := by decide
  have hdescent : baseEnd_889961 < baseStart_889961 := by decide
  rcases family_descends (prefixWord ++ tailWord_889961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889985 : List Nat := [1, 2, 4, 2, 2, 1, 3, 3, 2]
def baseStart_889985 : Nat := 118140960795 + 889985 * 2 ^ 59
def prefixEnd_889985 : Nat := 4983230072969 + 3 ^ 40 * 889985 * 2
def baseEnd_889985 : Nat := 406213404703827256261813

theorem tailTrace_889985 : CollatzResearch.WordTrace tailWord_889985 prefixEnd_889985 406213404703827256261813 := by
  unfold tailWord_889985
  simp only [CollatzResearch.WordTrace]
  refine ⟨32460419680743817181983409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21640279787162544787988939 32460419680743817181983409)
  ·
    refine ⟨24345314760557862886487557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32460419680743817181983409 24345314760557862886487557)
    ·
      refine ⟨4564746517604599291216417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24345314760557862886487557 4564746517604599291216417)
      ·
        refine ⟨3423559888203449468412313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4564746517604599291216417 3423559888203449468412313)
        ·
          refine ⟨2567669916152587101309235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3423559888203449468412313 2567669916152587101309235)
          ·
            refine ⟨3851504874228880651963853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567669916152587101309235 3851504874228880651963853)
            ·
              refine ⟨1444314327835830244486445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3851504874228880651963853 1444314327835830244486445)
              ·
                refine ⟨541617872938436341682417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1444314327835830244486445 541617872938436341682417)
                ·
                  refine ⟨406213404703827256261813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541617872938436341682417 406213404703827256261813)
                  ·
                    rfl

theorem cell20_889985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 2].length) (baseStart_889985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889985 prefixEnd_889985 := by exact prefixLift 889985
  have htrace : WordTrace (prefixWord ++ tailWord_889985) baseStart_889985 baseEnd_889985 := by
    simpa [prefixWord, tailWord_889985, baseEnd_889985] using wordTrace_append hprefix tailTrace_889985
  have hstable : (prefixWord ++ tailWord_889985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889985).length < 2 ^ (prefixWord ++ tailWord_889985).sum := by decide
  have hdescent : baseEnd_889985 < baseStart_889985 := by decide
  rcases family_descends (prefixWord ++ tailWord_889985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889992 : List Nat := [2, 1, 3, 4, 3, 1, 6]
def baseStart_889992 : Nat := 118140960795 + 889992 * 2 ^ 59
def prefixEnd_889992 : Nat := 4983230072969 + 3 ^ 40 * 889992 * 2
def baseEnd_889992 : Nat := 45135177743840704780939

theorem tailTrace_889992 : CollatzResearch.WordTrace tailWord_889992 prefixEnd_889992 45135177743840704780939 := by
  unfold tailWord_889992
  simp only [CollatzResearch.WordTrace]
  refine ⟨16230337495859228688744115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21640449994478971584992153 16230337495859228688744115)
  ·
    refine ⟨24345506243788843033116173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16230337495859228688744115 24345506243788843033116173)
    ·
      refine ⟨9129564841420816137418565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24345506243788843033116173 9129564841420816137418565)
      ·
        refine ⟨1711793407766403025765981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9129564841420816137418565 1711793407766403025765981)
        ·
          refine ⟨641922527912401134662243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1711793407766403025765981 641922527912401134662243)
          ·
            refine ⟨962883791868601701993365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641922527912401134662243 962883791868601701993365)
            ·
              refine ⟨45135177743840704780939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 962883791868601701993365 45135177743840704780939)
              ·
                rfl

theorem cell20_889992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 6].length) (baseStart_889992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_889992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_889992 prefixEnd_889992 := by exact prefixLift 889992
  have htrace : WordTrace (prefixWord ++ tailWord_889992) baseStart_889992 baseEnd_889992 := by
    simpa [prefixWord, tailWord_889992, baseEnd_889992] using wordTrace_append hprefix tailTrace_889992
  have hstable : (prefixWord ++ tailWord_889992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889992).length < 2 ^ (prefixWord ++ tailWord_889992).sum := by decide
  have hdescent : baseEnd_889992 < baseStart_889992 := by decide
  rcases family_descends (prefixWord ++ tailWord_889992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890002 : List Nat := [3, 2, 3, 1, 1, 3, 3, 2, 2]
def baseStart_890002 : Nat := 118140960795 + 890002 * 2 ^ 59
def prefixEnd_890002 : Nat := 4983230072969 + 3 ^ 40 * 890002 * 2
def baseEnd_890002 : Nat := 406221163967050752695077

theorem tailTrace_890002 : CollatzResearch.WordTrace tailWord_890002 prefixEnd_890002 406221163967050752695077 := by
  unfold tailWord_890002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8115259930420557271338065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21640693147788152723568173 8115259930420557271338065)
  ·
    refine ⟨6086444947815417953503549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8115259930420557271338065 6086444947815417953503549)
    ·
      refine ⟨2282416855430781732563831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6086444947815417953503549 2282416855430781732563831)
      ·
        refine ⟨3423625283146172598845747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2282416855430781732563831 3423625283146172598845747)
        ·
          refine ⟨5135437924719258898268621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3423625283146172598845747 5135437924719258898268621)
          ·
            refine ⟨1925789221769722086850733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5135437924719258898268621 1925789221769722086850733)
            ·
              refine ⟨722170958163645782569025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1925789221769722086850733 722170958163645782569025)
              ·
                refine ⟨541628218622734336926769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 722170958163645782569025 541628218622734336926769)
                ·
                  refine ⟨406221163967050752695077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541628218622734336926769 406221163967050752695077)
                  ·
                    rfl

theorem cell20_890002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_890002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890002 prefixEnd_890002 := by exact prefixLift 890002
  have htrace : WordTrace (prefixWord ++ tailWord_890002) baseStart_890002 baseEnd_890002 := by
    simpa [prefixWord, tailWord_890002, baseEnd_890002] using wordTrace_append hprefix tailTrace_890002
  have hstable : (prefixWord ++ tailWord_890002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890002).length < 2 ^ (prefixWord ++ tailWord_890002).sum := by decide
  have hdescent : baseEnd_890002 < baseStart_890002 := by decide
  rcases family_descends (prefixWord ++ tailWord_890002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890003 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 5]
def baseStart_890003 : Nat := 118140960795 + 890003 * 2 ^ 59
def prefixEnd_890003 : Nat := 4983230072969 + 3 ^ 40 * 890003 * 2
def baseEnd_890003 : Nat := 406221620394299193661739

theorem tailTrace_890003 : CollatzResearch.WordTrace tailWord_890003 prefixEnd_890003 406221620394299193661739 := by
  unfold tailWord_890003
  simp only [CollatzResearch.WordTrace]
  refine ⟨32461076194678606256138663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21640717463119070837425775 32461076194678606256138663)
  ·
    refine ⟨48691614292017909384207995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32461076194678606256138663 48691614292017909384207995)
    ·
      refine ⟨73037421438026864076311993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48691614292017909384207995 73037421438026864076311993)
      ·
        refine ⟨54778066078520148057233995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73037421438026864076311993 54778066078520148057233995)
        ·
          refine ⟨82167099117780222085850993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54778066078520148057233995 82167099117780222085850993)
          ·
            refine ⟨61625324338335166564388245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82167099117780222085850993 61625324338335166564388245)
            ·
              refine ⟨2888687078359460932705699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61625324338335166564388245 2888687078359460932705699)
              ·
                refine ⟨4333030617539191399058549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888687078359460932705699 4333030617539191399058549)
                ·
                  refine ⟨406221620394299193661739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4333030617539191399058549 406221620394299193661739)
                  ·
                    rfl

theorem cell20_890003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_890003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890003 prefixEnd_890003 := by exact prefixLift 890003
  have htrace : WordTrace (prefixWord ++ tailWord_890003) baseStart_890003 baseEnd_890003 := by
    simpa [prefixWord, tailWord_890003, baseEnd_890003] using wordTrace_append hprefix tailTrace_890003
  have hstable : (prefixWord ++ tailWord_890003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890003).length < 2 ^ (prefixWord ++ tailWord_890003).sum := by decide
  have hdescent : baseEnd_890003 < baseStart_890003 := by decide
  rcases family_descends (prefixWord ++ tailWord_890003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890034 : List Nat := [3, 2, 1, 1, 1, 4, 2, 6]
def baseStart_890034 : Nat := 118140960795 + 890034 * 2 ^ 59
def prefixEnd_890034 : Nat := 4983230072969 + 3 ^ 40 * 890034 * 2
def baseEnd_890034 : Nat := 135411923213000287876093

theorem tailTrace_890034 : CollatzResearch.WordTrace tailWord_890034 prefixEnd_890034 135411923213000287876093 := by
  unfold tailWord_890034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8115551714391574637629289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21641471238377532367011437 8115551714391574637629289)
  ·
    refine ⟨6086663785793680978221967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8115551714391574637629289 6086663785793680978221967)
    ·
      refine ⟨9129995678690521467332951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6086663785793680978221967 9129995678690521467332951)
      ·
        refine ⟨13694993518035782200999427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9129995678690521467332951 13694993518035782200999427)
        ·
          refine ⟨20542490277053673301499141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13694993518035782200999427 20542490277053673301499141)
          ·
            refine ⟨3851716926947563744031089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20542490277053673301499141 3851716926947563744031089)
            ·
              refine ⟨2888787695210672808023317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3851716926947563744031089 2888787695210672808023317)
              ·
                refine ⟨135411923213000287876093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2888787695210672808023317 135411923213000287876093)
                ·
                  rfl

theorem cell20_890034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_890034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890034 prefixEnd_890034 := by exact prefixLift 890034
  have htrace : WordTrace (prefixWord ++ tailWord_890034) baseStart_890034 baseEnd_890034 := by
    simpa [prefixWord, tailWord_890034, baseEnd_890034] using wordTrace_append hprefix tailTrace_890034
  have hstable : (prefixWord ++ tailWord_890034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890034).length < 2 ^ (prefixWord ++ tailWord_890034).sum := by decide
  have hdescent : baseEnd_890034 < baseStart_890034 := by decide
  rcases family_descends (prefixWord ++ tailWord_890034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890058 : List Nat := [3, 1, 2, 1, 3, 2, 1, 4, 3]
def baseStart_890058 : Nat := 118140960795 + 890058 * 2 ^ 59
def prefixEnd_890058 : Nat := 4983230072969 + 3 ^ 40 * 890058 * 2
def baseEnd_890058 : Nat := 406246723892963446828181

theorem tailTrace_890058 : CollatzResearch.WordTrace tailWord_890058 prefixEnd_890058 406246723892963446828181 := by
  unfold tailWord_890058
  simp only [CollatzResearch.WordTrace]
  refine ⟨8115770552369837662347707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21642054806319567099593885 8115770552369837662347707)
  ·
    refine ⟨12173655828554756493521561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8115770552369837662347707 12173655828554756493521561)
    ·
      refine ⟨9130241871416067370141171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12173655828554756493521561 9130241871416067370141171)
      ·
        refine ⟨13695362807124101055211757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9130241871416067370141171 13695362807124101055211757)
        ·
          refine ⟨5135761052671537895704409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13695362807124101055211757 5135761052671537895704409)
          ·
            refine ⟨3851820789503653421778307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5135761052671537895704409 3851820789503653421778307)
            ·
              refine ⟨5777731184255480132667461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851820789503653421778307 5777731184255480132667461)
              ·
                refine ⟨1083324597047902524875149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5777731184255480132667461 1083324597047902524875149)
                ·
                  refine ⟨406246723892963446828181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083324597047902524875149 406246723892963446828181)
                  ·
                    rfl

theorem cell20_890058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_890058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890058 prefixEnd_890058 := by exact prefixLift 890058
  have htrace : WordTrace (prefixWord ++ tailWord_890058) baseStart_890058 baseEnd_890058 := by
    simpa [prefixWord, tailWord_890058, baseEnd_890058] using wordTrace_append hprefix tailTrace_890058
  have hstable : (prefixWord ++ tailWord_890058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890058).length < 2 ^ (prefixWord ++ tailWord_890058).sum := by decide
  have hdescent : baseEnd_890058 < baseStart_890058 := by decide
  rcases family_descends (prefixWord ++ tailWord_890058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890113 : List Nat := [1, 2, 4, 1, 1, 5, 1, 2, 3]
def baseStart_890113 : Nat := 118140960795 + 890113 * 2 ^ 59
def prefixEnd_890113 : Nat := 4983230072969 + 3 ^ 40 * 890113 * 2
def baseEnd_890113 : Nat := 406271827391627699994623

theorem tailTrace_890113 : CollatzResearch.WordTrace tailWord_890113 prefixEnd_890113 406271827391627699994623 := by
  unfold tailWord_890113
  simp only [CollatzResearch.WordTrace]
  refine ⟨32465088224280095042642993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21643392149520063361761995 32465088224280095042642993)
  ·
    refine ⟨24348816168210071281982245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32465088224280095042642993 24348816168210071281982245)
    ·
      refine ⟨4565403031539388365371671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24348816168210071281982245 4565403031539388365371671)
      ·
        refine ⟨6848104547309082548057507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4565403031539388365371671 6848104547309082548057507)
        ·
          refine ⟨10272156820963623822086261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6848104547309082548057507 10272156820963623822086261)
          ·
            refine ⟨963014701965339733320587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10272156820963623822086261 963014701965339733320587)
            ·
              refine ⟨1444522052948009599980881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963014701965339733320587 1444522052948009599980881)
              ·
                refine ⟨1083391539711007199985661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1444522052948009599980881 1083391539711007199985661)
                ·
                  refine ⟨406271827391627699994623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083391539711007199985661 406271827391627699994623)
                  ·
                    rfl

theorem cell20_890113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_890113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890113 prefixEnd_890113 := by exact prefixLift 890113
  have htrace : WordTrace (prefixWord ++ tailWord_890113) baseStart_890113 baseEnd_890113 := by
    simpa [prefixWord, tailWord_890113, baseEnd_890113] using wordTrace_append hprefix tailTrace_890113
  have hstable : (prefixWord ++ tailWord_890113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890113).length < 2 ^ (prefixWord ++ tailWord_890113).sum := by decide
  have hdescent : baseEnd_890113 < baseStart_890113 := by decide
  rcases family_descends (prefixWord ++ tailWord_890113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890117 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 5]
def baseStart_890117 : Nat := 118140960795 + 890117 * 2 ^ 59
def prefixEnd_890117 : Nat := 4983230072969 + 3 ^ 40 * 890117 * 2
def baseEnd_890117 : Nat := 406273653100621463861273

theorem tailTrace_890117 : CollatzResearch.WordTrace tailWord_890117 prefixEnd_890117 406273653100621463861273 := by
  unfold tailWord_890117
  simp only [CollatzResearch.WordTrace]
  refine ⟨32465234116265603725788605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21643489410843735817192403 32465234116265603725788605)
  ·
    refine ⟨12174462793599601397170727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32465234116265603725788605 12174462793599601397170727)
    ·
      refine ⟨18261694190399402095756091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12174462793599601397170727 18261694190399402095756091)
      ·
        refine ⟨27392541285599103143634137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18261694190399402095756091 27392541285599103143634137)
        ·
          refine ⟨20544405964199327357725603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27392541285599103143634137 20544405964199327357725603)
          ·
            refine ⟨30816608946298991036588405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20544405964199327357725603 30816608946298991036588405)
            ·
              refine ⟨2889057088715530409680163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30816608946298991036588405 2889057088715530409680163)
              ·
                refine ⟨4333585633073295614520245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2889057088715530409680163 4333585633073295614520245)
                ·
                  refine ⟨406273653100621463861273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4333585633073295614520245 406273653100621463861273)
                  ·
                    rfl

theorem cell20_890117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_890117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890117 prefixEnd_890117 := by exact prefixLift 890117
  have htrace : WordTrace (prefixWord ++ tailWord_890117) baseStart_890117 baseEnd_890117 := by
    simpa [prefixWord, tailWord_890117, baseEnd_890117] using wordTrace_append hprefix tailTrace_890117
  have hstable : (prefixWord ++ tailWord_890117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890117).length < 2 ^ (prefixWord ++ tailWord_890117).sum := by decide
  have hdescent : baseEnd_890117 < baseStart_890117 := by decide
  rcases family_descends (prefixWord ++ tailWord_890117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890120 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 4]
def baseStart_890120 : Nat := 118140960795 + 890120 * 2 ^ 59
def prefixEnd_890120 : Nat := 4983230072969 + 3 ^ 40 * 890120 * 2
def baseEnd_890120 : Nat := 406275022382366786761261

theorem tailTrace_890120 : CollatzResearch.WordTrace tailWord_890120 prefixEnd_890120 406275022382366786761261 := by
  unfold tailWord_890120
  simp only [CollatzResearch.WordTrace]
  refine ⟨16232671767627367619073907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21643562356836490158765209 16232671767627367619073907)
  ·
    refine ⟨24349007651441051428610861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16232671767627367619073907 24349007651441051428610861)
    ·
      refine ⟨9130877869290394285729073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24349007651441051428610861 9130877869290394285729073)
      ·
        refine ⟨6848158401967795714296805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9130877869290394285729073 6848158401967795714296805)
        ·
          refine ⟨1284029700368961696430651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6848158401967795714296805 1284029700368961696430651)
          ·
            refine ⟨1926044550553442544645977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284029700368961696430651 1926044550553442544645977)
            ·
              refine ⟨1444533412915081908484483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1926044550553442544645977 1444533412915081908484483)
              ·
                refine ⟨2166800119372622862726725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444533412915081908484483 2166800119372622862726725)
                ·
                  refine ⟨406275022382366786761261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2166800119372622862726725 406275022382366786761261)
                  ·
                    rfl

theorem cell20_890120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_890120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890120 prefixEnd_890120 := by exact prefixLift 890120
  have htrace : WordTrace (prefixWord ++ tailWord_890120) baseStart_890120 baseEnd_890120 := by
    simpa [prefixWord, tailWord_890120, baseEnd_890120] using wordTrace_append hprefix tailTrace_890120
  have hstable : (prefixWord ++ tailWord_890120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890120).length < 2 ^ (prefixWord ++ tailWord_890120).sum := by decide
  have hdescent : baseEnd_890120 < baseStart_890120 := by decide
  rcases family_descends (prefixWord ++ tailWord_890120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890144 : List Nat := [2, 1, 1, 5, 3, 2, 2, 4]
def baseStart_890144 : Nat := 118140960795 + 890144 * 2 ^ 59
def prefixEnd_890144 : Nat := 4983230072969 + 3 ^ 40 * 890144 * 2
def baseEnd_890144 : Nat := 135428658878776456653721

theorem tailTrace_890144 : CollatzResearch.WordTrace tailWord_890144 prefixEnd_890144 135428658878776456653721 := by
  unfold tailWord_890144
  simp only [CollatzResearch.WordTrace]
  refine ⟨16233109443583893668510743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21644145924778524891347657 16233109443583893668510743)
  ·
    refine ⟨24349664165375840502766115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16233109443583893668510743 24349664165375840502766115)
    ·
      refine ⟨36524496248063760754149173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24349664165375840502766115 36524496248063760754149173)
      ·
        refine ⟨3424171523255977570701485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36524496248063760754149173 3424171523255977570701485)
        ·
          refine ⟨1284064321220991589013057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3424171523255977570701485 1284064321220991589013057)
          ·
            refine ⟨963048240915743691759793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1284064321220991589013057 963048240915743691759793)
            ·
              refine ⟨722286180686807768819845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963048240915743691759793 722286180686807768819845)
              ·
                refine ⟨135428658878776456653721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 722286180686807768819845 135428658878776456653721)
                ·
                  rfl

theorem cell20_890144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_890144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890144 prefixEnd_890144 := by exact prefixLift 890144
  have htrace : WordTrace (prefixWord ++ tailWord_890144) baseStart_890144 baseEnd_890144 := by
    simpa [prefixWord, tailWord_890144, baseEnd_890144] using wordTrace_append hprefix tailTrace_890144
  have hstable : (prefixWord ++ tailWord_890144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890144).length < 2 ^ (prefixWord ++ tailWord_890144).sum := by decide
  have hdescent : baseEnd_890144 < baseStart_890144 := by decide
  rcases family_descends (prefixWord ++ tailWord_890144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890148 : List Nat := [2, 3, 1, 3, 1, 1, 3, 6]
def baseStart_890148 : Nat := 118140960795 + 890148 * 2 ^ 59
def prefixEnd_890148 : Nat := 4983230072969 + 3 ^ 40 * 890148 * 2
def baseEnd_890148 : Nat := 135429267448441044609271

theorem tailTrace_890148 : CollatzResearch.WordTrace tailWord_890148 prefixEnd_890148 135429267448441044609271 := by
  unfold tailWord_890148
  simp only [CollatzResearch.WordTrace]
  refine ⟨16233182389576648010083549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21644243186102197346778065 16233182389576648010083549)
  ·
    refine ⟨6087443396091243003781331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16233182389576648010083549 6087443396091243003781331)
    ·
      refine ⟨9131165094136864505671997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6087443396091243003781331 9131165094136864505671997)
      ·
        refine ⟨3424186910301324189626999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9131165094136864505671997 3424186910301324189626999)
        ·
          refine ⟨5136280365451986284440499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3424186910301324189626999 5136280365451986284440499)
          ·
            refine ⟨7704420548177979426660749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5136280365451986284440499 7704420548177979426660749)
            ·
              refine ⟨2889157705566742284997781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7704420548177979426660749 2889157705566742284997781)
              ·
                refine ⟨135429267448441044609271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2889157705566742284997781 135429267448441044609271)
                ·
                  rfl

theorem cell20_890148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_890148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890148 prefixEnd_890148 := by exact prefixLift 890148
  have htrace : WordTrace (prefixWord ++ tailWord_890148) baseStart_890148 baseEnd_890148 := by
    simpa [prefixWord, tailWord_890148, baseEnd_890148] using wordTrace_append hprefix tailTrace_890148
  have hstable : (prefixWord ++ tailWord_890148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890148).length < 2 ^ (prefixWord ++ tailWord_890148).sum := by decide
  have hdescent : baseEnd_890148 < baseStart_890148 := by decide
  rcases family_descends (prefixWord ++ tailWord_890148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890154 : List Nat := [3, 1, 4, 2, 1, 3, 1, 3, 2]
def baseStart_890154 : Nat := 118140960795 + 890154 * 2 ^ 59
def prefixEnd_890154 : Nat := 4983230072969 + 3 ^ 40 * 890154 * 2
def baseEnd_890154 : Nat := 406290540908813779627789

theorem tailTrace_890154 : CollatzResearch.WordTrace tailWord_890154 prefixEnd_890154 406290540908813779627789 := by
  unfold tailWord_890154
  simp only [CollatzResearch.WordTrace]
  refine ⟨8116645904282889761221379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21644389078087706029923677 8116645904282889761221379)
  ·
    refine ⟨12174968856424334641832069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8116645904282889761221379 12174968856424334641832069)
    ·
      refine ⟨2282806660579562745343513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12174968856424334641832069 2282806660579562745343513)
      ·
        refine ⟨1712104995434672059007635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2282806660579562745343513 1712104995434672059007635)
        ·
          refine ⟨2568157493152008088511453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1712104995434672059007635 2568157493152008088511453)
          ·
            refine ⟨963059059932003033191795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2568157493152008088511453 963059059932003033191795)
            ·
              refine ⟨1444588589898004549787693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963059059932003033191795 1444588589898004549787693)
              ·
                refine ⟨541720721211751706170385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1444588589898004549787693 541720721211751706170385)
                ·
                  refine ⟨406290540908813779627789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541720721211751706170385 406290540908813779627789)
                  ·
                    rfl

theorem cell20_890154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_890154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890154 prefixEnd_890154 := by exact prefixLift 890154
  have htrace : WordTrace (prefixWord ++ tailWord_890154) baseStart_890154 baseEnd_890154 := by
    simpa [prefixWord, tailWord_890154, baseEnd_890154] using wordTrace_append hprefix tailTrace_890154
  have hstable : (prefixWord ++ tailWord_890154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890154).length < 2 ^ (prefixWord ++ tailWord_890154).sum := by decide
  have hdescent : baseEnd_890154 < baseStart_890154 := by decide
  rcases family_descends (prefixWord ++ tailWord_890154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890175 : List Nat := [1, 1, 2, 2, 4, 3, 3, 2, 2]
def baseStart_890175 : Nat := 118140960795 + 890175 * 2 ^ 59
def prefixEnd_890175 : Nat := 4983230072969 + 3 ^ 40 * 890175 * 2
def baseEnd_890175 : Nat := 406300125881031039927703

theorem tailTrace_890175 : CollatzResearch.WordTrace tailWord_890175 prefixEnd_890175 406300125881031039927703 := by
  unfold tailWord_890175
  simp only [CollatzResearch.WordTrace]
  refine ⟨32467349550055479631399979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21644899700036986420933319 32467349550055479631399979)
  ·
    refine ⟨48701024325083219447099969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32467349550055479631399979 48701024325083219447099969)
    ·
      refine ⟨36525768243812414585324977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48701024325083219447099969 36525768243812414585324977)
      ·
        refine ⟨27394326182859310938993733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36525768243812414585324977 27394326182859310938993733)
        ·
          refine ⟨5136436159286120801061325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27394326182859310938993733 5136436159286120801061325)
          ·
            refine ⟨1926163559732295300397997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5136436159286120801061325 1926163559732295300397997)
            ·
              refine ⟨722311334899610737649249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1926163559732295300397997 722311334899610737649249)
              ·
                refine ⟨541733501174708053236937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 722311334899610737649249 541733501174708053236937)
                ·
                  refine ⟨406300125881031039927703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541733501174708053236937 406300125881031039927703)
                  ·
                    rfl

theorem cell20_890175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 2].length) (baseStart_890175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890175 prefixEnd_890175 := by exact prefixLift 890175
  have htrace : WordTrace (prefixWord ++ tailWord_890175) baseStart_890175 baseEnd_890175 := by
    simpa [prefixWord, tailWord_890175, baseEnd_890175] using wordTrace_append hprefix tailTrace_890175
  have hstable : (prefixWord ++ tailWord_890175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890175).length < 2 ^ (prefixWord ++ tailWord_890175).sum := by decide
  have hdescent : baseEnd_890175 < baseStart_890175 := by decide
  rcases family_descends (prefixWord ++ tailWord_890175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890200 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 6]
def baseStart_890200 : Nat := 118140960795 + 890200 * 2 ^ 59
def prefixEnd_890200 : Nat := 4983230072969 + 3 ^ 40 * 890200 * 2
def baseEnd_890200 : Nat := 406311536562242064094267

theorem tailTrace_890200 : CollatzResearch.WordTrace tailWord_890200 prefixEnd_890200 406311536562242064094267 := by
  unfold tailWord_890200
  simp only [CollatzResearch.WordTrace]
  refine ⟨16234130687482454450530027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21645507583309939267373369 16234130687482454450530027)
  ·
    refine ⟨24351196031223681675795041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16234130687482454450530027 24351196031223681675795041)
    ·
      refine ⟨18263397023417761256846281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24351196031223681675795041 18263397023417761256846281)
      ·
        refine ⟨13697547767563320942634711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18263397023417761256846281 13697547767563320942634711)
        ·
          refine ⟨20546321651344981413952067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13697547767563320942634711 20546321651344981413952067)
          ·
            refine ⟨30819482477017472120928101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20546321651344981413952067 30819482477017472120928101)
            ·
              refine ⟨5778652964440776022674019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30819482477017472120928101 5778652964440776022674019)
              ·
                refine ⟨8667979446661164034011029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5778652964440776022674019 8667979446661164034011029)
                ·
                  refine ⟨406311536562242064094267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8667979446661164034011029 406311536562242064094267)
                  ·
                    rfl

theorem cell20_890200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_890200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890200 prefixEnd_890200 := by exact prefixLift 890200
  have htrace : WordTrace (prefixWord ++ tailWord_890200) baseStart_890200 baseEnd_890200 := by
    simpa [prefixWord, tailWord_890200, baseEnd_890200] using wordTrace_append hprefix tailTrace_890200
  have hstable : (prefixWord ++ tailWord_890200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890200).length < 2 ^ (prefixWord ++ tailWord_890200).sum := by decide
  have hdescent : baseEnd_890200 < baseStart_890200 := by decide
  rcases family_descends (prefixWord ++ tailWord_890200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890248 : List Nat := [2, 1, 3, 3, 1, 2, 2, 3, 3]
def baseStart_890248 : Nat := 118140960795 + 890248 * 2 ^ 59
def prefixEnd_890248 : Nat := 4983230072969 + 3 ^ 40 * 890248 * 2
def baseEnd_890248 : Nat := 406333445070167230494071

theorem tailTrace_890248 : CollatzResearch.WordTrace tailWord_890248 prefixEnd_890248 406333445070167230494071 := by
  unfold tailWord_890248
  simp only [CollatzResearch.WordTrace]
  refine ⟨16235006039395506549403699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21646674719194008732538265 16235006039395506549403699)
  ·
    refine ⟨24352509059093259824105549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16235006039395506549403699 24352509059093259824105549)
    ·
      refine ⟨9132190897159972434039581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24352509059093259824105549 9132190897159972434039581)
      ·
        refine ⟨3424571586434989662764843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9132190897159972434039581 3424571586434989662764843)
        ·
          refine ⟨5136857379652484494147265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3424571586434989662764843 5136857379652484494147265)
          ·
            refine ⟨3852643034739363370610449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5136857379652484494147265 3852643034739363370610449)
            ·
              refine ⟨2889482276054522527957837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3852643034739363370610449 2889482276054522527957837)
              ·
                refine ⟨1083555853520445947984189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2889482276054522527957837 1083555853520445947984189)
                ·
                  refine ⟨406333445070167230494071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083555853520445947984189 406333445070167230494071)
                  ·
                    rfl

theorem cell20_890248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_890248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890248 prefixEnd_890248 := by exact prefixLift 890248
  have htrace : WordTrace (prefixWord ++ tailWord_890248) baseStart_890248 baseEnd_890248 := by
    simpa [prefixWord, tailWord_890248, baseEnd_890248] using wordTrace_append hprefix tailTrace_890248
  have hstable : (prefixWord ++ tailWord_890248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890248).length < 2 ^ (prefixWord ++ tailWord_890248).sum := by decide
  have hdescent : baseEnd_890248 < baseStart_890248 := by decide
  rcases family_descends (prefixWord ++ tailWord_890248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890268 : List Nat := [2, 2, 3, 4, 1, 1, 2, 3, 2]
def baseStart_890268 : Nat := 118140960795 + 890268 * 2 ^ 59
def prefixEnd_890268 : Nat := 4983230072969 + 3 ^ 40 * 890268 * 2
def baseEnd_890268 : Nat := 406342573615136049827323

theorem tailTrace_890268 : CollatzResearch.WordTrace tailWord_890268 prefixEnd_890268 406342573615136049827323 := by
  unfold tailWord_890268
  simp only [CollatzResearch.WordTrace]
  refine ⟨16235370769359278257267729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21647161025812371009690305 16235370769359278257267729)
  ·
    refine ⟨12176528077019458692950797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16235370769359278257267729 12176528077019458692950797)
    ·
      refine ⟨4566198028882297009856549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12176528077019458692950797 4566198028882297009856549)
      ·
        refine ⟨856162130415430689348103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4566198028882297009856549 856162130415430689348103)
        ·
          refine ⟨1284243195623146034022155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856162130415430689348103 1284243195623146034022155)
          ·
            refine ⟨1926364793434719051033233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284243195623146034022155 1926364793434719051033233)
            ·
              refine ⟨1444773595076039288274925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1926364793434719051033233 1444773595076039288274925)
              ·
                refine ⟨541790098153514733103097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1444773595076039288274925 541790098153514733103097)
                ·
                  refine ⟨406342573615136049827323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541790098153514733103097 406342573615136049827323)
                  ·
                    rfl

theorem cell20_890268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_890268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890268 prefixEnd_890268 := by exact prefixLift 890268
  have htrace : WordTrace (prefixWord ++ tailWord_890268) baseStart_890268 baseEnd_890268 := by
    simpa [prefixWord, tailWord_890268, baseEnd_890268] using wordTrace_append hprefix tailTrace_890268
  have hstable : (prefixWord ++ tailWord_890268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890268).length < 2 ^ (prefixWord ++ tailWord_890268).sum := by decide
  have hdescent : baseEnd_890268 < baseStart_890268 := by decide
  rcases family_descends (prefixWord ++ tailWord_890268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890272 : List Nat := [2, 1, 1, 4, 1, 2, 4, 3, 2]
def baseStart_890272 : Nat := 118140960795 + 890272 * 2 ^ 59
def prefixEnd_890272 : Nat := 4983230072969 + 3 ^ 40 * 890272 * 2
def baseEnd_890272 : Nat := 406344399324129813693973

theorem tailTrace_890272 : CollatzResearch.WordTrace tailWord_890272 prefixEnd_890272 406344399324129813693973 := by
  unfold tailWord_890272
  simp only [CollatzResearch.WordTrace]
  refine ⟨16235443715352032598840535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21647258287136043465120713 16235443715352032598840535)
  ·
    refine ⟨24353165573028048898260803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16235443715352032598840535 24353165573028048898260803)
    ·
      refine ⟨36529748359542073347391205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24353165573028048898260803 36529748359542073347391205)
      ·
        refine ⟨6849327817414138752635851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36529748359542073347391205 6849327817414138752635851)
        ·
          refine ⟨10273991726121208128953777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6849327817414138752635851 10273991726121208128953777)
          ·
            refine ⟨7705493794590906096715333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10273991726121208128953777 7705493794590906096715333)
            ·
              refine ⟨1444780086485794893134125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7705493794590906096715333 1444780086485794893134125)
              ·
                refine ⟨541792532432173084925297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1444780086485794893134125 541792532432173084925297)
                ·
                  refine ⟨406344399324129813693973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541792532432173084925297 406344399324129813693973)
                  ·
                    rfl

theorem cell20_890272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 2].length) (baseStart_890272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890272 prefixEnd_890272 := by exact prefixLift 890272
  have htrace : WordTrace (prefixWord ++ tailWord_890272) baseStart_890272 baseEnd_890272 := by
    simpa [prefixWord, tailWord_890272, baseEnd_890272] using wordTrace_append hprefix tailTrace_890272
  have hstable : (prefixWord ++ tailWord_890272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890272).length < 2 ^ (prefixWord ++ tailWord_890272).sum := by decide
  have hdescent : baseEnd_890272 < baseStart_890272 := by decide
  rcases family_descends (prefixWord ++ tailWord_890272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890276 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 8]
def baseStart_890276 : Nat := 118140960795 + 890276 * 2 ^ 59
def prefixEnd_890276 : Nat := 4983230072969 + 3 ^ 40 * 890276 * 2
def baseEnd_890276 : Nat := 406346225033123577560623

theorem tailTrace_890276 : CollatzResearch.WordTrace tailWord_890276 prefixEnd_890276 406346225033123577560623 := by
  unfold tailWord_890276
  simp only [CollatzResearch.WordTrace]
  refine ⟨16235516661344786940413341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21647355548459715920551121 16235516661344786940413341)
  ·
    refine ⟨6088318748004295102655003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16235516661344786940413341 6088318748004295102655003)
    ·
      refine ⟨9132478122006442653982505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6088318748004295102655003 9132478122006442653982505)
      ·
        refine ⟨6849358591504831990486879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9132478122006442653982505 6849358591504831990486879)
        ·
          refine ⟨10274037887257247985730319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6849358591504831990486879 10274037887257247985730319)
          ·
            refine ⟨15411056830885871978595479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10274037887257247985730319 15411056830885871978595479)
            ·
              refine ⟨23116585246328807967893219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15411056830885871978595479 23116585246328807967893219)
              ·
                refine ⟨34674877869493211951839829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23116585246328807967893219 34674877869493211951839829)
                ·
                  refine ⟨406346225033123577560623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34674877869493211951839829 406346225033123577560623)
                  ·
                    rfl

theorem cell20_890276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_890276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890276 prefixEnd_890276 := by exact prefixLift 890276
  have htrace : WordTrace (prefixWord ++ tailWord_890276) baseStart_890276 baseEnd_890276 := by
    simpa [prefixWord, tailWord_890276, baseEnd_890276] using wordTrace_append hprefix tailTrace_890276
  have hstable : (prefixWord ++ tailWord_890276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890276).length < 2 ^ (prefixWord ++ tailWord_890276).sum := by decide
  have hdescent : baseEnd_890276 < baseStart_890276 := by decide
  rcases family_descends (prefixWord ++ tailWord_890276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890293 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 4]
def baseStart_890293 : Nat := 118140960795 + 890293 * 2 ^ 59
def prefixEnd_890293 : Nat := 4983230072969 + 3 ^ 40 * 890293 * 2
def baseEnd_890293 : Nat := 406353984296347073993887

theorem tailTrace_890293 : CollatzResearch.WordTrace tailWord_890293 prefixEnd_890293 406353984296347073993887 := by
  unfold tailWord_890293
  simp only [CollatzResearch.WordTrace]
  refine ⟨32471653363627985784195533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21647768909085323856130355 32471653363627985784195533)
  ·
    refine ⟨12176870011360494669073325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32471653363627985784195533 12176870011360494669073325)
    ·
      refine ⟨4566326254260185500902497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12176870011360494669073325 4566326254260185500902497)
      ·
        refine ⟨3424744690695139125676873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4566326254260185500902497 3424744690695139125676873)
        ·
          refine ⟨2568558518021354344257655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3424744690695139125676873 2568558518021354344257655)
          ·
            refine ⟨3852837777032031516386483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2568558518021354344257655 3852837777032031516386483)
            ·
              refine ⟨5779256665548047274579725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3852837777032031516386483 5779256665548047274579725)
              ·
                refine ⟨2167221249580517727967397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5779256665548047274579725 2167221249580517727967397)
                ·
                  refine ⟨406353984296347073993887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2167221249580517727967397 406353984296347073993887)
                  ·
                    rfl

theorem cell20_890293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_890293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890293 prefixEnd_890293 := by exact prefixLift 890293
  have htrace : WordTrace (prefixWord ++ tailWord_890293) baseStart_890293 baseEnd_890293 := by
    simpa [prefixWord, tailWord_890293, baseEnd_890293] using wordTrace_append hprefix tailTrace_890293
  have hstable : (prefixWord ++ tailWord_890293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890293).length < 2 ^ (prefixWord ++ tailWord_890293).sum := by decide
  have hdescent : baseEnd_890293 < baseStart_890293 := by decide
  rcases family_descends (prefixWord ++ tailWord_890293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890307 : List Nat := [1, 1, 1, 3, 1, 1, 4, 5, 3]
def baseStart_890307 : Nat := 118140960795 + 890307 * 2 ^ 59
def prefixEnd_890307 : Nat := 4983230072969 + 3 ^ 40 * 890307 * 2
def baseEnd_890307 : Nat := 406360374277825247527163

theorem tailTrace_890307 : CollatzResearch.WordTrace tailWord_890307 prefixEnd_890307 406360374277825247527163 := by
  unfold tailWord_890307
  simp only [CollatzResearch.WordTrace]
  refine ⟨32472163985577266175205175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21648109323718177450136783 32472163985577266175205175)
  ·
    refine ⟨48708245978365899262807763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32472163985577266175205175 48708245978365899262807763)
    ·
      refine ⟨73062368967548848894211645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48708245978365899262807763 73062368967548848894211645)
      ·
        refine ⟨27398388362830818335329367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73062368967548848894211645 27398388362830818335329367)
        ·
          refine ⟨41097582544246227502994051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27398388362830818335329367 41097582544246227502994051)
          ·
            refine ⟨61646373816369341254491077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41097582544246227502994051 61646373816369341254491077)
            ·
              refine ⟨11558695090569251485217077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61646373816369341254491077 11558695090569251485217077)
              ·
                refine ⟨1083627664740867326739101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11558695090569251485217077 1083627664740867326739101)
                ·
                  refine ⟨406360374277825247527163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083627664740867326739101 406360374277825247527163)
                  ·
                    rfl

theorem cell20_890307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 3].length) (baseStart_890307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890307 prefixEnd_890307 := by exact prefixLift 890307
  have htrace : WordTrace (prefixWord ++ tailWord_890307) baseStart_890307 baseEnd_890307 := by
    simpa [prefixWord, tailWord_890307, baseEnd_890307] using wordTrace_append hprefix tailTrace_890307
  have hstable : (prefixWord ++ tailWord_890307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890307).length < 2 ^ (prefixWord ++ tailWord_890307).sum := by decide
  have hdescent : baseEnd_890307 < baseStart_890307 := by decide
  rcases family_descends (prefixWord ++ tailWord_890307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890358 : List Nat := [5, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_890358 : Nat := 118140960795 + 890358 * 2 ^ 59
def prefixEnd_890358 : Nat := 4983230072969 + 3 ^ 40 * 890358 * 2
def baseEnd_890358 : Nat := 406383652067495736826955

theorem tailTrace_890358 : CollatzResearch.WordTrace tailWord_890358 prefixEnd_890358 406383652067495736826955 := by
  unfold tailWord_890358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2029626506774531367831983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21649349405595001256874485 2029626506774531367831983)
  ·
    refine ⟨3044439760161797051747975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2029626506774531367831983 3044439760161797051747975)
    ·
      refine ⟨4566659640242695577621963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3044439760161797051747975 4566659640242695577621963)
      ·
        refine ⟨6849989460364043366432945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4566659640242695577621963 6849989460364043366432945)
        ·
          refine ⟨5137492095273032524824709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6849989460364043366432945 5137492095273032524824709)
          ·
            refine ⟨963279767863693598404633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5137492095273032524824709 963279767863693598404633)
            ·
              refine ⟨722459825897770198803475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963279767863693598404633 722459825897770198803475)
              ·
                refine ⟨1083689738846655298205213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722459825897770198803475 1083689738846655298205213)
                ·
                  refine ⟨406383652067495736826955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083689738846655298205213 406383652067495736826955)
                  ·
                    rfl

theorem cell20_890358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_890358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890358 prefixEnd_890358 := by exact prefixLift 890358
  have htrace : WordTrace (prefixWord ++ tailWord_890358) baseStart_890358 baseEnd_890358 := by
    simpa [prefixWord, tailWord_890358, baseEnd_890358] using wordTrace_append hprefix tailTrace_890358
  have hstable : (prefixWord ++ tailWord_890358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890358).length < 2 ^ (prefixWord ++ tailWord_890358).sum := by decide
  have hdescent : baseEnd_890358 < baseStart_890358 := by decide
  rcases family_descends (prefixWord ++ tailWord_890358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890400 : List Nat := [2, 1, 1, 6, 1, 1, 1, 4, 3]
def baseStart_890400 : Nat := 118140960795 + 890400 * 2 ^ 59
def prefixEnd_890400 : Nat := 4983230072969 + 3 ^ 40 * 890400 * 2
def baseEnd_890400 : Nat := 406402822011930257426783

theorem tailTrace_890400 : CollatzResearch.WordTrace tailWord_890400 prefixEnd_890400 406402822011930257426783 := by
  unfold tailWord_890400
  simp only [CollatzResearch.WordTrace]
  refine ⟨16237777987120171529170327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21650370649493562038893769 16237777987120171529170327)
  ·
    refine ⟨24356666980680257293755491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16237777987120171529170327 24356666980680257293755491)
    ·
      refine ⟨36535000471020385940633237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24356666980680257293755491 36535000471020385940633237)
      ·
        refine ⟨1712578147079080590967183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36535000471020385940633237 1712578147079080590967183)
        ·
          refine ⟨2568867220618620886450775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1712578147079080590967183 2568867220618620886450775)
          ·
            refine ⟨3853300830927931329676163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2568867220618620886450775 3853300830927931329676163)
            ·
              refine ⟨5779951246391896994514245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3853300830927931329676163 5779951246391896994514245)
              ·
                refine ⟨1083740858698480686471421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5779951246391896994514245 1083740858698480686471421)
                ·
                  refine ⟨406402822011930257426783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083740858698480686471421 406402822011930257426783)
                  ·
                    rfl

theorem cell20_890400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_890400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890400 prefixEnd_890400 := by exact prefixLift 890400
  have htrace : WordTrace (prefixWord ++ tailWord_890400) baseStart_890400 baseEnd_890400 := by
    simpa [prefixWord, tailWord_890400, baseEnd_890400] using wordTrace_append hprefix tailTrace_890400
  have hstable : (prefixWord ++ tailWord_890400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890400).length < 2 ^ (prefixWord ++ tailWord_890400).sum := by decide
  have hdescent : baseEnd_890400 < baseStart_890400 := by decide
  rcases family_descends (prefixWord ++ tailWord_890400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890486 : List Nat := [5, 1, 1, 2, 2, 3, 2, 4]
def baseStart_890486 : Nat := 118140960795 + 890486 * 2 ^ 59
def prefixEnd_890486 : Nat := 4983230072969 + 3 ^ 40 * 890486 * 2
def baseEnd_890486 : Nat := 135480691585098726853255

theorem tailTrace_890486 : CollatzResearch.WordTrace tailWord_890486 prefixEnd_890486 135480691585098726853255 := by
  unfold tailWord_890486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2029918290745548734123207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21652461767952519830647541 2029918290745548734123207)
  ·
    refine ⟨3044877436118323101184811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2029918290745548734123207 3044877436118323101184811)
    ·
      refine ⟨4567316154177484651777217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3044877436118323101184811 4567316154177484651777217)
      ·
        refine ⟨3425487115633113488832913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4567316154177484651777217 3425487115633113488832913)
        ·
          refine ⟨2569115336724835116624685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3425487115633113488832913 2569115336724835116624685)
          ·
            refine ⟨963418251271813168734257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2569115336724835116624685 963418251271813168734257)
            ·
              refine ⟨722563688453859876550693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963418251271813168734257 722563688453859876550693)
              ·
                refine ⟨135480691585098726853255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 722563688453859876550693 135480691585098726853255)
                ·
                  rfl

theorem cell20_890486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_890486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890486 prefixEnd_890486 := by exact prefixLift 890486
  have htrace : WordTrace (prefixWord ++ tailWord_890486) baseStart_890486 baseEnd_890486 := by
    simpa [prefixWord, tailWord_890486, baseEnd_890486] using wordTrace_append hprefix tailTrace_890486
  have hstable : (prefixWord ++ tailWord_890486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890486).length < 2 ^ (prefixWord ++ tailWord_890486).sum := by decide
  have hdescent : baseEnd_890486 < baseStart_890486 := by decide
  rcases family_descends (prefixWord ++ tailWord_890486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890497 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 5]
def baseStart_890497 : Nat := 118140960795 + 890497 * 2 ^ 59
def prefixEnd_890497 : Nat := 4983230072969 + 3 ^ 40 * 890497 * 2
def baseEnd_890497 : Nat := 406447095455029031193053

theorem tailTrace_890497 : CollatzResearch.WordTrace tailWord_890497 prefixEnd_890497 406447095455029031193053 := by
  unfold tailWord_890497
  simp only [CollatzResearch.WordTrace]
  refine ⟨32479093854888928624621745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21652729236592619083081163 32479093854888928624621745)
  ·
    refine ⟨24359320391166696468466309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32479093854888928624621745 24359320391166696468466309)
    ·
      refine ⟨4567372573343755587837433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24359320391166696468466309 4567372573343755587837433)
      ·
        refine ⟨3425529430007816690878075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4567372573343755587837433 3425529430007816690878075)
        ·
          refine ⟨5138294145011725036317113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3425529430007816690878075 5138294145011725036317113)
          ·
            refine ⟨3853720608758793777237835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5138294145011725036317113 3853720608758793777237835)
            ·
              refine ⟨5780580913138190665856753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3853720608758793777237835 5780580913138190665856753)
              ·
                refine ⟨4335435684853642999392565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5780580913138190665856753 4335435684853642999392565)
                ·
                  refine ⟨406447095455029031193053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4335435684853642999392565 406447095455029031193053)
                  ·
                    rfl

theorem cell20_890497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_890497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890497 prefixEnd_890497 := by exact prefixLift 890497
  have htrace : WordTrace (prefixWord ++ tailWord_890497) baseStart_890497 baseEnd_890497 := by
    simpa [prefixWord, tailWord_890497, baseEnd_890497] using wordTrace_append hprefix tailTrace_890497
  have hstable : (prefixWord ++ tailWord_890497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890497).length < 2 ^ (prefixWord ++ tailWord_890497).sum := by decide
  have hdescent : baseEnd_890497 < baseStart_890497 := by decide
  rcases family_descends (prefixWord ++ tailWord_890497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890527 : List Nat := [1, 1, 2, 7, 2, 1, 2, 1, 3]
def baseStart_890527 : Nat := 118140960795 + 890527 * 2 ^ 59
def prefixEnd_890527 : Nat := 4983230072969 + 3 ^ 40 * 890527 * 2
def baseEnd_890527 : Nat := 406460788272482260192931

theorem tailTrace_890527 : CollatzResearch.WordTrace tailWord_890527 prefixEnd_890527 406460788272482260192931 := by
  unfold tailWord_890527
  simp only [CollatzResearch.WordTrace]
  refine ⟨32480188044780243748213835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21653458696520162498809223 32480188044780243748213835)
  ·
    refine ⟨48720282067170365622320753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32480188044780243748213835 48720282067170365622320753)
    ·
      refine ⟨36540211550377774216740565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48720282067170365622320753 36540211550377774216740565)
      ·
        refine ⟨856411208211979083204857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 36540211550377774216740565 856411208211979083204857)
        ·
          refine ⟨642308406158984312403643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 856411208211979083204857 642308406158984312403643)
          ·
            refine ⟨963462609238476468605465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642308406158984312403643 963462609238476468605465)
            ·
              refine ⟨722596956928857351454099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963462609238476468605465 722596956928857351454099)
              ·
                refine ⟨1083895435393286027181149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722596956928857351454099 1083895435393286027181149)
                ·
                  refine ⟨406460788272482260192931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083895435393286027181149 406460788272482260192931)
                  ·
                    rfl

theorem cell20_890527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 3].length) (baseStart_890527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890527 prefixEnd_890527 := by exact prefixLift 890527
  have htrace : WordTrace (prefixWord ++ tailWord_890527) baseStart_890527 baseEnd_890527 := by
    simpa [prefixWord, tailWord_890527, baseEnd_890527] using wordTrace_append hprefix tailTrace_890527
  have hstable : (prefixWord ++ tailWord_890527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890527).length < 2 ^ (prefixWord ++ tailWord_890527).sum := by decide
  have hdescent : baseEnd_890527 < baseStart_890527 := by decide
  rcases family_descends (prefixWord ++ tailWord_890527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890528 : List Nat := [2, 1, 1, 4, 3, 2, 2, 5]
def baseStart_890528 : Nat := 118140960795 + 890528 * 2 ^ 59
def prefixEnd_890528 : Nat := 4983230072969 + 3 ^ 40 * 890528 * 2
def baseEnd_890528 : Nat := 135487081566576900386531

theorem tailTrace_890528 : CollatzResearch.WordTrace tailWord_890528 prefixEnd_890528 135487081566576900386531 := by
  unfold tailWord_890528
  simp only [CollatzResearch.WordTrace]
  refine ⟨16240112258888310459500119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21653483011851080612666825 16240112258888310459500119)
  ·
    refine ⟨24360168388332465689250179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16240112258888310459500119 24360168388332465689250179)
    ·
      refine ⟨36540252582498698533875269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24360168388332465689250179 36540252582498698533875269)
      ·
        refine ⟨6851297359218505975101613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36540252582498698533875269 6851297359218505975101613)
        ·
          refine ⟨2569236509706939740663105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6851297359218505975101613 2569236509706939740663105)
          ·
            refine ⟨1926927382280204805497329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2569236509706939740663105 1926927382280204805497329)
            ·
              refine ⟨1445195536710153604122997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1926927382280204805497329 1445195536710153604122997)
              ·
                refine ⟨135487081566576900386531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1445195536710153604122997 135487081566576900386531)
                ·
                  rfl

theorem cell20_890528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_890528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890528 prefixEnd_890528 := by exact prefixLift 890528
  have htrace : WordTrace (prefixWord ++ tailWord_890528) baseStart_890528 baseEnd_890528 := by
    simpa [prefixWord, tailWord_890528, baseEnd_890528] using wordTrace_append hprefix tailTrace_890528
  have hstable : (prefixWord ++ tailWord_890528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890528).length < 2 ^ (prefixWord ++ tailWord_890528).sum := by decide
  have hdescent : baseEnd_890528 < baseStart_890528 := by decide
  rcases family_descends (prefixWord ++ tailWord_890528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890559 : List Nat := [1, 1, 2, 2, 2, 3, 2, 5, 2]
def baseStart_890559 : Nat := 118140960795 + 890559 * 2 ^ 59
def prefixEnd_890559 : Nat := 4983230072969 + 3 ^ 40 * 890559 * 2
def baseEnd_890559 : Nat := 406475393944432371126133

theorem tailTrace_890559 : CollatzResearch.WordTrace tailWord_890559 prefixEnd_890559 406475393944432371126133 := by
  unfold tailWord_890559
  simp only [CollatzResearch.WordTrace]
  refine ⟨32481355180664313213378731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21654236787109542142252487 32481355180664313213378731)
  ·
    refine ⟨48722032770996469820068097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32481355180664313213378731 48722032770996469820068097)
    ·
      refine ⟨36541524578247352365051073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48722032770996469820068097 36541524578247352365051073)
      ·
        refine ⟨27406143433685514273788305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36541524578247352365051073 27406143433685514273788305)
        ·
          refine ⟨20554607575264135705341229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27406143433685514273788305 20554607575264135705341229)
          ·
            refine ⟨7707977840724050889502961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20554607575264135705341229 7707977840724050889502961)
            ·
              refine ⟨5780983380543038167127221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7707977840724050889502961 5780983380543038167127221)
              ·
                refine ⟨541967191925909828168177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5780983380543038167127221 541967191925909828168177)
                ·
                  refine ⟨406475393944432371126133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541967191925909828168177 406475393944432371126133)
                  ·
                    rfl

theorem cell20_890559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 2].length) (baseStart_890559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890559 prefixEnd_890559 := by exact prefixLift 890559
  have htrace : WordTrace (prefixWord ++ tailWord_890559) baseStart_890559 baseEnd_890559 := by
    simpa [prefixWord, tailWord_890559, baseEnd_890559] using wordTrace_append hprefix tailTrace_890559
  have hstable : (prefixWord ++ tailWord_890559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890559).length < 2 ^ (prefixWord ++ tailWord_890559).sum := by decide
  have hdescent : baseEnd_890559 < baseStart_890559 := by decide
  rcases family_descends (prefixWord ++ tailWord_890559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890562 : List Nat := [3, 5, 1, 2, 1, 8]
def baseStart_890562 : Nat := 118140960795 + 890562 * 2 ^ 59
def prefixEnd_890562 : Nat := 4983230072969 + 3 ^ 40 * 890562 * 2
def baseEnd_890562 : Nat := 15054694934302877556523

theorem tailTrace_890562 : CollatzResearch.WordTrace tailWord_890562 prefixEnd_890562 15054694934302877556523 := by
  unfold tailWord_890562
  simp only [CollatzResearch.WordTrace]
  refine ⟨8120366149913361181434485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21654309733102296483825293 8120366149913361181434485)
  ·
    refine ⟨761284326554377610759483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8120366149913361181434485 761284326554377610759483)
    ·
      refine ⟨1141926489831566416139225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 761284326554377610759483 1141926489831566416139225)
      ·
        refine ⟨856444867373674812104419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1141926489831566416139225 856444867373674812104419)
        ·
          refine ⟨1284667301060512218156629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856444867373674812104419 1284667301060512218156629)
          ·
            refine ⟨15054694934302877556523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1284667301060512218156629 15054694934302877556523)
            ·
              rfl

theorem cell20_890562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 8].length) (baseStart_890562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890562 prefixEnd_890562 := by exact prefixLift 890562
  have htrace : WordTrace (prefixWord ++ tailWord_890562) baseStart_890562 baseEnd_890562 := by
    simpa [prefixWord, tailWord_890562, baseEnd_890562] using wordTrace_append hprefix tailTrace_890562
  have hstable : (prefixWord ++ tailWord_890562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890562).length < 2 ^ (prefixWord ++ tailWord_890562).sum := by decide
  have hdescent : baseEnd_890562 < baseStart_890562 := by decide
  rcases family_descends (prefixWord ++ tailWord_890562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890572 : List Nat := [2, 2, 1, 5, 2, 2, 2, 2, 2]
def baseStart_890572 : Nat := 118140960795 + 890572 * 2 ^ 59
def prefixEnd_890572 : Nat := 4983230072969 + 3 ^ 40 * 890572 * 2
def baseEnd_890572 : Nat := 406481327498662103692747

theorem tailTrace_890572 : CollatzResearch.WordTrace tailWord_890572 prefixEnd_890572 406481327498662103692747 := by
  unfold tailWord_890572
  simp only [CollatzResearch.WordTrace]
  refine ⟨16240914664808608216800985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21654552886411477622401313 16240914664808608216800985)
  ·
    refine ⟨12180685998606456162600739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16240914664808608216800985 12180685998606456162600739)
    ·
      refine ⟨18271028997909684243901109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12180685998606456162600739 18271028997909684243901109)
      ·
        refine ⟨1712908968554032897865729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18271028997909684243901109 1712908968554032897865729)
        ·
          refine ⟨1284681726415524673399297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1712908968554032897865729 1284681726415524673399297)
          ·
            refine ⟨963511294811643505049473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1284681726415524673399297 963511294811643505049473)
            ·
              refine ⟨722633471108732628787105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963511294811643505049473 722633471108732628787105)
              ·
                refine ⟨541975103331549471590329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 722633471108732628787105 541975103331549471590329)
                ·
                  refine ⟨406481327498662103692747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541975103331549471590329 406481327498662103692747)
                  ·
                    rfl

theorem cell20_890572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_890572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890572 prefixEnd_890572 := by exact prefixLift 890572
  have htrace : WordTrace (prefixWord ++ tailWord_890572) baseStart_890572 baseEnd_890572 := by
    simpa [prefixWord, tailWord_890572, baseEnd_890572] using wordTrace_append hprefix tailTrace_890572
  have hstable : (prefixWord ++ tailWord_890572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890572).length < 2 ^ (prefixWord ++ tailWord_890572).sum := by decide
  have hdescent : baseEnd_890572 < baseStart_890572 := by decide
  rcases family_descends (prefixWord ++ tailWord_890572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890614 : List Nat := [5, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_890614 : Nat := 118140960795 + 890614 * 2 ^ 59
def prefixEnd_890614 : Nat := 4983230072969 + 3 ^ 40 * 890614 * 2
def baseEnd_890614 : Nat := 406500497443096624292575

theorem tailTrace_890614 : CollatzResearch.WordTrace tailWord_890614 prefixEnd_890614 406500497443096624292575 := by
  unfold tailWord_890614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030210074716566100414431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21655574130310038404420597 2030210074716566100414431)
  ·
    refine ⟨3045315112074849150621647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2030210074716566100414431 3045315112074849150621647)
    ·
      refine ⟨4567972668112273725932471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3045315112074849150621647 4567972668112273725932471)
      ·
        refine ⟨6851959002168410588898707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4567972668112273725932471 6851959002168410588898707)
        ·
          refine ⟨10277938503252615883348061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6851959002168410588898707 10277938503252615883348061)
          ·
            refine ⟨3854226938719730956255523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10277938503252615883348061 3854226938719730956255523)
            ·
              refine ⟨5781340408079596434383285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3854226938719730956255523 5781340408079596434383285)
              ·
                refine ⟨542000663257462165723433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5781340408079596434383285 542000663257462165723433)
                ·
                  refine ⟨406500497443096624292575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542000663257462165723433 406500497443096624292575)
                  ·
                    rfl

theorem cell20_890614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_890614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890614 prefixEnd_890614 := by exact prefixLift 890614
  have htrace : WordTrace (prefixWord ++ tailWord_890614) baseStart_890614 baseEnd_890614 := by
    simpa [prefixWord, tailWord_890614, baseEnd_890614] using wordTrace_append hprefix tailTrace_890614
  have hstable : (prefixWord ++ tailWord_890614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890614).length < 2 ^ (prefixWord ++ tailWord_890614).sum := by decide
  have hdescent : baseEnd_890614 < baseStart_890614 := by decide
  rcases family_descends (prefixWord ++ tailWord_890614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890628 : List Nat := [2, 3, 2, 2, 1, 2, 3, 2, 3]
def baseStart_890628 : Nat := 118140960795 + 890628 * 2 ^ 59
def prefixEnd_890628 : Nat := 4983230072969 + 3 ^ 40 * 890628 * 2
def baseEnd_890628 : Nat := 406506887424574797825851

theorem tailTrace_890628 : CollatzResearch.WordTrace tailWord_890628 prefixEnd_890628 406506887424574797825851 := by
  unfold tailWord_890628
  simp only [CollatzResearch.WordTrace]
  refine ⟨16241935908707168998820269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21655914544942891998427025 16241935908707168998820269)
  ·
    refine ⟨6090725965765188374557601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16241935908707168998820269 6090725965765188374557601)
    ·
      refine ⟨4568044474323891280918201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6090725965765188374557601 4568044474323891280918201)
      ·
        refine ⟨3426033355742918460688651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4568044474323891280918201 3426033355742918460688651)
        ·
          refine ⟨5139050033614377691032977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3426033355742918460688651 5139050033614377691032977)
          ·
            refine ⟨3854287525210783268274733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5139050033614377691032977 3854287525210783268274733)
            ·
              refine ⟨1445357821954043725603025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3854287525210783268274733 1445357821954043725603025)
              ·
                refine ⟨1084018366465532794202269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1445357821954043725603025 1084018366465532794202269)
                ·
                  refine ⟨406506887424574797825851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1084018366465532794202269 406506887424574797825851)
                  ·
                    rfl

theorem cell20_890628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_890628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890628 prefixEnd_890628 := by exact prefixLift 890628
  have htrace : WordTrace (prefixWord ++ tailWord_890628) baseStart_890628 baseEnd_890628 := by
    simpa [prefixWord, tailWord_890628, baseEnd_890628] using wordTrace_append hprefix tailTrace_890628
  have hstable : (prefixWord ++ tailWord_890628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890628).length < 2 ^ (prefixWord ++ tailWord_890628).sum := by decide
  have hdescent : baseEnd_890628 < baseStart_890628 := by decide
  rcases family_descends (prefixWord ++ tailWord_890628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890635 : List Nat := [1, 1, 1, 1, 5, 1, 4, 4, 2]
def baseStart_890635 : Nat := 118140960795 + 890635 * 2 ^ 59
def prefixEnd_890635 : Nat := 4983230072969 + 3 ^ 40 * 890635 * 2
def baseEnd_890635 : Nat := 406510082415313884592489

theorem tailTrace_890635 : CollatzResearch.WordTrace tailWord_890635 prefixEnd_890635 406510082415313884592489 := by
  unfold tailWord_890635
  simp only [CollatzResearch.WordTrace]
  refine ⟨32484127128388978193145359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21656084752259318795430239 32484127128388978193145359)
  ·
    refine ⟨48726190692583467289718039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32484127128388978193145359 48726190692583467289718039)
    ·
      refine ⟨73089286038875200934577059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48726190692583467289718039 73089286038875200934577059)
      ·
        refine ⟨109633929058312801401865589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73089286038875200934577059 109633929058312801401865589)
        ·
          refine ⟨10278180849216825131424899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109633929058312801401865589 10278180849216825131424899)
          ·
            refine ⟨15417271273825237697137349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10278180849216825131424899 15417271273825237697137349)
            ·
              refine ⟨2890738363842232068213253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15417271273825237697137349 2890738363842232068213253)
              ·
                refine ⟨542013443220418512789985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2890738363842232068213253 542013443220418512789985)
                ·
                  refine ⟨406510082415313884592489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542013443220418512789985 406510082415313884592489)
                  ·
                    rfl

theorem cell20_890635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 2].length) (baseStart_890635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890635 prefixEnd_890635 := by exact prefixLift 890635
  have htrace : WordTrace (prefixWord ++ tailWord_890635) baseStart_890635 baseEnd_890635 := by
    simpa [prefixWord, tailWord_890635, baseEnd_890635] using wordTrace_append hprefix tailTrace_890635
  have hstable : (prefixWord ++ tailWord_890635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890635).length < 2 ^ (prefixWord ++ tailWord_890635).sum := by decide
  have hdescent : baseEnd_890635 < baseStart_890635 := by decide
  rcases family_descends (prefixWord ++ tailWord_890635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890656 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 4]
def baseStart_890656 : Nat := 118140960795 + 890656 * 2 ^ 59
def prefixEnd_890656 : Nat := 4983230072969 + 3 ^ 40 * 890656 * 2
def baseEnd_890656 : Nat := 406519667387531144892403

theorem tailTrace_890656 : CollatzResearch.WordTrace tailWord_890656 prefixEnd_890656 406519667387531144892403 := by
  unfold tailWord_890656
  simp only [CollatzResearch.WordTrace]
  refine ⟨16242446530656449389829911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21656595374208599186439881 16242446530656449389829911)
  ·
    refine ⟨24363669795984674084744867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16242446530656449389829911 24363669795984674084744867)
    ·
      refine ⟨36545504693977011127117301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24363669795984674084744867 36545504693977011127117301)
      ·
        refine ⟨3426141065060344793167247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36545504693977011127117301 3426141065060344793167247)
        ·
          refine ⟨5139211597590517189750871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3426141065060344793167247 5139211597590517189750871)
          ·
            refine ⟨7708817396385775784626307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5139211597590517189750871 7708817396385775784626307)
            ·
              refine ⟨11563226094578663676939461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7708817396385775784626307 11563226094578663676939461)
              ·
                refine ⟨2168104892733499439426149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11563226094578663676939461 2168104892733499439426149)
                ·
                  refine ⟨406519667387531144892403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2168104892733499439426149 406519667387531144892403)
                  ·
                    rfl

theorem cell20_890656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_890656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890656 prefixEnd_890656 := by exact prefixLift 890656
  have htrace : WordTrace (prefixWord ++ tailWord_890656) baseStart_890656 baseEnd_890656 := by
    simpa [prefixWord, tailWord_890656, baseEnd_890656] using wordTrace_append hprefix tailTrace_890656
  have hstable : (prefixWord ++ tailWord_890656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890656).length < 2 ^ (prefixWord ++ tailWord_890656).sum := by decide
  have hdescent : baseEnd_890656 < baseStart_890656 := by decide
  rcases family_descends (prefixWord ++ tailWord_890656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890700 : List Nat := [2, 2, 1, 3, 5, 1, 2, 1, 3]
def baseStart_890700 : Nat := 118140960795 + 890700 * 2 ^ 59
def prefixEnd_890700 : Nat := 4983230072969 + 3 ^ 40 * 890700 * 2
def baseEnd_890700 : Nat := 406539750186462547425557

theorem tailTrace_890700 : CollatzResearch.WordTrace tailWord_890700 prefixEnd_890700 406539750186462547425557 := by
  unfold tailWord_890700
  simp only [CollatzResearch.WordTrace]
  refine ⟨16243248936576747147130777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21657665248768996196174369 16243248936576747147130777)
  ·
    refine ⟨12182436702432560360348083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16243248936576747147130777 12182436702432560360348083)
    ·
      refine ⟨18273655053648840540522125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12182436702432560360348083 18273655053648840540522125)
      ·
        refine ⟨6852620645118315202695797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18273655053648840540522125 6852620645118315202695797)
        ·
          refine ⟨642433185479842050252731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6852620645118315202695797 642433185479842050252731)
          ·
            refine ⟨963649778219763075379097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642433185479842050252731 963649778219763075379097)
            ·
              refine ⟨722737333664822306534323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963649778219763075379097 722737333664822306534323)
              ·
                refine ⟨1084106000497233459801485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722737333664822306534323 1084106000497233459801485)
                ·
                  refine ⟨406539750186462547425557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1084106000497233459801485 406539750186462547425557)
                  ·
                    rfl

theorem cell20_890700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_890700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890700 prefixEnd_890700 := by exact prefixLift 890700
  have htrace : WordTrace (prefixWord ++ tailWord_890700) baseStart_890700 baseEnd_890700 := by
    simpa [prefixWord, tailWord_890700, baseEnd_890700] using wordTrace_append hprefix tailTrace_890700
  have hstable : (prefixWord ++ tailWord_890700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890700).length < 2 ^ (prefixWord ++ tailWord_890700).sum := by decide
  have hdescent : baseEnd_890700 < baseStart_890700 := by decide
  rcases family_descends (prefixWord ++ tailWord_890700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890746 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_890746 : Nat := 118140960795 + 890746 * 2 ^ 59
def prefixEnd_890746 : Nat := 4983230072969 + 3 ^ 40 * 890746 * 2
def baseEnd_890746 : Nat := 406560745839890831892035

theorem tailTrace_890746 : CollatzResearch.WordTrace tailWord_890746 prefixEnd_890746 406560745839890831892035 := by
  unfold tailWord_890746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8122043907746711037609023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21658783753991229433624061 8122043907746711037609023)
  ·
    refine ⟨12183065861620066556413535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8122043907746711037609023 12183065861620066556413535)
    ·
      refine ⟨18274598792430099834620303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12183065861620066556413535 18274598792430099834620303)
      ·
        refine ⟨27411898188645149751930455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18274598792430099834620303 27411898188645149751930455)
        ·
          refine ⟨41117847282967724627895683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27411898188645149751930455 41117847282967724627895683)
          ·
            refine ⟨61676770924451586941843525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41117847282967724627895683 61676770924451586941843525)
            ·
              refine ⟨11564394548334672551595661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61676770924451586941843525 11564394548334672551595661)
              ·
                refine ⟨4336647955625502206848373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11564394548334672551595661 4336647955625502206848373)
                ·
                  refine ⟨406560745839890831892035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4336647955625502206848373 406560745839890831892035)
                  ·
                    rfl

theorem cell20_890746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_890746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890746 prefixEnd_890746 := by exact prefixLift 890746
  have htrace : WordTrace (prefixWord ++ tailWord_890746) baseStart_890746 baseEnd_890746 := by
    simpa [prefixWord, tailWord_890746, baseEnd_890746] using wordTrace_append hprefix tailTrace_890746
  have hstable : (prefixWord ++ tailWord_890746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890746).length < 2 ^ (prefixWord ++ tailWord_890746).sum := by decide
  have hdescent : baseEnd_890746 < baseStart_890746 := by decide
  rcases family_descends (prefixWord ++ tailWord_890746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890766 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_890766 : Nat := 118140960795 + 890766 * 2 ^ 59
def prefixEnd_890766 : Nat := 4983230072969 + 3 ^ 40 * 890766 * 2
def baseEnd_890766 : Nat := 406569874384859651225287

theorem tailTrace_890766 : CollatzResearch.WordTrace tailWord_890766 prefixEnd_890766 406569874384859651225287 := by
  unfold tailWord_890766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4061113136364298445770519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21659270060609591710776101 4061113136364298445770519)
  ·
    refine ⟨6091669704546447668655779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4061113136364298445770519 6091669704546447668655779)
    ·
      refine ⟨9137504556819671502983669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6091669704546447668655779 9137504556819671502983669)
      ·
        refine ⟨856641052201844203404719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9137504556819671502983669 856641052201844203404719)
        ·
          refine ⟨1284961578302766305107079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856641052201844203404719 1284961578302766305107079)
          ·
            refine ⟨1927442367454149457660619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284961578302766305107079 1927442367454149457660619)
            ·
              refine ⟨2891163551181224186490929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927442367454149457660619 2891163551181224186490929)
              ·
                refine ⟨2168372663385918139868197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2891163551181224186490929 2168372663385918139868197)
                ·
                  refine ⟨406569874384859651225287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2168372663385918139868197 406569874384859651225287)
                  ·
                    rfl

theorem cell20_890766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_890766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890766 prefixEnd_890766 := by exact prefixLift 890766
  have htrace : WordTrace (prefixWord ++ tailWord_890766) baseStart_890766 baseEnd_890766 := by
    simpa [prefixWord, tailWord_890766, baseEnd_890766] using wordTrace_append hprefix tailTrace_890766
  have hstable : (prefixWord ++ tailWord_890766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890766).length < 2 ^ (prefixWord ++ tailWord_890766).sum := by decide
  have hdescent : baseEnd_890766 < baseStart_890766 := by decide
  rcases family_descends (prefixWord ++ tailWord_890766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890784 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 5]
def baseStart_890784 : Nat := 118140960795 + 890784 * 2 ^ 59
def prefixEnd_890784 : Nat := 4983230072969 + 3 ^ 40 * 890784 * 2
def baseEnd_890784 : Nat := 406578090075331588625213

theorem tailTrace_890784 : CollatzResearch.WordTrace tailWord_890784 prefixEnd_890784 406578090075331588625213 := by
  unfold tailWord_890784
  simp only [CollatzResearch.WordTrace]
  refine ⟨16244780802424588320159703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21659707736566117760212937 16244780802424588320159703)
  ·
    refine ⟨24367171203636882480239555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16244780802424588320159703 24367171203636882480239555)
    ·
      refine ⟨36550756805455323720359333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24367171203636882480239555 36550756805455323720359333)
      ·
        refine ⟨6853266901022873197567375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36550756805455323720359333 6853266901022873197567375)
        ·
          refine ⟨10279900351534309796351063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6853266901022873197567375 10279900351534309796351063)
          ·
            refine ⟨15419850527301464694526595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10279900351534309796351063 15419850527301464694526595)
            ·
              refine ⟨23129775790952197041789893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15419850527301464694526595 23129775790952197041789893)
              ·
                refine ⟨4336832960803536945335605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23129775790952197041789893 4336832960803536945335605)
                ·
                  refine ⟨406578090075331588625213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4336832960803536945335605 406578090075331588625213)
                  ·
                    rfl

theorem cell20_890784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_890784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890784 prefixEnd_890784 := by exact prefixLift 890784
  have htrace : WordTrace (prefixWord ++ tailWord_890784) baseStart_890784 baseEnd_890784 := by
    simpa [prefixWord, tailWord_890784, baseEnd_890784] using wordTrace_append hprefix tailTrace_890784
  have hstable : (prefixWord ++ tailWord_890784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890784).length < 2 ^ (prefixWord ++ tailWord_890784).sum := by decide
  have hdescent : baseEnd_890784 < baseStart_890784 := by decide
  rcases family_descends (prefixWord ++ tailWord_890784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890801 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 5]
def baseStart_890801 : Nat := 118140960795 + 890801 * 2 ^ 59
def prefixEnd_890801 : Nat := 4983230072969 + 3 ^ 40 * 890801 * 2
def baseEnd_890801 : Nat := 406585849338555085058477

theorem tailTrace_890801 : CollatzResearch.WordTrace tailWord_890801 prefixEnd_890801 406585849338555085058477 := by
  unfold tailWord_890801
  simp only [CollatzResearch.WordTrace]
  refine ⟨32490181645787588543688257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21660121097191725695792171 32490181645787588543688257)
  ·
    refine ⟨24367636234340691407766193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32490181645787588543688257 24367636234340691407766193)
    ·
      refine ⟨18275727175755518555824645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24367636234340691407766193 18275727175755518555824645)
      ·
        refine ⟨3426698845454159729217121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18275727175755518555824645 3426698845454159729217121)
        ·
          refine ⟨2570024134090619796912841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3426698845454159729217121 2570024134090619796912841)
          ·
            refine ⟨1927518100567964847684631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2570024134090619796912841 1927518100567964847684631)
            ·
              refine ⟨2891277150851947271526947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927518100567964847684631 2891277150851947271526947)
              ·
                refine ⟨4336915726277920907290421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2891277150851947271526947 4336915726277920907290421)
                ·
                  refine ⟨406585849338555085058477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4336915726277920907290421 406585849338555085058477)
                  ·
                    rfl

theorem cell20_890801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_890801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890801 prefixEnd_890801 := by exact prefixLift 890801
  have htrace : WordTrace (prefixWord ++ tailWord_890801) baseStart_890801 baseEnd_890801 := by
    simpa [prefixWord, tailWord_890801, baseEnd_890801] using wordTrace_append hprefix tailTrace_890801
  have hstable : (prefixWord ++ tailWord_890801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890801).length < 2 ^ (prefixWord ++ tailWord_890801).sum := by decide
  have hdescent : baseEnd_890801 < baseStart_890801 := by decide
  rcases family_descends (prefixWord ++ tailWord_890801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890808 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 4]
def baseStart_890808 : Nat := 118140960795 + 890808 * 2 ^ 59
def prefixEnd_890808 : Nat := 4983230072969 + 3 ^ 40 * 890808 * 2
def baseEnd_890808 : Nat := 406589044329294171825115

theorem tailTrace_890808 : CollatzResearch.WordTrace tailWord_890808 prefixEnd_890808 406589044329294171825115 := by
  unfold tailWord_890808
  simp only [CollatzResearch.WordTrace]
  refine ⟨16245218478381114369596539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21660291304508152492795385 16245218478381114369596539)
  ·
    refine ⟨24367827717571671554394809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16245218478381114369596539 24367827717571671554394809)
    ·
      refine ⟨18275870788178753665796107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24367827717571671554394809 18275870788178753665796107)
      ·
        refine ⟨27413806182268130498694161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18275870788178753665796107 27413806182268130498694161)
        ·
          refine ⟨20560354636701097874020621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27413806182268130498694161 20560354636701097874020621)
          ·
            refine ⟨7710132988762911702757733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20560354636701097874020621 7710132988762911702757733)
            ·
              refine ⟨1445649935393045944267075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7710132988762911702757733 1445649935393045944267075)
              ·
                refine ⟨2168474903089568916400613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1445649935393045944267075 2168474903089568916400613)
                ·
                  refine ⟨406589044329294171825115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2168474903089568916400613 406589044329294171825115)
                  ·
                    rfl

theorem cell20_890808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_890808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890808 prefixEnd_890808 := by exact prefixLift 890808
  have htrace : WordTrace (prefixWord ++ tailWord_890808) baseStart_890808 baseEnd_890808 := by
    simpa [prefixWord, tailWord_890808, baseEnd_890808] using wordTrace_append hprefix tailTrace_890808
  have hstable : (prefixWord ++ tailWord_890808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890808).length < 2 ^ (prefixWord ++ tailWord_890808).sum := by decide
  have hdescent : baseEnd_890808 < baseStart_890808 := by decide
  rcases family_descends (prefixWord ++ tailWord_890808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890838 : List Nat := [5, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_890838 : Nat := 118140960795 + 890838 * 2 ^ 59
def prefixEnd_890838 : Nat := 4983230072969 + 3 ^ 40 * 890838 * 2
def baseEnd_890838 : Nat := 406602737146747400824993

theorem tailTrace_890838 : CollatzResearch.WordTrace tailWord_890838 prefixEnd_890838 406602737146747400824993 := by
  unfold tailWord_890838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030720696665846491424073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21661020764435695908523445 2030720696665846491424073)
  ·
    refine ⟨1523040522499384868568055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2030720696665846491424073 1523040522499384868568055)
    ·
      refine ⟨2284560783749077302852083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1523040522499384868568055 2284560783749077302852083)
      ·
        refine ⟨3426841175623615954278125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2284560783749077302852083 3426841175623615954278125)
        ·
          refine ⟨1285065440858855982854297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3426841175623615954278125 1285065440858855982854297)
          ·
            refine ⟨963799080644141987140723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1285065440858855982854297 963799080644141987140723)
            ·
              refine ⟨1445698620966212980711085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963799080644141987140723 1445698620966212980711085)
              ·
                refine ⟨542136982862329867766657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1445698620966212980711085 542136982862329867766657)
                ·
                  refine ⟨406602737146747400824993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542136982862329867766657 406602737146747400824993)
                  ·
                    rfl

theorem cell20_890838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_890838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890838 prefixEnd_890838 := by exact prefixLift 890838
  have htrace : WordTrace (prefixWord ++ tailWord_890838) baseStart_890838 baseEnd_890838 := by
    simpa [prefixWord, tailWord_890838, baseEnd_890838] using wordTrace_append hprefix tailTrace_890838
  have hstable : (prefixWord ++ tailWord_890838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890838).length < 2 ^ (prefixWord ++ tailWord_890838).sum := by decide
  have hdescent : baseEnd_890838 < baseStart_890838 := by decide
  rcases family_descends (prefixWord ++ tailWord_890838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890912 : List Nat := [2, 1, 1, 16]
def baseStart_890912 : Nat := 118140960795 + 890912 * 2 ^ 59
def prefixEnd_890912 : Nat := 4983230072969 + 3 ^ 40 * 890912 * 2
def baseEnd_890912 : Nat := 1673401287091078322461

theorem tailTrace_890912 : CollatzResearch.WordTrace tailWord_890912 prefixEnd_890912 1673401287091078322461 := by
  unfold tailWord_890912
  simp only [CollatzResearch.WordTrace]
  refine ⟨16247115074192727250489495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21662820098923636333985993 16247115074192727250489495)
  ·
    refine ⟨24370672611289090875734243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16247115074192727250489495 24370672611289090875734243)
    ·
      refine ⟨36556008916933636313601365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24370672611289090875734243 36556008916933636313601365)
      ·
        refine ⟨1673401287091078322461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 36556008916933636313601365 1673401287091078322461)
        ·
          rfl

theorem cell20_890912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 16].length) (baseStart_890912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890912 prefixEnd_890912 := by exact prefixLift 890912
  have htrace : WordTrace (prefixWord ++ tailWord_890912) baseStart_890912 baseEnd_890912 := by
    simpa [prefixWord, tailWord_890912, baseEnd_890912] using wordTrace_append hprefix tailTrace_890912
  have hstable : (prefixWord ++ tailWord_890912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890912).length < 2 ^ (prefixWord ++ tailWord_890912).sum := by decide
  have hdescent : baseEnd_890912 < baseStart_890912 := by decide
  rcases family_descends (prefixWord ++ tailWord_890912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890915 : List Nat := [1, 1, 1, 4, 3, 1, 4, 2, 3]
def baseStart_890915 : Nat := 118140960795 + 890915 * 2 ^ 59
def prefixEnd_890915 : Nat := 4983230072969 + 3 ^ 40 * 890915 * 2
def baseEnd_890915 : Nat := 406637882044877355258011

theorem tailTrace_890915 : CollatzResearch.WordTrace tailWord_890915 prefixEnd_890915 406637882044877355258011 := by
  unfold tailWord_890915
  simp only [CollatzResearch.WordTrace]
  refine ⟨32494339567374586013338199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21662893044916390675558799 32494339567374586013338199)
  ·
    refine ⟨48741509351061879020007299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32494339567374586013338199 48741509351061879020007299)
    ·
      refine ⟨73112264026592818530010949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48741509351061879020007299 73112264026592818530010949)
      ·
        refine ⟨13708549504986153474377053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73112264026592818530010949 13708549504986153474377053)
        ·
          refine ⟨5140706064369807552891395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13708549504986153474377053 5140706064369807552891395)
          ·
            refine ⟨7711059096554711329337093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5140706064369807552891395 7711059096554711329337093)
            ·
              refine ⟨1445823580604008374250705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7711059096554711329337093 1445823580604008374250705)
              ·
                refine ⟨1084367685453006280688029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1445823580604008374250705 1084367685453006280688029)
                ·
                  refine ⟨406637882044877355258011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1084367685453006280688029 406637882044877355258011)
                  ·
                    rfl

theorem cell20_890915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 3].length) (baseStart_890915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890915 prefixEnd_890915 := by exact prefixLift 890915
  have htrace : WordTrace (prefixWord ++ tailWord_890915) baseStart_890915 baseEnd_890915 := by
    simpa [prefixWord, tailWord_890915, baseEnd_890915] using wordTrace_append hprefix tailTrace_890915
  have hstable : (prefixWord ++ tailWord_890915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890915).length < 2 ^ (prefixWord ++ tailWord_890915).sum := by decide
  have hdescent : baseEnd_890915 < baseStart_890915 := by decide
  rcases family_descends (prefixWord ++ tailWord_890915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890929 : List Nat := [1, 2, 2, 3, 1, 3, 3, 5]
def baseStart_890929 : Nat := 118140960795 + 890929 * 2 ^ 59
def prefixEnd_890929 : Nat := 4983230072969 + 3 ^ 40 * 890929 * 2
def baseEnd_890929 : Nat := 135548090675451842930429

theorem tailTrace_890929 : CollatzResearch.WordTrace tailWord_890929 prefixEnd_890929 135548090675451842930429 := by
  unfold tailWord_890929
  simp only [CollatzResearch.WordTrace]
  refine ⟨32494850189323866404347841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21663233459549244269565227 32494850189323866404347841)
  ·
    refine ⟨24371137641992899803260881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32494850189323866404347841 24371137641992899803260881)
    ·
      refine ⟨18278353231494674852445661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24371137641992899803260881 18278353231494674852445661)
      ·
        refine ⟨6854382461810503069667123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18278353231494674852445661 6854382461810503069667123)
        ·
          refine ⟨10281573692715754604500685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6854382461810503069667123 10281573692715754604500685)
          ·
            refine ⟨3855590134768407976687757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10281573692715754604500685 3855590134768407976687757)
            ·
              refine ⟨1445846300538152991257909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3855590134768407976687757 1445846300538152991257909)
              ·
                refine ⟨135548090675451842930429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1445846300538152991257909 135548090675451842930429)
                ·
                  rfl

theorem cell20_890929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 5].length) (baseStart_890929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890929 prefixEnd_890929 := by exact prefixLift 890929
  have htrace : WordTrace (prefixWord ++ tailWord_890929) baseStart_890929 baseEnd_890929 := by
    simpa [prefixWord, tailWord_890929, baseEnd_890929] using wordTrace_append hprefix tailTrace_890929
  have hstable : (prefixWord ++ tailWord_890929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890929).length < 2 ^ (prefixWord ++ tailWord_890929).sum := by decide
  have hdescent : baseEnd_890929 < baseStart_890929 := by decide
  rcases family_descends (prefixWord ++ tailWord_890929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890943 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 6]
def baseStart_890943 : Nat := 118140960795 + 890943 * 2 ^ 59
def prefixEnd_890943 : Nat := 4983230072969 + 3 ^ 40 * 890943 * 2
def baseEnd_890943 : Nat := 406650662007833702324563

theorem tailTrace_890943 : CollatzResearch.WordTrace tailWord_890943 prefixEnd_890943 406650662007833702324563 := by
  unfold tailWord_890943
  simp only [CollatzResearch.WordTrace]
  refine ⟨32495360811273146795357483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21663573874182097863571655 32495360811273146795357483)
  ·
    refine ⟨48743041216909720193036225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32495360811273146795357483 48743041216909720193036225)
    ·
      refine ⟨36557280912682290144777169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48743041216909720193036225 36557280912682290144777169)
      ·
        refine ⟨27417960684511717608582877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36557280912682290144777169 27417960684511717608582877)
        ·
          refine ⟨10281735256691894103218579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27417960684511717608582877 10281735256691894103218579)
          ·
            refine ⟨15422602885037841154827869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10281735256691894103218579 15422602885037841154827869)
            ·
              refine ⟨5783476081889190433060451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15422602885037841154827869 5783476081889190433060451)
              ·
                refine ⟨8675214122833785649590677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5783476081889190433060451 8675214122833785649590677)
                ·
                  refine ⟨406650662007833702324563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8675214122833785649590677 406650662007833702324563)
                  ·
                    rfl

theorem cell20_890943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_890943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890943 prefixEnd_890943 := by exact prefixLift 890943
  have htrace : WordTrace (prefixWord ++ tailWord_890943) baseStart_890943 baseEnd_890943 := by
    simpa [prefixWord, tailWord_890943, baseEnd_890943] using wordTrace_append hprefix tailTrace_890943
  have hstable : (prefixWord ++ tailWord_890943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890943).length < 2 ^ (prefixWord ++ tailWord_890943).sum := by decide
  have hdescent : baseEnd_890943 < baseStart_890943 := by decide
  rcases family_descends (prefixWord ++ tailWord_890943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890966 : List Nat := [5, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_890966 : Nat := 118140960795 + 890966 * 2 ^ 59
def prefixEnd_890966 : Nat := 4983230072969 + 3 ^ 40 * 890966 * 2
def baseEnd_890966 : Nat := 406661159834547844557803

theorem tailTrace_890966 : CollatzResearch.WordTrace tailWord_890966 prefixEnd_890966 406661159834547844557803 := by
  unfold tailWord_890966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2031012480636863857715297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21664133126793214482296501 2031012480636863857715297)
  ·
    refine ⟨1523259360477647893286473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2031012480636863857715297 1523259360477647893286473)
    ·
      refine ⟨1142444520358235919964855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1523259360477647893286473 1142444520358235919964855)
      ·
        refine ⟨1713666780537353879947283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1142444520358235919964855 1713666780537353879947283)
        ·
          refine ⟨2570500170806030819920925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1713666780537353879947283 2570500170806030819920925)
          ·
            refine ⟨963937564052261557470347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2570500170806030819920925 963937564052261557470347)
            ·
              refine ⟨1445906346078392336205521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963937564052261557470347 1445906346078392336205521)
              ·
                refine ⟨1084429759558794252154141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1445906346078392336205521 1084429759558794252154141)
                ·
                  refine ⟨406661159834547844557803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1084429759558794252154141 406661159834547844557803)
                  ·
                    rfl

theorem cell20_890966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_890966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_890966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_890966 prefixEnd_890966 := by exact prefixLift 890966
  have htrace : WordTrace (prefixWord ++ tailWord_890966) baseStart_890966 baseEnd_890966 := by
    simpa [prefixWord, tailWord_890966, baseEnd_890966] using wordTrace_append hprefix tailTrace_890966
  have hstable : (prefixWord ++ tailWord_890966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890966).length < 2 ^ (prefixWord ++ tailWord_890966).sum := by decide
  have hdescent : baseEnd_890966 < baseStart_890966 := by decide
  rcases family_descends (prefixWord ++ tailWord_890966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891005 : List Nat := [1, 4, 1, 1, 3, 3, 1, 6]
def baseStart_891005 : Nat := 118140960795 + 891005 * 2 ^ 59
def prefixEnd_891005 : Nat := 4983230072969 + 3 ^ 40 * 891005 * 2
def baseEnd_891005 : Nat := 135559653499079014085881

theorem tailTrace_891005 : CollatzResearch.WordTrace tailWord_891005 prefixEnd_891005 135559653499079014085881 := by
  unfold tailWord_891005
  simp only [CollatzResearch.WordTrace]
  refine ⟨32497622137048531384114469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21665081424699020922742979 32497622137048531384114469)
  ·
    refine ⟨6093304150696599634521463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32497622137048531384114469 6093304150696599634521463)
    ·
      refine ⟨9139956226044899451782195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6093304150696599634521463 9139956226044899451782195)
      ·
        refine ⟨13709934339067349177673293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9139956226044899451782195 13709934339067349177673293)
        ·
          refine ⟨5141225377150255941627485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13709934339067349177673293 5141225377150255941627485)
          ·
            refine ⟨1927959516431345978110307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5141225377150255941627485 1927959516431345978110307)
            ·
              refine ⟨2891939274647018967165461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927959516431345978110307 2891939274647018967165461)
              ·
                refine ⟨135559653499079014085881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2891939274647018967165461 135559653499079014085881)
                ·
                  rfl

theorem cell20_891005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 6].length) (baseStart_891005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891005 prefixEnd_891005 := by exact prefixLift 891005
  have htrace : WordTrace (prefixWord ++ tailWord_891005) baseStart_891005 baseEnd_891005 := by
    simpa [prefixWord, tailWord_891005, baseEnd_891005] using wordTrace_append hprefix tailTrace_891005
  have hstable : (prefixWord ++ tailWord_891005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891005).length < 2 ^ (prefixWord ++ tailWord_891005).sum := by decide
  have hdescent : baseEnd_891005 < baseStart_891005 := by decide
  rcases family_descends (prefixWord ++ tailWord_891005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891012 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 7]
def baseStart_891012 : Nat := 118140960795 + 891012 * 2 ^ 59
def prefixEnd_891012 : Nat := 4983230072969 + 3 ^ 40 * 891012 * 2
def baseEnd_891012 : Nat := 406682155487976129024281

theorem tailTrace_891012 : CollatzResearch.WordTrace tailWord_891012 prefixEnd_891012 406682155487976129024281 := by
  unfold tailWord_891012
  simp only [CollatzResearch.WordTrace]
  refine ⟨16248938724011585789809645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21665251632015447719746193 16248938724011585789809645)
  ·
    refine ⟨6093352021504344671178617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16248938724011585789809645 6093352021504344671178617)
    ·
      refine ⟨4570014016128258503383963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6093352021504344671178617 4570014016128258503383963)
      ·
        refine ⟨6855021024192387755075945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4570014016128258503383963 6855021024192387755075945)
        ·
          refine ⟨5141265768144290816306959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6855021024192387755075945 5141265768144290816306959)
          ·
            refine ⟨7711898652216436224460439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5141265768144290816306959 7711898652216436224460439)
            ·
              refine ⟨11567847978324654336690659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7711898652216436224460439 11567847978324654336690659)
              ·
                refine ⟨17351771967486981505035989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11567847978324654336690659 17351771967486981505035989)
                ·
                  refine ⟨406682155487976129024281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17351771967486981505035989 406682155487976129024281)
                  ·
                    rfl

theorem cell20_891012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_891012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891012 prefixEnd_891012 := by exact prefixLift 891012
  have htrace : WordTrace (prefixWord ++ tailWord_891012) baseStart_891012 baseEnd_891012 := by
    simpa [prefixWord, tailWord_891012, baseEnd_891012] using wordTrace_append hprefix tailTrace_891012
  have hstable : (prefixWord ++ tailWord_891012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891012).length < 2 ^ (prefixWord ++ tailWord_891012).sum := by decide
  have hdescent : baseEnd_891012 < baseStart_891012 := by decide
  rcases family_descends (prefixWord ++ tailWord_891012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891015 : List Nat := [1, 1, 4, 2, 1, 1, 5, 3, 2]
def baseStart_891015 : Nat := 118140960795 + 891015 * 2 ^ 59
def prefixEnd_891015 : Nat := 4983230072969 + 3 ^ 40 * 891015 * 2
def baseEnd_891015 : Nat := 406683524769721451924269

theorem tailTrace_891015 : CollatzResearch.WordTrace tailWord_891015 prefixEnd_891015 406683524769721451924269 := by
  unfold tailWord_891015
  simp only [CollatzResearch.WordTrace]
  refine ⟨32497986867012303091978499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21665324578008202061318999 32497986867012303091978499)
  ·
    refine ⟨48746980300518454637967749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32497986867012303091978499 48746980300518454637967749)
    ·
      refine ⟨9140058806347210244618953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48746980300518454637967749 9140058806347210244618953)
      ·
        refine ⟨6855044104760407683464215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9140058806347210244618953 6855044104760407683464215)
        ·
          refine ⟨10282566157140611525196323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6855044104760407683464215 10282566157140611525196323)
          ·
            refine ⟨15423849235710917287794485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10282566157140611525196323 15423849235710917287794485)
            ·
              refine ⟨1445985865847898495730733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15423849235710917287794485 1445985865847898495730733)
              ·
                refine ⟨542244699692961935899025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1445985865847898495730733 542244699692961935899025)
                ·
                  refine ⟨406683524769721451924269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542244699692961935899025 406683524769721451924269)
                  ·
                    rfl

theorem cell20_891015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 2].length) (baseStart_891015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891015 prefixEnd_891015 := by exact prefixLift 891015
  have htrace : WordTrace (prefixWord ++ tailWord_891015) baseStart_891015 baseEnd_891015 := by
    simpa [prefixWord, tailWord_891015, baseEnd_891015] using wordTrace_append hprefix tailTrace_891015
  have hstable : (prefixWord ++ tailWord_891015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891015).length < 2 ^ (prefixWord ++ tailWord_891015).sum := by decide
  have hdescent : baseEnd_891015 < baseStart_891015 := by decide
  rcases family_descends (prefixWord ++ tailWord_891015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891022 : List Nat := [4, 1, 1, 3, 3, 2, 6]
def baseStart_891022 : Nat := 118140960795 + 891022 * 2 ^ 59
def prefixEnd_891022 : Nat := 4983230072969 + 3 ^ 40 * 891022 * 2
def baseEnd_891022 : Nat := 45187413306717837632323

theorem tailTrace_891022 : CollatzResearch.WordTrace tailWord_891022 prefixEnd_891022 45187413306717837632323 := by
  unfold tailWord_891022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4062280272248367910935415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21665494785324628858322213 4062280272248367910935415)
  ·
    refine ⟨6093420408372551866403123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4062280272248367910935415 6093420408372551866403123)
    ·
      refine ⟨9140130612558827799604685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6093420408372551866403123 9140130612558827799604685)
      ·
        refine ⟨3427548979709560424851757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9140130612558827799604685 3427548979709560424851757)
        ·
          refine ⟨1285330867391085159319409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3427548979709560424851757 1285330867391085159319409)
          ·
            refine ⟨963998150543313869489557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1285330867391085159319409 963998150543313869489557)
            ·
              refine ⟨45187413306717837632323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 963998150543313869489557 45187413306717837632323)
              ·
                rfl

theorem cell20_891022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 6].length) (baseStart_891022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891022 prefixEnd_891022 := by exact prefixLift 891022
  have htrace : WordTrace (prefixWord ++ tailWord_891022) baseStart_891022 baseEnd_891022 := by
    simpa [prefixWord, tailWord_891022, baseEnd_891022] using wordTrace_append hprefix tailTrace_891022
  have hstable : (prefixWord ++ tailWord_891022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891022).length < 2 ^ (prefixWord ++ tailWord_891022).sum := by decide
  have hdescent : baseEnd_891022 < baseStart_891022 := by decide
  rcases family_descends (prefixWord ++ tailWord_891022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891028 : List Nat := [2, 4, 2, 3, 1, 1, 3, 2, 2]
def baseStart_891028 : Nat := 118140960795 + 891028 * 2 ^ 59
def prefixEnd_891028 : Nat := 4983230072969 + 3 ^ 40 * 891028 * 2
def baseEnd_891028 : Nat := 406689458323951184490883

theorem tailTrace_891028 : CollatzResearch.WordTrace tailWord_891028 prefixEnd_891028 406689458323951184490883 := by
  unfold tailWord_891028
  simp only [CollatzResearch.WordTrace]
  refine ⟨16249230507982603156100869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21665640677310137541467825 16249230507982603156100869)
  ·
    refine ⟨3046730720246738091768913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16249230507982603156100869 3046730720246738091768913)
    ·
      refine ⟨2285048040185053568826685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3046730720246738091768913 2285048040185053568826685)
      ·
        refine ⟨856893015069395088310007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2285048040185053568826685 856893015069395088310007)
        ·
          refine ⟨1285339522604092632465011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856893015069395088310007 1285339522604092632465011)
          ·
            refine ⟨1928009283906138948697517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285339522604092632465011 1928009283906138948697517)
            ·
              refine ⟨723003481464802105761569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1928009283906138948697517 723003481464802105761569)
              ·
                refine ⟨542252611098601579321177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723003481464802105761569 542252611098601579321177)
                ·
                  refine ⟨406689458323951184490883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542252611098601579321177 406689458323951184490883)
                  ·
                    rfl

theorem cell20_891028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_891028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891028 prefixEnd_891028 := by exact prefixLift 891028
  have htrace : WordTrace (prefixWord ++ tailWord_891028) baseStart_891028 baseEnd_891028 := by
    simpa [prefixWord, tailWord_891028, baseEnd_891028] using wordTrace_append hprefix tailTrace_891028
  have hstable : (prefixWord ++ tailWord_891028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891028).length < 2 ^ (prefixWord ++ tailWord_891028).sum := by decide
  have hdescent : baseEnd_891028 < baseStart_891028 := by decide
  rcases family_descends (prefixWord ++ tailWord_891028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891032 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 4]
def baseStart_891032 : Nat := 118140960795 + 891032 * 2 ^ 59
def prefixEnd_891032 : Nat := 4983230072969 + 3 ^ 40 * 891032 * 2
def baseEnd_891032 : Nat := 406691284032944948357533

theorem tailTrace_891032 : CollatzResearch.WordTrace tailWord_891032 prefixEnd_891032 406691284032944948357533 := by
  unfold tailWord_891032
  simp only [CollatzResearch.WordTrace]
  refine ⟨16249303453975357497673675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21665737938633809996898233 16249303453975357497673675)
  ·
    refine ⟨24373955180963036246510513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16249303453975357497673675 24373955180963036246510513)
    ·
      refine ⟨18280466385722277184882885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24373955180963036246510513 18280466385722277184882885)
      ·
        refine ⟨3427587447322926972165541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18280466385722277184882885 3427587447322926972165541)
        ·
          refine ⟨642672646373048807281039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3427587447322926972165541 642672646373048807281039)
          ·
            refine ⟨964008969559573210921559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642672646373048807281039 964008969559573210921559)
            ·
              refine ⟨1446013454339359816382339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964008969559573210921559 1446013454339359816382339)
              ·
                refine ⟨2169020181509039724573509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446013454339359816382339 2169020181509039724573509)
                ·
                  refine ⟨406691284032944948357533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2169020181509039724573509 406691284032944948357533)
                  ·
                    rfl

theorem cell20_891032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 4].length) (baseStart_891032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891032 prefixEnd_891032 := by exact prefixLift 891032
  have htrace : WordTrace (prefixWord ++ tailWord_891032) baseStart_891032 baseEnd_891032 := by
    simpa [prefixWord, tailWord_891032, baseEnd_891032] using wordTrace_append hprefix tailTrace_891032
  have hstable : (prefixWord ++ tailWord_891032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891032).length < 2 ^ (prefixWord ++ tailWord_891032).sum := by decide
  have hdescent : baseEnd_891032 < baseStart_891032 := by decide
  rcases family_descends (prefixWord ++ tailWord_891032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891064 : List Nat := [2, 1, 2, 1, 2, 1, 3, 8]
def baseStart_891064 : Nat := 118140960795 + 891064 * 2 ^ 59
def prefixEnd_891064 : Nat := 4983230072969 + 3 ^ 40 * 891064 * 2
def baseEnd_891064 : Nat := 135568629901631686430245

theorem tailTrace_891064 : CollatzResearch.WordTrace tailWord_891064 prefixEnd_891064 135568629901631686430245 := by
  unfold tailWord_891064
  simp only [CollatzResearch.WordTrace]
  refine ⟨16249887021917392230256123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21666516029223189640341497 16249887021917392230256123)
  ·
    refine ⟨24374830532876088345384185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16249887021917392230256123 24374830532876088345384185)
    ·
      refine ⟨18281122899657066259038139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24374830532876088345384185 18281122899657066259038139)
      ·
        refine ⟨27421684349485599388557209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18281122899657066259038139 27421684349485599388557209)
        ·
          refine ⟨20566263262114199541417907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27421684349485599388557209 20566263262114199541417907)
          ·
            refine ⟨30849394893171299312126861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20566263262114199541417907 30849394893171299312126861)
            ·
              refine ⟨11568523084939237242047573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30849394893171299312126861 11568523084939237242047573)
              ·
                refine ⟨135568629901631686430245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11568523084939237242047573 135568629901631686430245)
                ·
                  rfl

theorem cell20_891064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_891064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891064 prefixEnd_891064 := by exact prefixLift 891064
  have htrace : WordTrace (prefixWord ++ tailWord_891064) baseStart_891064 baseEnd_891064 := by
    simpa [prefixWord, tailWord_891064, baseEnd_891064] using wordTrace_append hprefix tailTrace_891064
  have hstable : (prefixWord ++ tailWord_891064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891064).length < 2 ^ (prefixWord ++ tailWord_891064).sum := by decide
  have hdescent : baseEnd_891064 < baseStart_891064 := by decide
  rcases family_descends (prefixWord ++ tailWord_891064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891095 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 4]
def baseStart_891095 : Nat := 118140960795 + 891095 * 2 ^ 59
def prefixEnd_891095 : Nat := 4983230072969 + 3 ^ 40 * 891095 * 2
def baseEnd_891095 : Nat := 406720038949596729257275

theorem tailTrace_891095 : CollatzResearch.WordTrace tailWord_891095 prefixEnd_891095 406720038949596729257275 := by
  unfold tailWord_891095
  simp only [CollatzResearch.WordTrace]
  refine ⟨32500904706722476754890739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21667269804481651169927159 32500904706722476754890739)
  ·
    refine ⟨48751357060083715132336109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32500904706722476754890739 48751357060083715132336109)
    ·
      refine ⟨18281758897531393174626041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48751357060083715132336109 18281758897531393174626041)
      ·
        refine ⟨13711319173148544880969531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18281758897531393174626041 13711319173148544880969531)
        ·
          refine ⟨20566978759722817321454297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13711319173148544880969531 20566978759722817321454297)
          ·
            refine ⟨15425234069792112991090723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20566978759722817321454297 15425234069792112991090723)
            ·
              refine ⟨23137851104688169486636085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15425234069792112991090723 23137851104688169486636085)
              ·
                refine ⟨2169173541064515889372133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23137851104688169486636085 2169173541064515889372133)
                ·
                  refine ⟨406720038949596729257275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2169173541064515889372133 406720038949596729257275)
                  ·
                    rfl

theorem cell20_891095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_891095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891095 prefixEnd_891095 := by exact prefixLift 891095
  have htrace : WordTrace (prefixWord ++ tailWord_891095) baseStart_891095 baseEnd_891095 := by
    simpa [prefixWord, tailWord_891095, baseEnd_891095] using wordTrace_append hprefix tailTrace_891095
  have hstable : (prefixWord ++ tailWord_891095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891095).length < 2 ^ (prefixWord ++ tailWord_891095).sum := by decide
  have hdescent : baseEnd_891095 < baseStart_891095 := by decide
  rcases family_descends (prefixWord ++ tailWord_891095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891112 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 4]
def baseStart_891112 : Nat := 118140960795 + 891112 * 2 ^ 59
def prefixEnd_891112 : Nat := 4983230072969 + 3 ^ 40 * 891112 * 2
def baseEnd_891112 : Nat := 406727798212820225690539

theorem tailTrace_891112 : CollatzResearch.WordTrace tailWord_891112 prefixEnd_891112 406727798212820225690539 := by
  unfold tailWord_891112
  simp only [CollatzResearch.WordTrace]
  refine ⟨16250762373830444329129795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21667683165107259105506393 16250762373830444329129795)
  ·
    refine ⟨24376143560745666493694693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16250762373830444329129795 24376143560745666493694693)
    ·
      refine ⟨4570526917639812467567755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24376143560745666493694693 4570526917639812467567755)
      ·
        refine ⟨6855790376459718701351633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4570526917639812467567755 6855790376459718701351633)
        ·
          refine ⟨5141842782344789026013725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6855790376459718701351633 5141842782344789026013725)
          ·
            refine ⟨1928191043379295884755147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5141842782344789026013725 1928191043379295884755147)
            ·
              refine ⟨2892286565068943827132721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1928191043379295884755147 2892286565068943827132721)
              ·
                refine ⟨2169214923801707870349541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2892286565068943827132721 2169214923801707870349541)
                ·
                  refine ⟨406727798212820225690539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2169214923801707870349541 406727798212820225690539)
                  ·
                    rfl

theorem cell20_891112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_891112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891112 prefixEnd_891112 := by exact prefixLift 891112
  have htrace : WordTrace (prefixWord ++ tailWord_891112) baseStart_891112 baseEnd_891112 := by
    simpa [prefixWord, tailWord_891112, baseEnd_891112] using wordTrace_append hprefix tailTrace_891112
  have hstable : (prefixWord ++ tailWord_891112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891112).length < 2 ^ (prefixWord ++ tailWord_891112).sum := by decide
  have hdescent : baseEnd_891112 < baseStart_891112 := by decide
  rcases family_descends (prefixWord ++ tailWord_891112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891150 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_891150 : Nat := 118140960795 + 891150 * 2 ^ 59
def prefixEnd_891150 : Nat := 4983230072969 + 3 ^ 40 * 891150 * 2
def baseEnd_891150 : Nat := 406745142448260982423717

theorem tailTrace_891150 : CollatzResearch.WordTrace tailWord_891150 prefixEnd_891150 406745142448260982423717 := by
  unfold tailWord_891150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4062863840190402643517863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21668607147682147432095269 4062863840190402643517863)
  ·
    refine ⟨6094295760285603965276795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4062863840190402643517863 6094295760285603965276795)
    ·
      refine ⟨9141443640428405947915193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6094295760285603965276795 9141443640428405947915193)
      ·
        refine ⟨6856082730321304460936395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9141443640428405947915193 6856082730321304460936395)
        ·
          refine ⟨10284124095481956691404593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6856082730321304460936395 10284124095481956691404593)
          ·
            refine ⟨7713093071611467518553445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10284124095481956691404593 7713093071611467518553445)
            ·
              refine ⟨1446204950927150159728771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7713093071611467518553445 1446204950927150159728771)
              ·
                refine ⟨2169307426390725239593157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446204950927150159728771 2169307426390725239593157)
                ·
                  refine ⟨406745142448260982423717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2169307426390725239593157 406745142448260982423717)
                  ·
                    rfl

theorem cell20_891150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_891150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891150 prefixEnd_891150 := by exact prefixLift 891150
  have htrace : WordTrace (prefixWord ++ tailWord_891150) baseStart_891150 baseEnd_891150 := by
    simpa [prefixWord, tailWord_891150, baseEnd_891150] using wordTrace_append hprefix tailTrace_891150
  have hstable : (prefixWord ++ tailWord_891150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891150).length < 2 ^ (prefixWord ++ tailWord_891150).sum := by decide
  have hdescent : baseEnd_891150 < baseStart_891150 := by decide
  rcases family_descends (prefixWord ++ tailWord_891150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891171 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 4]
def baseStart_891171 : Nat := 118140960795 + 891171 * 2 ^ 59
def prefixEnd_891171 : Nat := 4983230072969 + 3 ^ 40 * 891171 * 2
def baseEnd_891171 : Nat := 406754727420478242723631

theorem tailTrace_891171 : CollatzResearch.WordTrace tailWord_891171 prefixEnd_891171 406754727420478242723631 := by
  unfold tailWord_891171
  simp only [CollatzResearch.WordTrace]
  refine ⟨32503676654447141734657367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21669117769631427823104911 32503676654447141734657367)
  ·
    refine ⟨48755514981670712601986051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32503676654447141734657367 48755514981670712601986051)
    ·
      refine ⟨73133272472506068902979077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48755514981670712601986051 73133272472506068902979077)
      ·
        refine ⟨13712488588594887919308577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73133272472506068902979077 13712488588594887919308577)
        ·
          refine ⟨10284366441446165939481433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13712488588594887919308577 10284366441446165939481433)
          ·
            refine ⟨7713274831084624454611075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10284366441446165939481433 7713274831084624454611075)
            ·
              refine ⟨11569912246626936681916613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713274831084624454611075 11569912246626936681916613)
              ·
                refine ⟨2169358546242550627859365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11569912246626936681916613 2169358546242550627859365)
                ·
                  refine ⟨406754727420478242723631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2169358546242550627859365 406754727420478242723631)
                  ·
                    rfl

theorem cell20_891171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_891171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891171 prefixEnd_891171 := by exact prefixLift 891171
  have htrace : WordTrace (prefixWord ++ tailWord_891171) baseStart_891171 baseEnd_891171 := by
    simpa [prefixWord, tailWord_891171, baseEnd_891171] using wordTrace_append hprefix tailTrace_891171
  have hstable : (prefixWord ++ tailWord_891171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891171).length < 2 ^ (prefixWord ++ tailWord_891171).sum := by decide
  have hdescent : baseEnd_891171 < baseStart_891171 := by decide
  rcases family_descends (prefixWord ++ tailWord_891171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891201 : List Nat := [1, 2, 5, 2, 2, 1, 3, 2, 2]
def baseStart_891201 : Nat := 118140960795 + 891201 * 2 ^ 59
def prefixEnd_891201 : Nat := 4983230072969 + 3 ^ 40 * 891201 * 2
def baseEnd_891201 : Nat := 406768420237931471723509

theorem tailTrace_891201 : CollatzResearch.WordTrace tailWord_891201 prefixEnd_891201 406768420237931471723509 := by
  unfold tailWord_891201
  simp only [CollatzResearch.WordTrace]
  refine ⟨32504770844338456858249457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21669847229558971238832971 32504770844338456858249457)
  ·
    refine ⟨24378578133253842643687093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32504770844338456858249457 24378578133253842643687093)
    ·
      refine ⟨2285491699992547747845665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24378578133253842643687093 2285491699992547747845665)
      ·
        refine ⟨1714118774994410810884249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2285491699992547747845665 1714118774994410810884249)
        ·
          refine ⟨1285589081245808108163187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1714118774994410810884249 1285589081245808108163187)
          ·
            refine ⟨1928383621868712162244781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285589081245808108163187 1928383621868712162244781)
            ·
              refine ⟨723143858200767060841793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1928383621868712162244781 723143858200767060841793)
              ·
                refine ⟨542357893650575295631345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723143858200767060841793 542357893650575295631345)
                ·
                  refine ⟨406768420237931471723509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542357893650575295631345 406768420237931471723509)
                  ·
                    rfl

theorem cell20_891201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 2].length) (baseStart_891201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891201 prefixEnd_891201 := by exact prefixLift 891201
  have htrace : WordTrace (prefixWord ++ tailWord_891201) baseStart_891201 baseEnd_891201 := by
    simpa [prefixWord, tailWord_891201, baseEnd_891201] using wordTrace_append hprefix tailTrace_891201
  have hstable : (prefixWord ++ tailWord_891201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891201).length < 2 ^ (prefixWord ++ tailWord_891201).sum := by decide
  have hdescent : baseEnd_891201 < baseStart_891201 := by decide
  rcases family_descends (prefixWord ++ tailWord_891201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891216 : List Nat := [2, 1, 1, 1, 1, 6, 1, 7]
def baseStart_891216 : Nat := 118140960795 + 891216 * 2 ^ 59
def prefixEnd_891216 : Nat := 4983230072969 + 3 ^ 40 * 891216 * 2
def baseEnd_891216 : Nat := 135591755548886028741149

theorem tailTrace_891216 : CollatzResearch.WordTrace tailWord_891216 prefixEnd_891216 135591755548886028741149 := by
  unfold tailWord_891216
  simp only [CollatzResearch.WordTrace]
  refine ⟨16252658969642057210022751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21670211959522742946697001 16252658969642057210022751)
  ·
    refine ⟨24378988454463085815034127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16252658969642057210022751 24378988454463085815034127)
    ·
      refine ⟨36568482681694628722551191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24378988454463085815034127 36568482681694628722551191)
      ·
        refine ⟨54852724022541943083826787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36568482681694628722551191 54852724022541943083826787)
        ·
          refine ⟨82279086033812914625740181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54852724022541943083826787 82279086033812914625740181)
          ·
            refine ⟨3856832157834980373081571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82279086033812914625740181 3856832157834980373081571)
            ·
              refine ⟨5785248236752470559622357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3856832157834980373081571 5785248236752470559622357)
              ·
                refine ⟨135591755548886028741149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5785248236752470559622357 135591755548886028741149)
                ·
                  rfl

theorem cell20_891216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_891216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891216 prefixEnd_891216 := by exact prefixLift 891216
  have htrace : WordTrace (prefixWord ++ tailWord_891216) baseStart_891216 baseEnd_891216 := by
    simpa [prefixWord, tailWord_891216, baseEnd_891216] using wordTrace_append hprefix tailTrace_891216
  have hstable : (prefixWord ++ tailWord_891216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891216).length < 2 ^ (prefixWord ++ tailWord_891216).sum := by decide
  have hdescent : baseEnd_891216 < baseStart_891216 := by decide
  rcases family_descends (prefixWord ++ tailWord_891216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891288 : List Nat := [2, 1, 2, 5, 1, 2, 3, 4]
def baseStart_891288 : Nat := 118140960795 + 891288 * 2 ^ 59
def prefixEnd_891288 : Nat := 4983230072969 + 3 ^ 40 * 891288 * 2
def baseEnd_891288 : Nat := 135602709802848611941051

theorem tailTrace_891288 : CollatzResearch.WordTrace tailWord_891288 prefixEnd_891288 135602709802848611941051 := by
  unfold tailWord_891288
  simp only [CollatzResearch.WordTrace]
  refine ⟨16253971997511635358333259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21671962663348847144444345 16253971997511635358333259)
  ·
    refine ⟨24380957996267453037499889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16253971997511635358333259 24380957996267453037499889)
    ·
      refine ⟨18285718497200589778124917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24380957996267453037499889 18285718497200589778124917)
      ·
        refine ⟨1714286109112555291699211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18285718497200589778124917 1714286109112555291699211)
        ·
          refine ⟨2571429163668832937548817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1714286109112555291699211 2571429163668832937548817)
          ·
            refine ⟨1928571872751624703161613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2571429163668832937548817 1928571872751624703161613)
            ·
              refine ⟨723214452281859263685605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1928571872751624703161613 723214452281859263685605)
              ·
                refine ⟨135602709802848611941051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 723214452281859263685605 135602709802848611941051)
                ·
                  rfl

theorem cell20_891288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_891288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891288 prefixEnd_891288 := by exact prefixLift 891288
  have htrace : WordTrace (prefixWord ++ tailWord_891288) baseStart_891288 baseEnd_891288 := by
    simpa [prefixWord, tailWord_891288, baseEnd_891288] using wordTrace_append hprefix tailTrace_891288
  have hstable : (prefixWord ++ tailWord_891288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891288).length < 2 ^ (prefixWord ++ tailWord_891288).sum := by decide
  have hdescent : baseEnd_891288 < baseStart_891288 := by decide
  rcases family_descends (prefixWord ++ tailWord_891288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891368 : List Nat := [2, 1, 4, 1, 1, 3, 8]
def baseStart_891368 : Nat := 118140960795 + 891368 * 2 ^ 59
def prefixEnd_891368 : Nat := 4983230072969 + 3 ^ 40 * 891368 * 2
def baseEnd_891368 : Nat := 45204960398713457017351

theorem tailTrace_891368 : CollatzResearch.WordTrace tailWord_891368 prefixEnd_891368 45204960398713457017351 := by
  unfold tailWord_891368
  simp only [CollatzResearch.WordTrace]
  refine ⟨16255430917366722189789379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21673907889822296253052505 16255430917366722189789379)
  ·
    refine ⟨24383146376050083284684069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16255430917366722189789379 24383146376050083284684069)
    ·
      refine ⟨4571839945509390615878263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24383146376050083284684069 4571839945509390615878263)
      ·
        refine ⟨6857759918264085923817395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4571839945509390615878263 6857759918264085923817395)
        ·
          refine ⟨10286639877396128885726093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6857759918264085923817395 10286639877396128885726093)
          ·
            refine ⟨3857489954023548332147285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10286639877396128885726093 3857489954023548332147285)
            ·
              refine ⟨45204960398713457017351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3857489954023548332147285 45204960398713457017351)
              ·
                rfl

theorem cell20_891368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 8].length) (baseStart_891368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891368 prefixEnd_891368 := by exact prefixLift 891368
  have htrace : WordTrace (prefixWord ++ tailWord_891368) baseStart_891368 baseEnd_891368 := by
    simpa [prefixWord, tailWord_891368, baseEnd_891368] using wordTrace_append hprefix tailTrace_891368
  have hstable : (prefixWord ++ tailWord_891368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891368).length < 2 ^ (prefixWord ++ tailWord_891368).sum := by decide
  have hdescent : baseEnd_891368 < baseStart_891368 := by decide
  rcases family_descends (prefixWord ++ tailWord_891368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891374 : List Nat := [4, 1, 2, 1, 2, 3, 3, 2, 2]
def baseStart_891374 : Nat := 118140960795 + 891374 * 2 ^ 59
def prefixEnd_891374 : Nat := 4983230072969 + 3 ^ 40 * 891374 * 2
def baseEnd_891374 : Nat := 406847382151911758956135

theorem tailTrace_891374 : CollatzResearch.WordTrace tailWord_891374 prefixEnd_891374 406847382151911758956135 := by
  unfold tailWord_891374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4063885084088963425537147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21674053781807804936198117 4063885084088963425537147)
  ·
    refine ⟨6095827626133445138305721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4063885084088963425537147 6095827626133445138305721)
    ·
      refine ⟨4571870719600083853729291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6095827626133445138305721 4571870719600083853729291)
      ·
        refine ⟨6857806079400125780593937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4571870719600083853729291 6857806079400125780593937)
        ·
          refine ⟨5143354559550094335445453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6857806079400125780593937 5143354559550094335445453)
          ·
            refine ⟨1928757959831285375792045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5143354559550094335445453 1928757959831285375792045)
            ·
              refine ⟨723284234936732015922017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1928757959831285375792045 723284234936732015922017)
              ·
                refine ⟨542463176202549011941513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723284234936732015922017 542463176202549011941513)
                ·
                  refine ⟨406847382151911758956135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542463176202549011941513 406847382151911758956135)
                  ·
                    rfl

theorem cell20_891374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_891374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891374 prefixEnd_891374 := by exact prefixLift 891374
  have htrace : WordTrace (prefixWord ++ tailWord_891374) baseStart_891374 baseEnd_891374 := by
    simpa [prefixWord, tailWord_891374, baseEnd_891374] using wordTrace_append hprefix tailTrace_891374
  have hstable : (prefixWord ++ tailWord_891374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891374).length < 2 ^ (prefixWord ++ tailWord_891374).sum := by decide
  have hdescent : baseEnd_891374 < baseStart_891374 := by decide
  rcases family_descends (prefixWord ++ tailWord_891374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891461 : List Nat := [1, 3, 1, 1, 1, 6, 3, 4]
def baseStart_891461 : Nat := 118140960795 + 891461 * 2 ^ 59
def prefixEnd_891461 : Nat := 4983230072969 + 3 ^ 40 * 891461 * 2
def baseEnd_891461 : Nat := 135629030440842041018593

theorem tailTrace_891461 : CollatzResearch.WordTrace tailWord_891461 prefixEnd_891461 135629030440842041018593 := by
  unfold tailWord_891461
  simp only [CollatzResearch.WordTrace]
  refine ⟨32514253823396521262714237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21676169215597680841809491 32514253823396521262714237)
  ·
    refine ⟨12192845183773695473517839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32514253823396521262714237 12192845183773695473517839)
    ·
      refine ⟨18289267775660543210276759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12192845183773695473517839 18289267775660543210276759)
      ·
        refine ⟨27433901663490814815415139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18289267775660543210276759 27433901663490814815415139)
        ·
          refine ⟨41150852495236222223122709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27433901663490814815415139 41150852495236222223122709)
          ·
            refine ⟨1928946210714197916708877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41150852495236222223122709 1928946210714197916708877)
            ·
              refine ⟨723354829017824218765829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1928946210714197916708877 723354829017824218765829)
              ·
                refine ⟨135629030440842041018593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 723354829017824218765829 135629030440842041018593)
                ·
                  rfl

theorem cell20_891461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 4].length) (baseStart_891461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891461 prefixEnd_891461 := by exact prefixLift 891461
  have htrace : WordTrace (prefixWord ++ tailWord_891461) baseStart_891461 baseEnd_891461 := by
    simpa [prefixWord, tailWord_891461, baseEnd_891461] using wordTrace_append hprefix tailTrace_891461
  have hstable : (prefixWord ++ tailWord_891461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891461).length < 2 ^ (prefixWord ++ tailWord_891461).sum := by decide
  have hdescent : baseEnd_891461 < baseStart_891461 := by decide
  rcases family_descends (prefixWord ++ tailWord_891461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891492 : List Nat := [2, 3, 1, 1, 2, 2, 1, 6, 2]
def baseStart_891492 : Nat := 118140960795 + 891492 * 2 ^ 59
def prefixEnd_891492 : Nat := 4983230072969 + 3 ^ 40 * 891492 * 2
def baseEnd_891492 : Nat := 406901240567227793022319

theorem tailTrace_891492 : CollatzResearch.WordTrace tailWord_891492 prefixEnd_891492 406901240567227793022319 := by
  unfold tailWord_891492
  simp only [CollatzResearch.WordTrace]
  refine ⟨16257692243142106778546365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21676922990856142371395153 16257692243142106778546365)
  ·
    refine ⟨6096634591178290041954887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16257692243142106778546365 6096634591178290041954887)
    ·
      refine ⟨9144951886767435062932331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6096634591178290041954887 9144951886767435062932331)
      ·
        refine ⟨13717427830151152594398497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9144951886767435062932331 13717427830151152594398497)
        ·
          refine ⟨10288070872613364445798873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13717427830151152594398497 10288070872613364445798873)
          ·
            refine ⟨7716053154460023334349155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10288070872613364445798873 7716053154460023334349155)
            ·
              refine ⟨11574079731690035001523733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7716053154460023334349155 11574079731690035001523733)
              ·
                refine ⟨542534987422970390696425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11574079731690035001523733 542534987422970390696425)
                ·
                  refine ⟨406901240567227793022319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542534987422970390696425 406901240567227793022319)
                  ·
                    rfl

theorem cell20_891492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_891492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891492 prefixEnd_891492 := by exact prefixLift 891492
  have htrace : WordTrace (prefixWord ++ tailWord_891492) baseStart_891492 baseEnd_891492 := by
    simpa [prefixWord, tailWord_891492, baseEnd_891492] using wordTrace_append hprefix tailTrace_891492
  have hstable : (prefixWord ++ tailWord_891492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891492).length < 2 ^ (prefixWord ++ tailWord_891492).sum := by decide
  have hdescent : baseEnd_891492 < baseStart_891492 := by decide
  rcases family_descends (prefixWord ++ tailWord_891492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891502 : List Nat := [4, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_891502 : Nat := 118140960795 + 891502 * 2 ^ 59
def prefixEnd_891502 : Nat := 4983230072969 + 3 ^ 40 * 891502 * 2
def baseEnd_891502 : Nat := 406905804839712202688945

theorem tailTrace_891502 : CollatzResearch.WordTrace tailWord_891502 prefixEnd_891502 406905804839712202688945 := by
  unfold tailWord_891502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4064468652030998158119595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21677166144165323509971173 4064468652030998158119595)
  ·
    refine ⟨6096702978046497237179393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4064468652030998158119595 6096702978046497237179393)
    ·
      refine ⟨4572527233534872927884545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6096702978046497237179393 4572527233534872927884545)
      ·
        refine ⟨3429395425151154695913409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4572527233534872927884545 3429395425151154695913409)
        ·
          refine ⟨2572046568863366021935057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3429395425151154695913409 2572046568863366021935057)
          ·
            refine ⟨1929034926647524516451293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2572046568863366021935057 1929034926647524516451293)
            ·
              refine ⟨723388097492821693669235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1929034926647524516451293 723388097492821693669235)
              ·
                refine ⟨1085082146239232540503853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723388097492821693669235 1085082146239232540503853)
                ·
                  refine ⟨406905804839712202688945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1085082146239232540503853 406905804839712202688945)
                  ·
                    rfl

theorem cell20_891502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_891502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891502 prefixEnd_891502 := by exact prefixLift 891502
  have htrace : WordTrace (prefixWord ++ tailWord_891502) baseStart_891502 baseEnd_891502 := by
    simpa [prefixWord, tailWord_891502, baseEnd_891502] using wordTrace_append hprefix tailTrace_891502
  have hstable : (prefixWord ++ tailWord_891502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891502).length < 2 ^ (prefixWord ++ tailWord_891502).sum := by decide
  have hdescent : baseEnd_891502 < baseStart_891502 := by decide
  rcases family_descends (prefixWord ++ tailWord_891502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891513 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 4]
def baseStart_891513 : Nat := 118140960795 + 891513 * 2 ^ 59
def prefixEnd_891513 : Nat := 4983230072969 + 3 ^ 40 * 891513 * 2
def baseEnd_891513 : Nat := 406910825539445053322233

theorem tailTrace_891513 : CollatzResearch.WordTrace tailWord_891513 prefixEnd_891513 406910825539445053322233 := by
  unfold tailWord_891513
  simp only [CollatzResearch.WordTrace]
  refine ⟨32516150419208134143607193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21677433612805422762404795 32516150419208134143607193)
  ·
    refine ⟨24387112814406100607705395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32516150419208134143607193 24387112814406100607705395)
    ·
      refine ⟨36580669221609150911558093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24387112814406100607705395 36580669221609150911558093)
      ·
        refine ⟨13717750958103431591834285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36580669221609150911558093 13717750958103431591834285)
        ·
          refine ⟨5144156609288786846937857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13717750958103431591834285 5144156609288786846937857)
          ·
            refine ⟨3858117456966590135203393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5144156609288786846937857 3858117456966590135203393)
            ·
              refine ⟨2893588092724942601402545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3858117456966590135203393 2893588092724942601402545)
              ·
                refine ⟨2170191069543706951051909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2893588092724942601402545 2170191069543706951051909)
                ·
                  refine ⟨406910825539445053322233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2170191069543706951051909 406910825539445053322233)
                  ·
                    rfl

theorem cell20_891513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_891513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891513 prefixEnd_891513 := by exact prefixLift 891513
  have htrace : WordTrace (prefixWord ++ tailWord_891513) baseStart_891513 baseEnd_891513 := by
    simpa [prefixWord, tailWord_891513, baseEnd_891513] using wordTrace_append hprefix tailTrace_891513
  have hstable : (prefixWord ++ tailWord_891513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891513).length < 2 ^ (prefixWord ++ tailWord_891513).sum := by decide
  have hdescent : baseEnd_891513 < baseStart_891513 := by decide
  rcases family_descends (prefixWord ++ tailWord_891513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891520 : List Nat := [2, 1, 1, 2, 1, 6, 1, 6]
def baseStart_891520 : Nat := 118140960795 + 891520 * 2 ^ 59
def prefixEnd_891520 : Nat := 4983230072969 + 3 ^ 40 * 891520 * 2
def baseEnd_891520 : Nat := 135638006843394713362957

theorem tailTrace_891520 : CollatzResearch.WordTrace tailWord_891520 prefixEnd_891520 135638006843394713362957 := by
  unfold tailWord_891520
  simp only [CollatzResearch.WordTrace]
  refine ⟨16258202865091387169556007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21677603820121849559408009 16258202865091387169556007)
  ·
    refine ⟨24387304297637080754334011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16258202865091387169556007 24387304297637080754334011)
    ·
      refine ⟨36580956446455621131501017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24387304297637080754334011 36580956446455621131501017)
      ·
        refine ⟨27435717334841715848625763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36580956446455621131501017 27435717334841715848625763)
        ·
          refine ⟨41153576002262573772938645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27435717334841715848625763 41153576002262573772938645)
          ·
            refine ⟨1929073875106058145606499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41153576002262573772938645 1929073875106058145606499)
            ·
              refine ⟨2893610812659087218409749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1929073875106058145606499 2893610812659087218409749)
              ·
                refine ⟨135638006843394713362957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2893610812659087218409749 135638006843394713362957)
                ·
                  rfl

theorem cell20_891520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_891520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891520 prefixEnd_891520 := by exact prefixLift 891520
  have htrace : WordTrace (prefixWord ++ tailWord_891520) baseStart_891520 baseEnd_891520 := by
    simpa [prefixWord, tailWord_891520, baseEnd_891520] using wordTrace_append hprefix tailTrace_891520
  have hstable : (prefixWord ++ tailWord_891520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891520).length < 2 ^ (prefixWord ++ tailWord_891520).sum := by decide
  have hdescent : baseEnd_891520 < baseStart_891520 := by decide
  rcases family_descends (prefixWord ++ tailWord_891520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891527 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 7]
def baseStart_891527 : Nat := 118140960795 + 891527 * 2 ^ 59
def prefixEnd_891527 : Nat := 4983230072969 + 3 ^ 40 * 891527 * 2
def baseEnd_891527 : Nat := 406917215520923226855509

theorem tailTrace_891527 : CollatzResearch.WordTrace tailWord_891527 prefixEnd_891527 406917215520923226855509 := by
  unfold tailWord_891527
  simp only [CollatzResearch.WordTrace]
  refine ⟨32516661041157414534616835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21677774027438276356411223 32516661041157414534616835)
  ·
    refine ⟨48774991561736121801925253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32516661041157414534616835 48774991561736121801925253)
    ·
      refine ⟨9145310917825522837860985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48774991561736121801925253 9145310917825522837860985)
      ·
        refine ⟨6858983188369142128395739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9145310917825522837860985 6858983188369142128395739)
        ·
          refine ⟨10288474782553713192593609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6858983188369142128395739 10288474782553713192593609)
          ·
            refine ⟨7716356086915284894445207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10288474782553713192593609 7716356086915284894445207)
            ·
              refine ⟨11574534130372927341667811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7716356086915284894445207 11574534130372927341667811)
              ·
                refine ⟨17361801195559391012501717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11574534130372927341667811 17361801195559391012501717)
                ·
                  refine ⟨406917215520923226855509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17361801195559391012501717 406917215520923226855509)
                  ·
                    rfl

theorem cell20_891527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_891527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891527 prefixEnd_891527 := by exact prefixLift 891527
  have htrace : WordTrace (prefixWord ++ tailWord_891527) baseStart_891527 baseEnd_891527 := by
    simpa [prefixWord, tailWord_891527, baseEnd_891527] using wordTrace_append hprefix tailTrace_891527
  have hstable : (prefixWord ++ tailWord_891527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891527).length < 2 ^ (prefixWord ++ tailWord_891527).sum := by decide
  have hdescent : baseEnd_891527 < baseStart_891527 := by decide
  rcases family_descends (prefixWord ++ tailWord_891527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891544 : List Nat := [2, 1, 2, 4, 1, 1, 2, 4, 3]
def baseStart_891544 : Nat := 118140960795 + 891544 * 2 ^ 59
def prefixEnd_891544 : Nat := 4983230072969 + 3 ^ 40 * 891544 * 2
def baseEnd_891544 : Nat := 406924974784146723288773

theorem tailTrace_891544 : CollatzResearch.WordTrace tailWord_891544 prefixEnd_891544 406924974784146723288773 := by
  unfold tailWord_891544
  simp only [CollatzResearch.WordTrace]
  refine ⟨16258640541047913218992843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21678187388063884291990457 16258640541047913218992843)
  ·
    refine ⟨24387960811571869828489265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16258640541047913218992843 24387960811571869828489265)
    ·
      refine ⟨18290970608678902371366949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24387960811571869828489265 18290970608678902371366949)
      ·
        refine ⟨3429556989127294194631303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18290970608678902371366949 3429556989127294194631303)
        ·
          refine ⟨5144335483690941291946955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3429556989127294194631303 5144335483690941291946955)
          ·
            refine ⟨7716503225536411937920433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5144335483690941291946955 7716503225536411937920433)
            ·
              refine ⟨5787377419152308953440325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7716503225536411937920433 5787377419152308953440325)
              ·
                refine ⟨1085133266091057928770061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5787377419152308953440325 1085133266091057928770061)
                ·
                  refine ⟨406924974784146723288773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1085133266091057928770061 406924974784146723288773)
                  ·
                    rfl

theorem cell20_891544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_891544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891544 prefixEnd_891544 := by exact prefixLift 891544
  have htrace : WordTrace (prefixWord ++ tailWord_891544) baseStart_891544 baseEnd_891544 := by
    simpa [prefixWord, tailWord_891544, baseEnd_891544] using wordTrace_append hprefix tailTrace_891544
  have hstable : (prefixWord ++ tailWord_891544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891544).length < 2 ^ (prefixWord ++ tailWord_891544).sum := by decide
  have hdescent : baseEnd_891544 < baseStart_891544 := by decide
  rcases family_descends (prefixWord ++ tailWord_891544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891596 : List Nat := [2, 2, 1, 5, 1, 9]
def baseStart_891596 : Nat := 118140960795 + 891596 * 2 ^ 59
def prefixEnd_891596 : Nat := 4983230072969 + 3 ^ 40 * 891596 * 2
def baseEnd_891596 : Nat := 15072174407446876057601

theorem tailTrace_891596 : CollatzResearch.WordTrace tailWord_891596 prefixEnd_891596 15072174407446876057601 := by
  unfold tailWord_891596
  simp only [CollatzResearch.WordTrace]
  refine ⟨16259588838953719659439321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21679451785271626212585761 16259588838953719659439321)
  ·
    refine ⟨12194691629215289744579491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16259588838953719659439321 12194691629215289744579491)
    ·
      refine ⟨18292037443822934616869237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12194691629215289744579491 18292037443822934616869237)
      ·
        refine ⟨1714878510358400120331491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18292037443822934616869237 1714878510358400120331491)
        ·
          refine ⟨2572317765537600180497237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1714878510358400120331491 2572317765537600180497237)
          ·
            refine ⟨15072174407446876057601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2572317765537600180497237 15072174407446876057601)
            ·
              rfl

theorem cell20_891596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 9].length) (baseStart_891596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891596 prefixEnd_891596 := by exact prefixLift 891596
  have htrace : WordTrace (prefixWord ++ tailWord_891596) baseStart_891596 baseEnd_891596 := by
    simpa [prefixWord, tailWord_891596, baseEnd_891596] using wordTrace_append hprefix tailTrace_891596
  have hstable : (prefixWord ++ tailWord_891596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891596).length < 2 ^ (prefixWord ++ tailWord_891596).sum := by decide
  have hdescent : baseEnd_891596 < baseStart_891596 := by decide
  rcases family_descends (prefixWord ++ tailWord_891596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891620 : List Nat := [2, 3, 1, 1, 1, 4, 2, 3, 3]
def baseStart_891620 : Nat := 118140960795 + 891620 * 2 ^ 59
def prefixEnd_891620 : Nat := 4983230072969 + 3 ^ 40 * 891620 * 2
def baseEnd_891620 : Nat := 406959663255028236755129

theorem tailTrace_891620 : CollatzResearch.WordTrace tailWord_891620 prefixEnd_891620 406959663255028236755129 := by
  unfold tailWord_891620
  simp only [CollatzResearch.WordTrace]
  refine ⟨16260026514910245708876157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21680035353213660945168209 16260026514910245708876157)
  ·
    refine ⟨6097509943091342140828559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16260026514910245708876157 6097509943091342140828559)
    ·
      refine ⟨9146264914637013211242839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6097509943091342140828559 9146264914637013211242839)
      ·
        refine ⟨13719397371955519816864259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9146264914637013211242839 13719397371955519816864259)
        ·
          refine ⟨20579096057933279725296389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13719397371955519816864259 20579096057933279725296389)
          ·
            refine ⟨3858580510862489948493073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20579096057933279725296389 3858580510862489948493073)
            ·
              refine ⟨2893935383146867461369805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3858580510862489948493073 2893935383146867461369805)
              ·
                refine ⟨1085225768680075298013677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2893935383146867461369805 1085225768680075298013677)
                ·
                  refine ⟨406959663255028236755129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1085225768680075298013677 406959663255028236755129)
                  ·
                    rfl

theorem cell20_891620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_891620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891620 prefixEnd_891620 := by exact prefixLift 891620
  have htrace : WordTrace (prefixWord ++ tailWord_891620) baseStart_891620 baseEnd_891620 := by
    simpa [prefixWord, tailWord_891620, baseEnd_891620] using wordTrace_append hprefix tailTrace_891620
  have hstable : (prefixWord ++ tailWord_891620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891620).length < 2 ^ (prefixWord ++ tailWord_891620).sum := by decide
  have hdescent : baseEnd_891620 < baseStart_891620 := by decide
  rcases family_descends (prefixWord ++ tailWord_891620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891644 : List Nat := [2, 2, 2, 1, 3, 2, 1, 5, 2]
def baseStart_891644 : Nat := 118140960795 + 891644 * 2 ^ 59
def prefixEnd_891644 : Nat := 4983230072969 + 3 ^ 40 * 891644 * 2
def baseEnd_891644 : Nat := 406970617508990819955031

theorem tailTrace_891644 : CollatzResearch.WordTrace tailWord_891644 prefixEnd_891644 406970617508990819955031 := by
  unfold tailWord_891644
  simp only [CollatzResearch.WordTrace]
  refine ⟨16260464190866771758312993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21680618921155695677750657 16260464190866771758312993)
  ·
    refine ⟨12195348143150078818734745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16260464190866771758312993 12195348143150078818734745)
    ·
      refine ⟨9146511107362559114051059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12195348143150078818734745 9146511107362559114051059)
      ·
        refine ⟨13719766661043838671076589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9146511107362559114051059 13719766661043838671076589)
        ·
          refine ⟨5144912497891439501653721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13719766661043838671076589 5144912497891439501653721)
          ·
            refine ⟨3858684373418579626240291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5144912497891439501653721 3858684373418579626240291)
            ·
              refine ⟨5788026560127869439360437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3858684373418579626240291 5788026560127869439360437)
              ·
                refine ⟨542627490011987759940041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5788026560127869439360437 542627490011987759940041)
                ·
                  refine ⟨406970617508990819955031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542627490011987759940041 406970617508990819955031)
                  ·
                    rfl

theorem cell20_891644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_891644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891644 prefixEnd_891644 := by exact prefixLift 891644
  have htrace : WordTrace (prefixWord ++ tailWord_891644) baseStart_891644 baseEnd_891644 := by
    simpa [prefixWord, tailWord_891644, baseEnd_891644] using wordTrace_append hprefix tailTrace_891644
  have hstable : (prefixWord ++ tailWord_891644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891644).length < 2 ^ (prefixWord ++ tailWord_891644).sum := by decide
  have hdescent : baseEnd_891644 < baseStart_891644 := by decide
  rcases family_descends (prefixWord ++ tailWord_891644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891699 : List Nat := [1, 1, 1, 2, 6, 3, 1, 3, 2]
def baseStart_891699 : Nat := 118140960795 + 891699 * 2 ^ 59
def prefixEnd_891699 : Nat := 4983230072969 + 3 ^ 40 * 891699 * 2
def baseEnd_891699 : Nat := 406995721007655073121473

theorem tailTrace_891699 : CollatzResearch.WordTrace tailWord_891699 prefixEnd_891699 406995721007655073121473 := by
  unfold tailWord_891699
  simp only [CollatzResearch.WordTrace]
  refine ⟨32522934396534287909878151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21681956264356191939918767 32522934396534287909878151)
  ·
    refine ⟨48784401594801431864817227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32522934396534287909878151 48784401594801431864817227)
    ·
      refine ⟨73176602392202147797225841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48784401594801431864817227 73176602392202147797225841)
      ·
        refine ⟨54882451794151610847919381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73176602392202147797225841 54882451794151610847919381)
        ·
          refine ⟨2572614927850856758496221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54882451794151610847919381 2572614927850856758496221)
          ·
            refine ⟨964730597944071284436083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2572614927850856758496221 964730597944071284436083)
            ·
              refine ⟨1447095896916106926654125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964730597944071284436083 1447095896916106926654125)
              ·
                refine ⟨542660961343540097495297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1447095896916106926654125 542660961343540097495297)
                ·
                  refine ⟨406995721007655073121473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542660961343540097495297 406995721007655073121473)
                  ·
                    rfl

theorem cell20_891699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 2].length) (baseStart_891699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891699 prefixEnd_891699 := by exact prefixLift 891699
  have htrace : WordTrace (prefixWord ++ tailWord_891699) baseStart_891699 baseEnd_891699 := by
    simpa [prefixWord, tailWord_891699, baseEnd_891699] using wordTrace_append hprefix tailTrace_891699
  have hstable : (prefixWord ++ tailWord_891699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891699).length < 2 ^ (prefixWord ++ tailWord_891699).sum := by decide
  have hdescent : baseEnd_891699 < baseStart_891699 := by decide
  rcases family_descends (prefixWord ++ tailWord_891699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891716 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 4]
def baseStart_891716 : Nat := 118140960795 + 891716 * 2 ^ 59
def prefixEnd_891716 : Nat := 4983230072969 + 3 ^ 40 * 891716 * 2
def baseEnd_891716 : Nat := 407003480270878569554737

theorem tailTrace_891716 : CollatzResearch.WordTrace tailWord_891716 prefixEnd_891716 407003480270878569554737 := by
  unfold tailWord_891716
  simp only [CollatzResearch.WordTrace]
  refine ⟨16261777218736349906623501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21682369624981799875498001 16261777218736349906623501)
  ·
    refine ⟨6098166457026131214983813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16261777218736349906623501 6098166457026131214983813)
    ·
      refine ⟨1143406210692399602809465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6098166457026131214983813 1143406210692399602809465)
      ·
        refine ⟨857554658019299702107099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1143406210692399602809465 857554658019299702107099)
        ·
          refine ⟨1286331987028949553160649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857554658019299702107099 1286331987028949553160649)
          ·
            refine ⟨964748990271712164870487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1286331987028949553160649 964748990271712164870487)
            ·
              refine ⟨1447123485407568247305731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964748990271712164870487 1447123485407568247305731)
              ·
                refine ⟨2170685228111352370958597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1447123485407568247305731 2170685228111352370958597)
                ·
                  refine ⟨407003480270878569554737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2170685228111352370958597 407003480270878569554737)
                  ·
                    rfl

theorem cell20_891716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_891716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891716 prefixEnd_891716 := by exact prefixLift 891716
  have htrace : WordTrace (prefixWord ++ tailWord_891716) baseStart_891716 baseEnd_891716 := by
    simpa [prefixWord, tailWord_891716, baseEnd_891716] using wordTrace_append hprefix tailTrace_891716
  have hstable : (prefixWord ++ tailWord_891716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891716).length < 2 ^ (prefixWord ++ tailWord_891716).sum := by decide
  have hdescent : baseEnd_891716 < baseStart_891716 := by decide
  rcases family_descends (prefixWord ++ tailWord_891716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891748 : List Nat := [2, 3, 1, 1, 4, 1, 2, 6]
def baseStart_891748 : Nat := 118140960795 + 891748 * 2 ^ 59
def prefixEnd_891748 : Nat := 4983230072969 + 3 ^ 40 * 891748 * 2
def baseEnd_891748 : Nat := 135672695314276226829313

theorem tailTrace_891748 : CollatzResearch.WordTrace tailWord_891748 prefixEnd_891748 135672695314276226829313 := by
  unfold tailWord_891748
  simp only [CollatzResearch.WordTrace]
  refine ⟨16262360786678384639205949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21683147715571179518941265 16262360786678384639205949)
  ·
    refine ⟨6098385295004394239702231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16262360786678384639205949 6098385295004394239702231)
    ·
      refine ⟨9147577942506591359553347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6098385295004394239702231 9147577942506591359553347)
      ·
        refine ⟨13721366913759887039330021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9147577942506591359553347 13721366913759887039330021)
        ·
          refine ⟨2572756296329978819874379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13721366913759887039330021 2572756296329978819874379)
          ·
            refine ⟨3859134444494968229811569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2572756296329978819874379 3859134444494968229811569)
            ·
              refine ⟨2894350833371226172358677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3859134444494968229811569 2894350833371226172358677)
              ·
                refine ⟨135672695314276226829313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2894350833371226172358677 135672695314276226829313)
                ·
                  rfl

theorem cell20_891748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_891748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891748 prefixEnd_891748 := by exact prefixLift 891748
  have htrace : WordTrace (prefixWord ++ tailWord_891748) baseStart_891748 baseEnd_891748 := by
    simpa [prefixWord, tailWord_891748, baseEnd_891748] using wordTrace_append hprefix tailTrace_891748
  have hstable : (prefixWord ++ tailWord_891748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891748).length < 2 ^ (prefixWord ++ tailWord_891748).sum := by decide
  have hdescent : baseEnd_891748 < baseStart_891748 := by decide
  rcases family_descends (prefixWord ++ tailWord_891748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891769 : List Nat := [1, 2, 1, 3, 2, 11]
def baseStart_891769 : Nat := 118140960795 + 891769 * 2 ^ 59
def prefixEnd_891769 : Nat := 4983230072969 + 3 ^ 40 * 891769 * 2
def baseEnd_891769 : Nat := 15075098922779479288439

theorem tailTrace_891769 : CollatzResearch.WordTrace tailWord_891769 prefixEnd_891769 15075098922779479288439 := by
  unfold tailWord_891769
  simp only [CollatzResearch.WordTrace]
  refine ⟨32525487506280689864926361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21683658337520459909950907 32525487506280689864926361)
  ·
    refine ⟨24394115629710517398694771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32525487506280689864926361 24394115629710517398694771)
    ·
      refine ⟨36591173444565776098042157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24394115629710517398694771 36591173444565776098042157)
      ·
        refine ⟨13721690041712166036765809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36591173444565776098042157 13721690041712166036765809)
        ·
          refine ⟨10291267531284124527574357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13721690041712166036765809 10291267531284124527574357)
          ·
            refine ⟨15075098922779479288439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10291267531284124527574357 15075098922779479288439)
            ·
              rfl

theorem cell20_891769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 11].length) (baseStart_891769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891769 prefixEnd_891769 := by exact prefixLift 891769
  have htrace : WordTrace (prefixWord ++ tailWord_891769) baseStart_891769 baseEnd_891769 := by
    simpa [prefixWord, tailWord_891769, baseEnd_891769] using wordTrace_append hprefix tailTrace_891769
  have hstable : (prefixWord ++ tailWord_891769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891769).length < 2 ^ (prefixWord ++ tailWord_891769).sum := by decide
  have hdescent : baseEnd_891769 < baseStart_891769 := by decide
  rcases family_descends (prefixWord ++ tailWord_891769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891778 : List Nat := [3, 4, 2, 2, 2, 1, 1, 5]
def baseStart_891778 : Nat := 118140960795 + 891778 * 2 ^ 59
def prefixEnd_891778 : Nat := 4983230072969 + 3 ^ 40 * 891778 * 2
def baseEnd_891778 : Nat := 135677259586760636495939

theorem tailTrace_891778 : CollatzResearch.WordTrace tailWord_891778 prefixEnd_891778 135677259586760636495939 := by
  unfold tailWord_891778
  simp only [CollatzResearch.WordTrace]
  refine ⟨8131453940812021100500997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21683877175498722934669325 8131453940812021100500997)
  ·
    refine ⟨1524647613902253956343937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8131453940812021100500997 1524647613902253956343937)
    ·
      refine ⟨1143485710426690467257953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1524647613902253956343937 1143485710426690467257953)
      ·
        refine ⟨857614282820017850443465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1143485710426690467257953 857614282820017850443465)
        ·
          refine ⟨643210712115013387832599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857614282820017850443465 643210712115013387832599)
          ·
            refine ⟨964816068172520081748899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643210712115013387832599 964816068172520081748899)
            ·
              refine ⟨1447224102258780122623349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964816068172520081748899 1447224102258780122623349)
              ·
                refine ⟨135677259586760636495939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1447224102258780122623349 135677259586760636495939)
                ·
                  rfl

theorem cell20_891778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_891778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891778 prefixEnd_891778 := by exact prefixLift 891778
  have htrace : WordTrace (prefixWord ++ tailWord_891778) baseStart_891778 baseEnd_891778 := by
    simpa [prefixWord, tailWord_891778, baseEnd_891778] using wordTrace_append hprefix tailTrace_891778
  have hstable : (prefixWord ++ tailWord_891778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891778).length < 2 ^ (prefixWord ++ tailWord_891778).sum := by decide
  have hdescent : baseEnd_891778 < baseStart_891778 := by decide
  rcases family_descends (prefixWord ++ tailWord_891778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891858 : List Nat := [3, 2, 2, 3, 1, 3, 2, 4]
def baseStart_891858 : Nat := 118140960795 + 891858 * 2 ^ 59
def prefixEnd_891858 : Nat := 4983230072969 + 3 ^ 40 * 891858 * 2
def baseEnd_891858 : Nat := 135689430980052395606941

theorem tailTrace_891858 : CollatzResearch.WordTrace tailWord_891858 prefixEnd_891858 135689430980052395606941 := by
  unfold tailWord_891858
  simp only [CollatzResearch.WordTrace]
  refine ⟨8132183400739564516229057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21685822401972172043277485 8132183400739564516229057)
  ·
    refine ⟨6099137550554673387171793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8132183400739564516229057 6099137550554673387171793)
    ·
      refine ⟨4574353162916005040378845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6099137550554673387171793 4574353162916005040378845)
      ·
        refine ⟨1715382436093501890142067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4574353162916005040378845 1715382436093501890142067)
        ·
          refine ⟨2573073654140252835213101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715382436093501890142067 2573073654140252835213101)
          ·
            refine ⟨964902620302594813204913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2573073654140252835213101 964902620302594813204913)
            ·
              refine ⟨723676965226946109903685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 964902620302594813204913 723676965226946109903685)
              ·
                refine ⟨135689430980052395606941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 723676965226946109903685 135689430980052395606941)
                ·
                  rfl

theorem cell20_891858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_891858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891858 prefixEnd_891858 := by exact prefixLift 891858
  have htrace : WordTrace (prefixWord ++ tailWord_891858) baseStart_891858 baseEnd_891858 := by
    simpa [prefixWord, tailWord_891858, baseEnd_891858] using wordTrace_append hprefix tailTrace_891858
  have hstable : (prefixWord ++ tailWord_891858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891858).length < 2 ^ (prefixWord ++ tailWord_891858).sum := by decide
  have hdescent : baseEnd_891858 < baseStart_891858 := by decide
  rcases family_descends (prefixWord ++ tailWord_891858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891889 : List Nat := [1, 2, 2, 2, 4, 2, 3, 2, 2]
def baseStart_891889 : Nat := 118140960795 + 891889 * 2 ^ 59
def prefixEnd_891889 : Nat := 4983230072969 + 3 ^ 40 * 891889 * 2
def baseEnd_891889 : Nat := 407082442184858856787363

theorem tailTrace_891889 : CollatzResearch.WordTrace tailWord_891889 prefixEnd_891889 407082442184858856787363 := by
  unfold tailWord_891889
  simp only [CollatzResearch.WordTrace]
  refine ⟨32529864265845950359294721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21686576177230633572863147 32529864265845950359294721)
  ·
    refine ⟨24397398199384462769471041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32529864265845950359294721 24397398199384462769471041)
    ·
      refine ⟨18298048649538347077103281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24397398199384462769471041 18298048649538347077103281)
      ·
        refine ⟨13723536487153760307827461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18298048649538347077103281 13723536487153760307827461)
        ·
          refine ⟨2573163091341330057717649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13723536487153760307827461 2573163091341330057717649)
          ·
            refine ⟨1929872318505997543288237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2573163091341330057717649 1929872318505997543288237)
            ·
              refine ⟨723702119439749078733089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1929872318505997543288237 723702119439749078733089)
              ·
                refine ⟨542776589579811809049817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723702119439749078733089 542776589579811809049817)
                ·
                  refine ⟨407082442184858856787363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542776589579811809049817 407082442184858856787363)
                  ·
                    rfl

theorem cell20_891889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 2].length) (baseStart_891889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891889 prefixEnd_891889 := by exact prefixLift 891889
  have htrace : WordTrace (prefixWord ++ tailWord_891889) baseStart_891889 baseEnd_891889 := by
    simpa [prefixWord, tailWord_891889, baseEnd_891889] using wordTrace_append hprefix tailTrace_891889
  have hstable : (prefixWord ++ tailWord_891889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891889).length < 2 ^ (prefixWord ++ tailWord_891889).sum := by decide
  have hdescent : baseEnd_891889 < baseStart_891889 := by decide
  rcases family_descends (prefixWord ++ tailWord_891889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891892 : List Nat := [2, 6, 2, 1, 1, 1, 2, 5]
def baseStart_891892 : Nat := 118140960795 + 891892 * 2 ^ 59
def prefixEnd_891892 : Nat := 4983230072969 + 3 ^ 40 * 891892 * 2
def baseEnd_891892 : Nat := 135694603822201393229117

theorem tailTrace_891892 : CollatzResearch.WordTrace tailWord_891892 prefixEnd_891892 135694603822201393229117 := by
  unfold tailWord_891892
  simp only [CollatzResearch.WordTrace]
  refine ⟨16264986842417540935826965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21686649123223387914435953 16264986842417540935826965)
  ·
    refine ⟨762421258238322231366889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16264986842417540935826965 762421258238322231366889)
    ·
      refine ⟨571815943678741673525167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 762421258238322231366889 571815943678741673525167)
      ·
        refine ⟨857723915518112510287751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571815943678741673525167 857723915518112510287751)
        ·
          refine ⟨1286585873277168765431627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857723915518112510287751 1286585873277168765431627)
          ·
            refine ⟨1929878809915753148147441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286585873277168765431627 1929878809915753148147441)
            ·
              refine ⟨1447409107436814861110581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1929878809915753148147441 1447409107436814861110581)
              ·
                refine ⟨135694603822201393229117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1447409107436814861110581 135694603822201393229117)
                ·
                  rfl

theorem cell20_891892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_891892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891892 prefixEnd_891892 := by exact prefixLift 891892
  have htrace : WordTrace (prefixWord ++ tailWord_891892) baseStart_891892 baseEnd_891892 := by
    simpa [prefixWord, tailWord_891892, baseEnd_891892] using wordTrace_append hprefix tailTrace_891892
  have hstable : (prefixWord ++ tailWord_891892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891892).length < 2 ^ (prefixWord ++ tailWord_891892).sum := by decide
  have hdescent : baseEnd_891892 < baseStart_891892 := by decide
  rcases family_descends (prefixWord ++ tailWord_891892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891900 : List Nat := [2, 2, 2, 1, 2, 4, 2, 5]
def baseStart_891900 : Nat := 118140960795 + 891900 * 2 ^ 59
def prefixEnd_891900 : Nat := 4983230072969 + 3 ^ 40 * 891900 * 2
def baseEnd_891900 : Nat := 135695820961530569140217

theorem tailTrace_891900 : CollatzResearch.WordTrace tailWord_891900 prefixEnd_891900 135695820961530569140217 := by
  unfold tailWord_891900
  simp only [CollatzResearch.WordTrace]
  refine ⟨16265132734403049618972577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21686843645870732825296769 16265132734403049618972577)
  ·
    refine ⟨12198849550802287214229433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16265132734403049618972577 12198849550802287214229433)
    ·
      refine ⟨9149137163101715410672075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12198849550802287214229433 9149137163101715410672075)
      ·
        refine ⟨13723705744652573116008113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9149137163101715410672075 13723705744652573116008113)
        ·
          refine ⟨10292779308489429837006085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13723705744652573116008113 10292779308489429837006085)
          ·
            refine ⟨1929896120341768094438641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10292779308489429837006085 1929896120341768094438641)
            ·
              refine ⟨1447422090256326070828981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1929896120341768094438641 1447422090256326070828981)
              ·
                refine ⟨135695820961530569140217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1447422090256326070828981 135695820961530569140217)
                ·
                  rfl

theorem cell20_891900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_891900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891900 prefixEnd_891900 := by exact prefixLift 891900
  have htrace : WordTrace (prefixWord ++ tailWord_891900) baseStart_891900 baseEnd_891900 := by
    simpa [prefixWord, tailWord_891900, baseEnd_891900] using wordTrace_append hprefix tailTrace_891900
  have hstable : (prefixWord ++ tailWord_891900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891900).length < 2 ^ (prefixWord ++ tailWord_891900).sum := by decide
  have hdescent : baseEnd_891900 < baseStart_891900 := by decide
  rcases family_descends (prefixWord ++ tailWord_891900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891952 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 4]
def baseStart_891952 : Nat := 118140960795 + 891952 * 2 ^ 59
def prefixEnd_891952 : Nat := 4983230072969 + 3 ^ 40 * 891952 * 2
def baseEnd_891952 : Nat := 407111197101510637687105

theorem tailTrace_891952 : CollatzResearch.WordTrace tailWord_891952 prefixEnd_891952 407111197101510637687105 := by
  unfold tailWord_891952
  simp only [CollatzResearch.WordTrace]
  refine ⟨16266081032308856059419055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21688108043078474745892073 16266081032308856059419055)
  ·
    refine ⟨24399121548463284089128583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16266081032308856059419055 24399121548463284089128583)
    ·
      refine ⟨36598682322694926133692875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24399121548463284089128583 36598682322694926133692875)
      ·
        refine ⟨54898023484042389200539313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36598682322694926133692875 54898023484042389200539313)
        ·
          refine ⟨41173517613031791900404485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54898023484042389200539313 41173517613031791900404485)
          ·
            refine ⟨7720034552443460981325841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41173517613031791900404485 7720034552443460981325841)
            ·
              refine ⟨5790025914332595735994381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7720034552443460981325841 5790025914332595735994381)
              ·
                refine ⟨2171259717874723400997893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5790025914332595735994381 2171259717874723400997893)
                ·
                  refine ⟨407111197101510637687105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2171259717874723400997893 407111197101510637687105)
                  ·
                    rfl

theorem cell20_891952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_891952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891952 prefixEnd_891952 := by exact prefixLift 891952
  have htrace : WordTrace (prefixWord ++ tailWord_891952) baseStart_891952 baseEnd_891952 := by
    simpa [prefixWord, tailWord_891952, baseEnd_891952] using wordTrace_append hprefix tailTrace_891952
  have hstable : (prefixWord ++ tailWord_891952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891952).length < 2 ^ (prefixWord ++ tailWord_891952).sum := by decide
  have hdescent : baseEnd_891952 < baseStart_891952 := by decide
  rcases family_descends (prefixWord ++ tailWord_891952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891976 : List Nat := [2, 1, 3, 1, 1, 1, 7, 4]
def baseStart_891976 : Nat := 118140960795 + 891976 * 2 ^ 59
def prefixEnd_891976 : Nat := 4983230072969 + 3 ^ 40 * 891976 * 2
def baseEnd_891976 : Nat := 135707383785157740295669

theorem tailTrace_891976 : CollatzResearch.WordTrace tailWord_891976 prefixEnd_891976 135707383785157740295669 := by
  unfold tailWord_891976
  simp only [CollatzResearch.WordTrace]
  refine ⟨16266518708265382108855891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21688691611020509478474521 16266518708265382108855891)
  ·
    refine ⟨24399778062398073163283837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16266518708265382108855891 24399778062398073163283837)
    ·
      refine ⟨9149916773399277436231439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24399778062398073163283837 9149916773399277436231439)
      ·
        refine ⟨13724875160098916154347159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9149916773399277436231439 13724875160098916154347159)
        ·
          refine ⟨20587312740148374231520739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13724875160098916154347159 20587312740148374231520739)
          ·
            refine ⟨30880969110222561347281109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20587312740148374231520739 30880969110222561347281109)
            ·
              refine ⟨723772713520841281576901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30880969110222561347281109 723772713520841281576901)
              ·
                refine ⟨135707383785157740295669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 723772713520841281576901 135707383785157740295669)
                ·
                  rfl

theorem cell20_891976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_891976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891976 prefixEnd_891976 := by exact prefixLift 891976
  have htrace : WordTrace (prefixWord ++ tailWord_891976) baseStart_891976 baseEnd_891976 := by
    simpa [prefixWord, tailWord_891976, baseEnd_891976] using wordTrace_append hprefix tailTrace_891976
  have hstable : (prefixWord ++ tailWord_891976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891976).length < 2 ^ (prefixWord ++ tailWord_891976).sum := by decide
  have hdescent : baseEnd_891976 < baseStart_891976 := by decide
  rcases family_descends (prefixWord ++ tailWord_891976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891986 : List Nat := [3, 2, 2, 1, 3, 1, 1, 5, 2]
def baseStart_891986 : Nat := 118140960795 + 891986 * 2 ^ 59
def prefixEnd_891986 : Nat := 4983230072969 + 3 ^ 40 * 891986 * 2
def baseEnd_891986 : Nat := 407126715627957630553633

theorem tailTrace_891986 : CollatzResearch.WordTrace tailWord_891986 prefixEnd_891986 407126715627957630553633 := by
  unfold tailWord_891986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8133350536623633981393953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21688934764329690617050541 8133350536623633981393953)
  ·
    refine ⟨6100012902467725486045465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8133350536623633981393953 6100012902467725486045465)
    ·
      refine ⟨4575009676850794114534099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6100012902467725486045465 4575009676850794114534099)
      ·
        refine ⟨6862514515276191171801149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4575009676850794114534099 6862514515276191171801149)
        ·
          refine ⟨2573442943228571689425431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6862514515276191171801149 2573442943228571689425431)
          ·
            refine ⟨3860164414842857534138147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573442943228571689425431 3860164414842857534138147)
            ·
              refine ⟨5790246622264286301207221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3860164414842857534138147 5790246622264286301207221)
              ·
                refine ⟨542835620837276840738177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5790246622264286301207221 542835620837276840738177)
                ·
                  refine ⟨407126715627957630553633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542835620837276840738177 407126715627957630553633)
                  ·
                    rfl

theorem cell20_891986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_891986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_891986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_891986 prefixEnd_891986 := by exact prefixLift 891986
  have htrace : WordTrace (prefixWord ++ tailWord_891986) baseStart_891986 baseEnd_891986 := by
    simpa [prefixWord, tailWord_891986, baseEnd_891986] using wordTrace_append hprefix tailTrace_891986
  have hstable : (prefixWord ++ tailWord_891986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891986).length < 2 ^ (prefixWord ++ tailWord_891986).sum := by decide
  have hdescent : baseEnd_891986 < baseStart_891986 := by decide
  rcases family_descends (prefixWord ++ tailWord_891986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892007 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 4]
def baseStart_892007 : Nat := 118140960795 + 892007 * 2 ^ 59
def prefixEnd_892007 : Nat := 4983230072969 + 3 ^ 40 * 892007 * 2
def baseEnd_892007 : Nat := 407136300600174890853547

theorem tailTrace_892007 : CollatzResearch.WordTrace tailWord_892007 prefixEnd_892007 407136300600174890853547 := by
  unfold tailWord_892007
  simp only [CollatzResearch.WordTrace]
  refine ⟨32534168079418456512090275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21689445386278971008060183 32534168079418456512090275)
  ·
    refine ⟨48801252119127684768135413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32534168079418456512090275 48801252119127684768135413)
    ·
      refine ⟨4575117386168220447012695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48801252119127684768135413 4575117386168220447012695)
      ·
        refine ⟨6862676079252330670519043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4575117386168220447012695 6862676079252330670519043)
        ·
          refine ⟨10294014118878496005778565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6862676079252330670519043 10294014118878496005778565)
          ·
            refine ⟨1930127647289718001083481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10294014118878496005778565 1930127647289718001083481)
            ·
              refine ⟨1447595735467288500812611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1930127647289718001083481 1447595735467288500812611)
              ·
                refine ⟨2171393603200932751218917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1447595735467288500812611 2171393603200932751218917)
                ·
                  refine ⟨407136300600174890853547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2171393603200932751218917 407136300600174890853547)
                  ·
                    rfl

theorem cell20_892007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 4].length) (baseStart_892007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892007 prefixEnd_892007 := by exact prefixLift 892007
  have htrace : WordTrace (prefixWord ++ tailWord_892007) baseStart_892007 baseEnd_892007 := by
    simpa [prefixWord, tailWord_892007, baseEnd_892007] using wordTrace_append hprefix tailTrace_892007
  have hstable : (prefixWord ++ tailWord_892007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892007).length < 2 ^ (prefixWord ++ tailWord_892007).sum := by decide
  have hdescent : baseEnd_892007 < baseStart_892007 := by decide
  rcases family_descends (prefixWord ++ tailWord_892007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892028 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 4]
def baseStart_892028 : Nat := 118140960795 + 892028 * 2 ^ 59
def prefixEnd_892028 : Nat := 4983230072969 + 3 ^ 40 * 892028 * 2
def baseEnd_892028 : Nat := 407145885572392151153461

theorem tailTrace_892028 : CollatzResearch.WordTrace tailWord_892028 prefixEnd_892028 407145885572392151153461 := by
  unfold tailWord_892028
  simp only [CollatzResearch.WordTrace]
  refine ⟨16267467006171188549302369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21689956008228251399069825 16267467006171188549302369)
  ·
    refine ⟨12200600254628391411976777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16267467006171188549302369 12200600254628391411976777)
    ·
      refine ⟨9150450190971293558982583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12200600254628391411976777 9150450190971293558982583)
      ·
        refine ⟨13725675286456940338473875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9150450190971293558982583 13725675286456940338473875)
        ·
          refine ⟨20588512929685410507710813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13725675286456940338473875 20588512929685410507710813)
          ·
            refine ⟨7720692348632028940391555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20588512929685410507710813 7720692348632028940391555)
            ·
              refine ⟨11581038522948043410587333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7720692348632028940391555 11581038522948043410587333)
              ·
                refine ⟨2171444723052758139485125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11581038522948043410587333 2171444723052758139485125)
                ·
                  refine ⟨407145885572392151153461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2171444723052758139485125 407145885572392151153461)
                  ·
                    rfl

theorem cell20_892028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_892028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892028 prefixEnd_892028 := by exact prefixLift 892028
  have htrace : WordTrace (prefixWord ++ tailWord_892028) baseStart_892028 baseEnd_892028 := by
    simpa [prefixWord, tailWord_892028, baseEnd_892028] using wordTrace_append hprefix tailTrace_892028
  have hstable : (prefixWord ++ tailWord_892028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892028).length < 2 ^ (prefixWord ++ tailWord_892028).sum := by decide
  have hdescent : baseEnd_892028 < baseStart_892028 := by decide
  rcases family_descends (prefixWord ++ tailWord_892028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892035 : List Nat := [1, 1, 1, 3, 3, 2, 3, 6]
def baseStart_892035 : Nat := 118140960795 + 892035 * 2 ^ 59
def prefixEnd_892035 : Nat := 4983230072969 + 3 ^ 40 * 892035 * 2
def baseEnd_892035 : Nat := 135716360187710412640033

theorem tailTrace_892035 : CollatzResearch.WordTrace tailWord_892035 prefixEnd_892035 135716360187710412640033 := by
  unfold tailWord_892035
  simp only [CollatzResearch.WordTrace]
  refine ⟨32535189323317017294109559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21690126215544678196073039 32535189323317017294109559)
  ·
    refine ⟨48802783984975525941164339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32535189323317017294109559 48802783984975525941164339)
    ·
      refine ⟨73204175977463288911746509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48802783984975525941164339 73204175977463288911746509)
      ·
        refine ⟨27451565991548733341904941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73204175977463288911746509 27451565991548733341904941)
        ·
          refine ⟨10294337246830775003214353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27451565991548733341904941 10294337246830775003214353)
          ·
            refine ⟨7720752935123081252410765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10294337246830775003214353 7720752935123081252410765)
            ·
              refine ⟨2895282350671155469654037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7720752935123081252410765 2895282350671155469654037)
              ·
                refine ⟨135716360187710412640033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2895282350671155469654037 135716360187710412640033)
                ·
                  rfl

theorem cell20_892035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 6].length) (baseStart_892035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892035 prefixEnd_892035 := by exact prefixLift 892035
  have htrace : WordTrace (prefixWord ++ tailWord_892035) baseStart_892035 baseEnd_892035 := by
    simpa [prefixWord, tailWord_892035, baseEnd_892035] using wordTrace_append hprefix tailTrace_892035
  have hstable : (prefixWord ++ tailWord_892035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892035).length < 2 ^ (prefixWord ++ tailWord_892035).sum := by decide
  have hdescent : baseEnd_892035 < baseStart_892035 := by decide
  rcases family_descends (prefixWord ++ tailWord_892035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892062 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_892062 : Nat := 118140960795 + 892062 * 2 ^ 59
def prefixEnd_892062 : Nat := 4983230072969 + 3 ^ 40 * 892062 * 2
def baseEnd_892062 : Nat := 407161404098839144019989

theorem tailTrace_892062 : CollatzResearch.WordTrace tailWord_892062 prefixEnd_892062 407161404098839144019989 := by
  unfold tailWord_892062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4067021761777400113167805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21690782729479467270228293 4067021761777400113167805)
  ·
    refine ⟨1525133160666525042437927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4067021761777400113167805 1525133160666525042437927)
    ·
      refine ⟨2287699740999787563656891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1525133160666525042437927 2287699740999787563656891)
      ·
        refine ⟨3431549611499681345485337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2287699740999787563656891 3431549611499681345485337)
        ·
          refine ⟨2573662208624761009114003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3431549611499681345485337 2573662208624761009114003)
          ·
            refine ⟨3860493312937141513671005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573662208624761009114003 3860493312937141513671005)
            ·
              refine ⟨1447684992351428067626627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3860493312937141513671005 1447684992351428067626627)
              ·
                refine ⟨2171527488527142101439941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1447684992351428067626627 2171527488527142101439941)
                ·
                  refine ⟨407161404098839144019989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2171527488527142101439941 407161404098839144019989)
                  ·
                    rfl

theorem cell20_892062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_892062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892062 prefixEnd_892062 := by exact prefixLift 892062
  have htrace : WordTrace (prefixWord ++ tailWord_892062) baseStart_892062 baseEnd_892062 := by
    simpa [prefixWord, tailWord_892062, baseEnd_892062] using wordTrace_append hprefix tailTrace_892062
  have hstable : (prefixWord ++ tailWord_892062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892062).length < 2 ^ (prefixWord ++ tailWord_892062).sum := by decide
  have hdescent : baseEnd_892062 < baseStart_892062 := by decide
  rcases family_descends (prefixWord ++ tailWord_892062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892114 : List Nat := [3, 2, 2, 2, 1, 1, 4, 2, 3]
def baseStart_892114 : Nat := 118140960795 + 892114 * 2 ^ 59
def prefixEnd_892114 : Nat := 4983230072969 + 3 ^ 40 * 892114 * 2
def baseEnd_892114 : Nat := 407185138315758074286443

theorem tailTrace_892114 : CollatzResearch.WordTrace tailWord_892114 prefixEnd_892114 407185138315758074286443 := by
  unfold tailWord_892114
  simp only [CollatzResearch.WordTrace]
  refine ⟨8134517672507703446558849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21692047126687209190823597 8134517672507703446558849)
  ·
    refine ⟨6100888254380777584919137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8134517672507703446558849 6100888254380777584919137)
    ·
      refine ⟨4575666190785583188689353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6100888254380777584919137 4575666190785583188689353)
      ·
        refine ⟨3431749643089187391517015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4575666190785583188689353 3431749643089187391517015)
        ·
          refine ⟨5147624464633781087275523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3431749643089187391517015 5147624464633781087275523)
          ·
            refine ⟨7721436696950671630913285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5147624464633781087275523 7721436696950671630913285)
            ·
              refine ⟨1447769380678250930796241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7721436696950671630913285 1447769380678250930796241)
              ·
                refine ⟨1085827035508688198097181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1447769380678250930796241 1085827035508688198097181)
                ·
                  refine ⟨407185138315758074286443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1085827035508688198097181 407185138315758074286443)
                  ·
                    rfl

theorem cell20_892114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_892114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892114 prefixEnd_892114 := by exact prefixLift 892114
  have htrace : WordTrace (prefixWord ++ tailWord_892114) baseStart_892114 baseEnd_892114 := by
    simpa [prefixWord, tailWord_892114, baseEnd_892114] using wordTrace_append hprefix tailTrace_892114
  have hstable : (prefixWord ++ tailWord_892114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892114).length < 2 ^ (prefixWord ++ tailWord_892114).sum := by decide
  have hdescent : baseEnd_892114 < baseStart_892114 := by decide
  rcases family_descends (prefixWord ++ tailWord_892114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892117 : List Nat := [1, 3, 2, 4, 1, 1, 4, 2, 2]
def baseStart_892117 : Nat := 118140960795 + 892117 * 2 ^ 59
def prefixEnd_892117 : Nat := 4983230072969 + 3 ^ 40 * 892117 * 2
def baseEnd_892117 : Nat := 407186507597503397186431

theorem tailTrace_892117 : CollatzResearch.WordTrace tailWord_892117 prefixEnd_892117 407186507597503397186431 := by
  unfold tailWord_892117
  simp only [CollatzResearch.WordTrace]
  refine ⟨32538180109019945298594605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21692120072679963532396403 32538180109019945298594605)
  ·
    refine ⟨12201817540882479486972977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32538180109019945298594605 12201817540882479486972977)
    ·
      refine ⟨9151363155661859615229733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12201817540882479486972977 9151363155661859615229733)
      ·
        refine ⟨1715880591686598677855575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9151363155661859615229733 1715880591686598677855575)
        ·
          refine ⟨2573820887529898016783363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715880591686598677855575 2573820887529898016783363)
          ·
            refine ⟨3860731331294847025175045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573820887529898016783363 3860731331294847025175045)
            ·
              refine ⟨723887124617783817220321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3860731331294847025175045 723887124617783817220321)
              ·
                refine ⟨542915343463337862915241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723887124617783817220321 542915343463337862915241)
                ·
                  refine ⟨407186507597503397186431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542915343463337862915241 407186507597503397186431)
                  ·
                    rfl

theorem cell20_892117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_892117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892117 prefixEnd_892117 := by exact prefixLift 892117
  have htrace : WordTrace (prefixWord ++ tailWord_892117) baseStart_892117 baseEnd_892117 := by
    simpa [prefixWord, tailWord_892117, baseEnd_892117] using wordTrace_append hprefix tailTrace_892117
  have hstable : (prefixWord ++ tailWord_892117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892117).length < 2 ^ (prefixWord ++ tailWord_892117).sum := by decide
  have hdescent : baseEnd_892117 < baseStart_892117 := by decide
  rcases family_descends (prefixWord ++ tailWord_892117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892128 : List Nat := [2, 1, 1, 3, 1, 6, 1, 5]
def baseStart_892128 : Nat := 118140960795 + 892128 * 2 ^ 59
def prefixEnd_892128 : Nat := 4983230072969 + 3 ^ 40 * 892128 * 2
def baseEnd_892128 : Nat := 135730509432412082606573

theorem tailTrace_892128 : CollatzResearch.WordTrace tailWord_892128 prefixEnd_892128 135730509432412082606573 := by
  unfold tailWord_892128
  simp only [CollatzResearch.WordTrace]
  refine ⟨16269290655990047088622519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21692387541320062784830025 16269290655990047088622519)
  ·
    refine ⟨24403935983985070632933779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16269290655990047088622519 24403935983985070632933779)
    ·
      refine ⟨36605903975977605949400669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24403935983985070632933779 36605903975977605949400669)
      ·
        refine ⟨13727213990991602231025251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36605903975977605949400669 13727213990991602231025251)
        ·
          refine ⟨20590820986487403346537877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13727213990991602231025251 20590820986487403346537877)
          ·
            refine ⟨965194733741597031868963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20590820986487403346537877 965194733741597031868963)
            ·
              refine ⟨1447792100612395547803445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965194733741597031868963 1447792100612395547803445)
              ·
                refine ⟨135730509432412082606573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1447792100612395547803445 135730509432412082606573)
                ·
                  rfl

theorem cell20_892128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_892128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892128 prefixEnd_892128 := by exact prefixLift 892128
  have htrace : WordTrace (prefixWord ++ tailWord_892128) baseStart_892128 baseEnd_892128 := by
    simpa [prefixWord, tailWord_892128, baseEnd_892128] using wordTrace_append hprefix tailTrace_892128
  have hstable : (prefixWord ++ tailWord_892128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892128).length < 2 ^ (prefixWord ++ tailWord_892128).sum := by decide
  have hdescent : baseEnd_892128 < baseStart_892128 := by decide
  rcases family_descends (prefixWord ++ tailWord_892128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892142 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_892142 : Nat := 118140960795 + 892142 * 2 ^ 59
def prefixEnd_892142 : Nat := 4983230072969 + 3 ^ 40 * 892142 * 2
def baseEnd_892142 : Nat := 407197918278714421352995

theorem tailTrace_892142 : CollatzResearch.WordTrace tailWord_892142 prefixEnd_892142 407197918278714421352995 := by
  unfold tailWord_892142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4067386491741171821031835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21692727955952916378836453 4067386491741171821031835)
  ·
    refine ⟨6101079737611757731547753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4067386491741171821031835 6101079737611757731547753)
    ·
      refine ⟨4575809803208818298660815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6101079737611757731547753 4575809803208818298660815)
      ·
        refine ⟨6863714704813227447991223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4575809803208818298660815 6863714704813227447991223)
        ·
          refine ⟨10295572057219841171986835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6863714704813227447991223 10295572057219841171986835)
          ·
            refine ⟨15443358085829761757980253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10295572057219841171986835 15443358085829761757980253)
            ·
              refine ⟨5791259282186160659242595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15443358085829761757980253 5791259282186160659242595)
              ·
                refine ⟨8686888923279240988863893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5791259282186160659242595 8686888923279240988863893)
                ·
                  refine ⟨407197918278714421352995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8686888923279240988863893 407197918278714421352995)
                  ·
                    rfl

theorem cell20_892142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_892142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892142 prefixEnd_892142 := by exact prefixLift 892142
  have htrace : WordTrace (prefixWord ++ tailWord_892142) baseStart_892142 baseEnd_892142 := by
    simpa [prefixWord, tailWord_892142, baseEnd_892142] using wordTrace_append hprefix tailTrace_892142
  have hstable : (prefixWord ++ tailWord_892142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892142).length < 2 ^ (prefixWord ++ tailWord_892142).sum := by decide
  have hdescent : baseEnd_892142 < baseStart_892142 := by decide
  rcases family_descends (prefixWord ++ tailWord_892142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892159 : List Nat := [1, 1, 2, 2, 1, 5, 1, 5, 2]
def baseStart_892159 : Nat := 118140960795 + 892159 * 2 ^ 59
def prefixEnd_892159 : Nat := 4983230072969 + 3 ^ 40 * 892159 * 2
def baseEnd_892159 : Nat := 407205677541937917786259

theorem tailTrace_892159 : CollatzResearch.WordTrace tailWord_892159 prefixEnd_892159 407205677541937917786259 := by
  unfold tailWord_892159
  simp only [CollatzResearch.WordTrace]
  refine ⟨32539711974867786471623531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21693141316578524314415687 32539711974867786471623531)
  ·
    refine ⟨48809567962301679707435297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32539711974867786471623531 48809567962301679707435297)
    ·
      refine ⟨36607175971726259780576473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48809567962301679707435297 36607175971726259780576473)
      ·
        refine ⟨27455381978794694835432355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36607175971726259780576473 27455381978794694835432355)
        ·
          refine ⟨41183072968192042253148533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27455381978794694835432355 41183072968192042253148533)
          ·
            refine ⟨3860913090768003961232675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41183072968192042253148533 3860913090768003961232675)
            ·
              refine ⟨5791369636152005941849013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3860913090768003961232675 5791369636152005941849013)
              ·
                refine ⟨542940903389250557048345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5791369636152005941849013 542940903389250557048345)
                ·
                  refine ⟨407205677541937917786259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542940903389250557048345 407205677541937917786259)
                  ·
                    rfl

theorem cell20_892159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 2].length) (baseStart_892159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892159 prefixEnd_892159 := by exact prefixLift 892159
  have htrace : WordTrace (prefixWord ++ tailWord_892159) baseStart_892159 baseEnd_892159 := by
    simpa [prefixWord, tailWord_892159, baseEnd_892159] using wordTrace_append hprefix tailTrace_892159
  have hstable : (prefixWord ++ tailWord_892159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892159).length < 2 ^ (prefixWord ++ tailWord_892159).sum := by decide
  have hdescent : baseEnd_892159 < baseStart_892159 := by decide
  rcases family_descends (prefixWord ++ tailWord_892159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892201 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 10]
def baseStart_892201 : Nat := 118140960795 + 892201 * 2 ^ 59
def prefixEnd_892201 : Nat := 4983230072969 + 3 ^ 40 * 892201 * 2
def baseEnd_892201 : Nat := 407224847486372438386087

theorem tailTrace_892201 : CollatzResearch.WordTrace tailWord_892201 prefixEnd_892201 407224847486372438386087 := by
  unfold tailWord_892201
  simp only [CollatzResearch.WordTrace]
  refine ⟨32541243840715627644652457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21694162560477085096434971 32541243840715627644652457)
  ·
    refine ⟨24405932880536720733489343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32541243840715627644652457 24405932880536720733489343)
    ·
      refine ⟨36608899320805081100234015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24405932880536720733489343 36608899320805081100234015)
      ·
        refine ⟨54913348981207621650351023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36608899320805081100234015 54913348981207621650351023)
        ·
          refine ⟨82370023471811432475526535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54913348981207621650351023 82370023471811432475526535)
          ·
            refine ⟨123555035207717148713289803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82370023471811432475526535 123555035207717148713289803)
            ·
              refine ⟨185332552811575723069934705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123555035207717148713289803 185332552811575723069934705)
              ·
                refine ⟨138999414608681792302451029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185332552811575723069934705 138999414608681792302451029)
                ·
                  refine ⟨407224847486372438386087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 138999414608681792302451029 407224847486372438386087)
                  ·
                    rfl

theorem cell20_892201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_892201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892201 prefixEnd_892201 := by exact prefixLift 892201
  have htrace : WordTrace (prefixWord ++ tailWord_892201) baseStart_892201 baseEnd_892201 := by
    simpa [prefixWord, tailWord_892201, baseEnd_892201] using wordTrace_append hprefix tailTrace_892201
  have hstable : (prefixWord ++ tailWord_892201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892201).length < 2 ^ (prefixWord ++ tailWord_892201).sum := by decide
  have hdescent : baseEnd_892201 < baseStart_892201 := by decide
  rcases family_descends (prefixWord ++ tailWord_892201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892221 : List Nat := [1, 4, 1, 5, 1, 2, 6]
def baseStart_892221 : Nat := 118140960795 + 892221 * 2 ^ 59
def prefixEnd_892221 : Nat := 4983230072969 + 3 ^ 40 * 892221 * 2
def baseEnd_892221 : Nat := 45248219559037917524371

theorem tailTrace_892221 : CollatzResearch.WordTrace tailWord_892221 prefixEnd_892221 45248219559037917524371 := by
  unfold tailWord_892221
  simp only [CollatzResearch.WordTrace]
  refine ⟨32541973300643171060380517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21694648867095447373587011 32541973300643171060380517)
  ·
    refine ⟨6101619993870594573821347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32541973300643171060380517 6101619993870594573821347)
    ·
      refine ⟨9152429990805891860732021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6101619993870594573821347 9152429990805891860732021)
      ·
        refine ⟨858040311638052361943627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9152429990805891860732021 858040311638052361943627)
        ·
          refine ⟨1287060467457078542915441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858040311638052361943627 1287060467457078542915441)
          ·
            refine ⟨965295350592808907186581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1287060467457078542915441 965295350592808907186581)
            ·
              refine ⟨45248219559037917524371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 965295350592808907186581 45248219559037917524371)
              ·
                rfl

theorem cell20_892221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 6].length) (baseStart_892221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892221 prefixEnd_892221 := by exact prefixLift 892221
  have htrace : WordTrace (prefixWord ++ tailWord_892221) baseStart_892221 baseEnd_892221 := by
    simpa [prefixWord, tailWord_892221, baseEnd_892221] using wordTrace_append hprefix tailTrace_892221
  have hstable : (prefixWord ++ tailWord_892221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892221).length < 2 ^ (prefixWord ++ tailWord_892221).sum := by decide
  have hdescent : baseEnd_892221 < baseStart_892221 := by decide
  rcases family_descends (prefixWord ++ tailWord_892221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892228 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 5]
def baseStart_892228 : Nat := 118140960795 + 892228 * 2 ^ 59
def prefixEnd_892228 : Nat := 4983230072969 + 3 ^ 40 * 892228 * 2
def baseEnd_892228 : Nat := 407237171022080344485977

theorem tailTrace_892228 : CollatzResearch.WordTrace tailWord_892228 prefixEnd_892228 407237171022080344485977 := by
  unfold tailWord_892228
  simp only [CollatzResearch.WordTrace]
  refine ⟨16271114305808905627942669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21694819074411874170590225 16271114305808905627942669)
  ·
    refine ⟨6101667864678339610478501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16271114305808905627942669 6101667864678339610478501)
    ·
      refine ⟨1144062724627188676964719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6101667864678339610478501 1144062724627188676964719)
      ·
        refine ⟨1716094086940783015447079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1144062724627188676964719 1716094086940783015447079)
        ·
          refine ⟨2574141130411174523170619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716094086940783015447079 2574141130411174523170619)
          ·
            refine ⟨3861211695616761784755929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574141130411174523170619 3861211695616761784755929)
            ·
              refine ⟨2895908771712571338566947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3861211695616761784755929 2895908771712571338566947)
              ·
                refine ⟨4343863157568857007850421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2895908771712571338566947 4343863157568857007850421)
                ·
                  refine ⟨407237171022080344485977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4343863157568857007850421 407237171022080344485977)
                  ·
                    rfl

theorem cell20_892228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_892228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892228 prefixEnd_892228 := by exact prefixLift 892228
  have htrace : WordTrace (prefixWord ++ tailWord_892228) baseStart_892228 baseEnd_892228 := by
    simpa [prefixWord, tailWord_892228, baseEnd_892228] using wordTrace_append hprefix tailTrace_892228
  have hstable : (prefixWord ++ tailWord_892228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892228).length < 2 ^ (prefixWord ++ tailWord_892228).sum := by decide
  have hdescent : baseEnd_892228 < baseStart_892228 := by decide
  rcases family_descends (prefixWord ++ tailWord_892228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892245 : List Nat := [1, 3, 2, 2, 3, 3, 2, 1, 3]
def baseStart_892245 : Nat := 118140960795 + 892245 * 2 ^ 59
def prefixEnd_892245 : Nat := 4983230072969 + 3 ^ 40 * 892245 * 2
def baseEnd_892245 : Nat := 407244930285303840919241

theorem tailTrace_892245 : CollatzResearch.WordTrace tailWord_892245 prefixEnd_892245 407244930285303840919241 := by
  unfold tailWord_892245
  simp only [CollatzResearch.WordTrace]
  refine ⟨32542848652556223159254189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21695232435037482106169459 32542848652556223159254189)
  ·
    refine ⟨12203568244708583684720321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32542848652556223159254189 12203568244708583684720321)
    ·
      refine ⟨9152676183531437763540241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12203568244708583684720321 9152676183531437763540241)
      ·
        refine ⟨6864507137648578322655181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9152676183531437763540241 6864507137648578322655181)
        ·
          refine ⟨2574190176618216870995693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6864507137648578322655181 2574190176618216870995693)
          ·
            refine ⟨965321316231831326623385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2574190176618216870995693 965321316231831326623385)
            ·
              refine ⟨723990987173873494967539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 965321316231831326623385 723990987173873494967539)
              ·
                refine ⟨1085986480760810242451309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723990987173873494967539 1085986480760810242451309)
                ·
                  refine ⟨407244930285303840919241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1085986480760810242451309 407244930285303840919241)
                  ·
                    rfl

theorem cell20_892245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_892245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892245 prefixEnd_892245 := by exact prefixLift 892245
  have htrace : WordTrace (prefixWord ++ tailWord_892245) baseStart_892245 baseEnd_892245 := by
    simpa [prefixWord, tailWord_892245, baseEnd_892245] using wordTrace_append hprefix tailTrace_892245
  have hstable : (prefixWord ++ tailWord_892245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892245).length < 2 ^ (prefixWord ++ tailWord_892245).sum := by decide
  have hdescent : baseEnd_892245 < baseStart_892245 := by decide
  rcases family_descends (prefixWord ++ tailWord_892245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892286 : List Nat := [4, 2, 3, 2, 1, 1, 1, 4, 2]
def baseStart_892286 : Nat := 118140960795 + 892286 * 2 ^ 59
def prefixEnd_892286 : Nat := 4983230072969 + 3 ^ 40 * 892286 * 2
def baseEnd_892286 : Nat := 407263643802489920552407

theorem tailTrace_892286 : CollatzResearch.WordTrace tailWord_892286 prefixEnd_892286 407263643802489920552407 := by
  unfold tailWord_892286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4068043005675960895187089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21696229363605124774331141 4068043005675960895187089)
  ·
    refine ⟨3051032254256970671390317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4068043005675960895187089 3051032254256970671390317)
    ·
      refine ⟨1144137095346364001771369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3051032254256970671390317 1144137095346364001771369)
      ·
        refine ⟨858102821509773001328527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1144137095346364001771369 858102821509773001328527)
        ·
          refine ⟨1287154232264659501992791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858102821509773001328527 1287154232264659501992791)
          ·
            refine ⟨1930731348396989252989187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287154232264659501992791 1930731348396989252989187)
            ·
              refine ⟨2896097022595483879483781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1930731348396989252989187 2896097022595483879483781)
              ·
                refine ⟨543018191736653227403209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2896097022595483879483781 543018191736653227403209)
                ·
                  refine ⟨407263643802489920552407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543018191736653227403209 407263643802489920552407)
                  ·
                    rfl

theorem cell20_892286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_892286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892286 prefixEnd_892286 := by exact prefixLift 892286
  have htrace : WordTrace (prefixWord ++ tailWord_892286) baseStart_892286 baseEnd_892286 := by
    simpa [prefixWord, tailWord_892286, baseEnd_892286] using wordTrace_append hprefix tailTrace_892286
  have hstable : (prefixWord ++ tailWord_892286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892286).length < 2 ^ (prefixWord ++ tailWord_892286).sum := by decide
  have hdescent : baseEnd_892286 < baseStart_892286 := by decide
  rcases family_descends (prefixWord ++ tailWord_892286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892297 : List Nat := [1, 2, 1, 1, 8, 1, 1, 5]
def baseStart_892297 : Nat := 118140960795 + 892297 * 2 ^ 59
def prefixEnd_892297 : Nat := 4983230072969 + 3 ^ 40 * 892297 * 2
def baseEnd_892297 : Nat := 135756221500740923728565

theorem tailTrace_892297 : CollatzResearch.WordTrace tailWord_892297 prefixEnd_892297 135756221500740923728565 := by
  unfold tailWord_892297
  simp only [CollatzResearch.WordTrace]
  refine ⟨32544745248367836040147145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21696496832245224026764763 32544745248367836040147145)
  ·
    refine ⟨24408558936275877030110359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32544745248367836040147145 24408558936275877030110359)
    ·
      refine ⟨36612838404413815545165539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24408558936275877030110359 36612838404413815545165539)
      ·
        refine ⟨54919257606620723317748309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36612838404413815545165539 54919257606620723317748309)
        ·
          refine ⟨643585050077586601379863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 54919257606620723317748309 643585050077586601379863)
          ·
            refine ⟨965377575116379902069795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643585050077586601379863 965377575116379902069795)
            ·
              refine ⟨1448066362674569853104693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965377575116379902069795 1448066362674569853104693)
              ·
                refine ⟨135756221500740923728565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1448066362674569853104693 135756221500740923728565)
                ·
                  rfl

theorem cell20_892297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 5].length) (baseStart_892297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892297 prefixEnd_892297 := by exact prefixLift 892297
  have htrace : WordTrace (prefixWord ++ tailWord_892297) baseStart_892297 baseEnd_892297 := by
    simpa [prefixWord, tailWord_892297, baseEnd_892297] using wordTrace_append hprefix tailTrace_892297
  have hstable : (prefixWord ++ tailWord_892297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892297).length < 2 ^ (prefixWord ++ tailWord_892297).sum := by decide
  have hdescent : baseEnd_892297 < baseStart_892297 := by decide
  rcases family_descends (prefixWord ++ tailWord_892297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892349 : List Nat := [1, 4, 1, 2, 2, 1, 1, 6, 2]
def baseStart_892349 : Nat := 118140960795 + 892349 * 2 ^ 59
def prefixEnd_892349 : Nat := 4983230072969 + 3 ^ 40 * 892349 * 2
def baseEnd_892349 : Nat := 407292398719141701452149

theorem tailTrace_892349 : CollatzResearch.WordTrace tailWord_892349 prefixEnd_892349 407292398719141701452149 := by
  unfold tailWord_892349
  simp only [CollatzResearch.WordTrace]
  refine ⟨32546641844179448921040101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21697761229452965947360067 32546641844179448921040101)
  ·
    refine ⟨6102495345783646672695019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32546641844179448921040101 6102495345783646672695019)
    ·
      refine ⟨9153743018675470009042529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6102495345783646672695019 9153743018675470009042529)
      ·
        refine ⟨6865307264006602506781897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9153743018675470009042529 6865307264006602506781897)
        ·
          refine ⟨5148980448004951880086423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6865307264006602506781897 5148980448004951880086423)
          ·
            refine ⟨7723470672007427820129635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5148980448004951880086423 7723470672007427820129635)
            ·
              refine ⟨11585206008011141730194453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7723470672007427820129635 11585206008011141730194453)
              ·
                refine ⟨543056531625522268602865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11585206008011141730194453 543056531625522268602865)
                ·
                  refine ⟨407292398719141701452149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543056531625522268602865 407292398719141701452149)
                  ·
                    rfl

theorem cell20_892349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_892349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892349 prefixEnd_892349 := by exact prefixLift 892349
  have htrace : WordTrace (prefixWord ++ tailWord_892349) baseStart_892349 baseEnd_892349 := by
    simpa [prefixWord, tailWord_892349, baseEnd_892349] using wordTrace_append hprefix tailTrace_892349
  have hstable : (prefixWord ++ tailWord_892349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892349).length < 2 ^ (prefixWord ++ tailWord_892349).sum := by decide
  have hdescent : baseEnd_892349 < baseStart_892349 := by decide
  rcases family_descends (prefixWord ++ tailWord_892349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892377 : List Nat := [1, 2, 1, 2, 4, 3, 1, 6]
def baseStart_892377 : Nat := 118140960795 + 892377 * 2 ^ 59
def prefixEnd_892377 : Nat := 4983230072969 + 3 ^ 40 * 892377 * 2
def baseEnd_892377 : Nat := 135768392894032682839567

theorem tailTrace_892377 : CollatzResearch.WordTrace tailWord_892377 prefixEnd_892377 135768392894032682839567 := by
  unfold tailWord_892377
  simp only [CollatzResearch.WordTrace]
  refine ⟨32547663088078009703059385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21698442058718673135372923 32547663088078009703059385)
  ·
    refine ⟨24410747316058507277294539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32547663088078009703059385 24410747316058507277294539)
    ·
      refine ⟨36616120974087760915941809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24410747316058507277294539 36616120974087760915941809)
      ·
        refine ⟨27462090730565820686956357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36616120974087760915941809 27462090730565820686956357)
        ·
          refine ⟨5149142011981091378804317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27462090730565820686956357 5149142011981091378804317)
          ·
            refine ⟨1930928254492909267051619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5149142011981091378804317 1930928254492909267051619)
            ·
              refine ⟨2896392381739363900577429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1930928254492909267051619 2896392381739363900577429)
              ·
                refine ⟨135768392894032682839567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2896392381739363900577429 135768392894032682839567)
                ·
                  rfl

theorem cell20_892377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 6].length) (baseStart_892377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892377 prefixEnd_892377 := by exact prefixLift 892377
  have htrace : WordTrace (prefixWord ++ tailWord_892377) baseStart_892377 baseEnd_892377 := by
    simpa [prefixWord, tailWord_892377, baseEnd_892377] using wordTrace_append hprefix tailTrace_892377
  have hstable : (prefixWord ++ tailWord_892377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892377).length < 2 ^ (prefixWord ++ tailWord_892377).sum := by decide
  have hdescent : baseEnd_892377 < baseStart_892377 := by decide
  rcases family_descends (prefixWord ++ tailWord_892377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892394 : List Nat := [3, 1, 3, 1, 4, 2, 6]
def baseStart_892394 : Nat := 118140960795 + 892394 * 2 ^ 59
def prefixEnd_892394 : Nat := 4983230072969 + 3 ^ 40 * 892394 * 2
def baseEnd_892394 : Nat := 45256993105035727216885

theorem tailTrace_892394 : CollatzResearch.WordTrace tailWord_892394 prefixEnd_892394 45256993105035727216885 := by
  unfold tailWord_892394
  simp only [CollatzResearch.WordTrace]
  refine ⟨8137070782254105401607059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21698855419344281070952157 8137070782254105401607059)
  ·
    refine ⟨12205606173381158102410589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8137070782254105401607059 12205606173381158102410589)
    ·
      refine ⟨4577102315017934288403971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12205606173381158102410589 4577102315017934288403971)
      ·
        refine ⟨6865653472526901432605957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4577102315017934288403971 6865653472526901432605957)
        ·
          refine ⟨1287310026098794018613617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6865653472526901432605957 1287310026098794018613617)
          ·
            refine ⟨965482519574095513960213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1287310026098794018613617 965482519574095513960213)
            ·
              refine ⟨45256993105035727216885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 965482519574095513960213 45256993105035727216885)
              ·
                rfl

theorem cell20_892394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 6].length) (baseStart_892394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892394 prefixEnd_892394 := by exact prefixLift 892394
  have htrace : WordTrace (prefixWord ++ tailWord_892394) baseStart_892394 baseEnd_892394 := by
    simpa [prefixWord, tailWord_892394, baseEnd_892394] using wordTrace_append hprefix tailTrace_892394
  have hstable : (prefixWord ++ tailWord_892394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892394).length < 2 ^ (prefixWord ++ tailWord_892394).sum := by decide
  have hdescent : baseEnd_892394 < baseStart_892394 := by decide
  rcases family_descends (prefixWord ++ tailWord_892394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892408 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 4]
def baseStart_892408 : Nat := 118140960795 + 892408 * 2 ^ 59
def prefixEnd_892408 : Nat := 4983230072969 + 3 ^ 40 * 892408 * 2
def baseEnd_892408 : Nat := 407319327926799718485241

theorem tailTrace_892408 : CollatzResearch.WordTrace tailWord_892408 prefixEnd_892408 407319327926799718485241 := by
  unfold tailWord_892408
  simp only [CollatzResearch.WordTrace]
  refine ⟨16274396875482850998718939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21699195833977134664958585 16274396875482850998718939)
  ·
    refine ⟨24411595313224276498078409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16274396875482850998718939 24411595313224276498078409)
    ·
      refine ⟨18308696484918207373558807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24411595313224276498078409 18308696484918207373558807)
      ·
        refine ⟨27463044727377311060338211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18308696484918207373558807 27463044727377311060338211)
        ·
          refine ⟨41194567091065966590507317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27463044727377311060338211 41194567091065966590507317)
          ·
            refine ⟨3861990664787434367860061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41194567091065966590507317 3861990664787434367860061)
            ·
              refine ⟨1448246499295287887947523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3861990664787434367860061 1448246499295287887947523)
              ·
                refine ⟨2172369748942931831921285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448246499295287887947523 2172369748942931831921285)
                ·
                  refine ⟨407319327926799718485241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2172369748942931831921285 407319327926799718485241)
                  ·
                    rfl

theorem cell20_892408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_892408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892408 prefixEnd_892408 := by exact prefixLift 892408
  have htrace : WordTrace (prefixWord ++ tailWord_892408) baseStart_892408 baseEnd_892408 := by
    simpa [prefixWord, tailWord_892408, baseEnd_892408] using wordTrace_append hprefix tailTrace_892408
  have hstable : (prefixWord ++ tailWord_892408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892408).length < 2 ^ (prefixWord ++ tailWord_892408).sum := by decide
  have hdescent : baseEnd_892408 < baseStart_892408 := by decide
  rcases family_descends (prefixWord ++ tailWord_892408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892515 : List Nat := [1, 1, 1, 5, 1, 3, 3, 2, 3]
def baseStart_892515 : Nat := 118140960795 + 892515 * 2 ^ 59
def prefixEnd_892515 : Nat := 4983230072969 + 3 ^ 40 * 892515 * 2
def baseEnd_892515 : Nat := 407368165642382901918137

theorem tailTrace_892515 : CollatzResearch.WordTrace tailWord_892515 prefixEnd_892515 407368165642382901918137 := by
  unfold tailWord_892515
  simp only [CollatzResearch.WordTrace]
  refine ⟨32552696361578059271582999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21701797574385372847721999 32552696361578059271582999)
  ·
    refine ⟨48829044542367088907374499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32552696361578059271582999 48829044542367088907374499)
    ·
      refine ⟨73243566813550633361061749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48829044542367088907374499 73243566813550633361061749)
      ·
        refine ⟨6866584388770371877599539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73243566813550633361061749 6866584388770371877599539)
        ·
          refine ⟨10299876583155557816399309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6866584388770371877599539 10299876583155557816399309)
          ·
            refine ⟨3862453718683334181149741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10299876583155557816399309 3862453718683334181149741)
            ·
              refine ⟨1448420144506250317931153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3862453718683334181149741 1448420144506250317931153)
              ·
                refine ⟨1086315108379687738448365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1448420144506250317931153 1086315108379687738448365)
                ·
                  refine ⟨407368165642382901918137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1086315108379687738448365 407368165642382901918137)
                  ·
                    rfl

theorem cell20_892515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 3].length) (baseStart_892515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892515 prefixEnd_892515 := by exact prefixLift 892515
  have htrace : WordTrace (prefixWord ++ tailWord_892515) baseStart_892515 baseEnd_892515 := by
    simpa [prefixWord, tailWord_892515, baseEnd_892515] using wordTrace_append hprefix tailTrace_892515
  have hstable : (prefixWord ++ tailWord_892515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892515).length < 2 ^ (prefixWord ++ tailWord_892515).sum := by decide
  have hdescent : baseEnd_892515 < baseStart_892515 := by decide
  rcases family_descends (prefixWord ++ tailWord_892515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892522 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_892522 : Nat := 118140960795 + 892522 * 2 ^ 59
def prefixEnd_892522 : Nat := 4983230072969 + 3 ^ 40 * 892522 * 2
def baseEnd_892522 : Nat := 407371360633121988684775

theorem tailTrace_892522 : CollatzResearch.WordTrace tailWord_892522 prefixEnd_892522 407371360633121988684775 := by
  unfold tailWord_892522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8138237918138174866771955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21701967781701799644725213 8138237918138174866771955)
  ·
    refine ⟨12207356877207262300157933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8138237918138174866771955 12207356877207262300157933)
    ·
      refine ⟨4577758828952723362559225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12207356877207262300157933 4577758828952723362559225)
      ·
        refine ⟨3433319121714542521919419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4577758828952723362559225 3433319121714542521919419)
        ·
          refine ⟨5149978682571813782879129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3433319121714542521919419 5149978682571813782879129)
          ·
            refine ⟨3862484011928860337159347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5149978682571813782879129 3862484011928860337159347)
            ·
              refine ⟨5793726017893290505739021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3862484011928860337159347 5793726017893290505739021)
              ·
                refine ⟨2172647256709983939652133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5793726017893290505739021 2172647256709983939652133)
                ·
                  refine ⟨407371360633121988684775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2172647256709983939652133 407371360633121988684775)
                  ·
                    rfl

theorem cell20_892522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_892522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892522 prefixEnd_892522 := by exact prefixLift 892522
  have htrace : WordTrace (prefixWord ++ tailWord_892522) baseStart_892522 baseEnd_892522 := by
    simpa [prefixWord, tailWord_892522, baseEnd_892522] using wordTrace_append hprefix tailTrace_892522
  have hstable : (prefixWord ++ tailWord_892522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892522).length < 2 ^ (prefixWord ++ tailWord_892522).sum := by decide
  have hdescent : baseEnd_892522 < baseStart_892522 := by decide
  rcases family_descends (prefixWord ++ tailWord_892522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892552 : List Nat := [2, 1, 3, 5, 2, 1, 1, 3, 2]
def baseStart_892552 : Nat := 118140960795 + 892552 * 2 ^ 59
def prefixEnd_892552 : Nat := 4983230072969 + 3 ^ 40 * 892552 * 2
def baseEnd_892552 : Nat := 407385053450575217684653

theorem tailTrace_892552 : CollatzResearch.WordTrace tailWord_892552 prefixEnd_892552 407385053450575217684653 := by
  unfold tailWord_892552
  simp only [CollatzResearch.WordTrace]
  refine ⟨16277022931222007295339955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21702697241629343060453273 16277022931222007295339955)
  ·
    refine ⟨24415534396833010943009933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16277022931222007295339955 24415534396833010943009933)
    ·
      refine ⟨9155825398812379103628725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24415534396833010943009933 9155825398812379103628725)
      ·
        refine ⟨858358631138660540965193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9155825398812379103628725 858358631138660540965193)
        ·
          refine ⟨643768973353995405723895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858358631138660540965193 643768973353995405723895)
          ·
            refine ⟨965653460030993108585843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643768973353995405723895 965653460030993108585843)
            ·
              refine ⟨1448480190046489662878765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965653460030993108585843 1448480190046489662878765)
              ·
                refine ⟨543180071267433623579537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1448480190046489662878765 543180071267433623579537)
                ·
                  refine ⟨407385053450575217684653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543180071267433623579537 407385053450575217684653)
                  ·
                    rfl

theorem cell20_892552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 2].length) (baseStart_892552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892552 prefixEnd_892552 := by exact prefixLift 892552
  have htrace : WordTrace (prefixWord ++ tailWord_892552) baseStart_892552 baseEnd_892552 := by
    simpa [prefixWord, tailWord_892552, baseEnd_892552] using wordTrace_append hprefix tailTrace_892552
  have hstable : (prefixWord ++ tailWord_892552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892552).length < 2 ^ (prefixWord ++ tailWord_892552).sum := by decide
  have hdescent : baseEnd_892552 < baseStart_892552 := by decide
  rcases family_descends (prefixWord ++ tailWord_892552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892567 : List Nat := [1, 1, 3, 3, 2, 4, 6]
def baseStart_892567 : Nat := 118140960795 + 892567 * 2 ^ 59
def prefixEnd_892567 : Nat := 4983230072969 + 3 ^ 40 * 892567 * 2
def baseEnd_892567 : Nat := 45265766651033536909399

theorem tailTrace_892567 : CollatzResearch.WordTrace tailWord_892567 prefixEnd_892567 45265766651033536909399 := by
  unfold tailWord_892567
  simp only [CollatzResearch.WordTrace]
  refine ⟨32554592957389672152475955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21703061971593114768317303 32554592957389672152475955)
  ·
    refine ⟨48831889436084508228713933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32554592957389672152475955 48831889436084508228713933)
    ·
      refine ⟨18311958538531690585767725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48831889436084508228713933 18311958538531690585767725)
      ·
        refine ⟨6866984451949383969662897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18311958538531690585767725 6866984451949383969662897)
        ·
          refine ⟨5150238338962037977247173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6866984451949383969662897 5150238338962037977247173)
          ·
            refine ⟨965669688555382120733845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5150238338962037977247173 965669688555382120733845)
            ·
              refine ⟨45265766651033536909399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 965669688555382120733845 45265766651033536909399)
              ·
                rfl

theorem cell20_892567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 6].length) (baseStart_892567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892567 prefixEnd_892567 := by exact prefixLift 892567
  have htrace : WordTrace (prefixWord ++ tailWord_892567) baseStart_892567 baseEnd_892567 := by
    simpa [prefixWord, tailWord_892567, baseEnd_892567] using wordTrace_append hprefix tailTrace_892567
  have hstable : (prefixWord ++ tailWord_892567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892567).length < 2 ^ (prefixWord ++ tailWord_892567).sum := by decide
  have hdescent : baseEnd_892567 < baseStart_892567 := by decide
  rcases family_descends (prefixWord ++ tailWord_892567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892577 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 4]
def baseStart_892577 : Nat := 118140960795 + 892577 * 2 ^ 59
def prefixEnd_892577 : Nat := 4983230072969 + 3 ^ 40 * 892577 * 2
def baseEnd_892577 : Nat := 407396464131786241851217

theorem tailTrace_892577 : CollatzResearch.WordTrace tailWord_892577 prefixEnd_892577 407396464131786241851217 := by
  unfold tailWord_892577
  simp only [CollatzResearch.WordTrace]
  refine ⟨32554957687353443860339985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21703305124902295906893323 32554957687353443860339985)
  ·
    refine ⟨24416218265515082895254989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32554957687353443860339985 24416218265515082895254989)
    ·
      refine ⟨9156081849568156085720621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24416218265515082895254989 9156081849568156085720621)
      ·
        refine ⟨3433530693588058532145233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9156081849568156085720621 3433530693588058532145233)
        ·
          refine ⟨2575148020191043899108925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3433530693588058532145233 2575148020191043899108925)
          ·
            refine ⟨965680507571641462165847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2575148020191043899108925 965680507571641462165847)
            ·
              refine ⟨1448520761357462193248771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965680507571641462165847 1448520761357462193248771)
              ·
                refine ⟨2172781142036193289873157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448520761357462193248771 2172781142036193289873157)
                ·
                  refine ⟨407396464131786241851217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2172781142036193289873157 407396464131786241851217)
                  ·
                    rfl

theorem cell20_892577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_892577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892577 prefixEnd_892577 := by exact prefixLift 892577
  have htrace : WordTrace (prefixWord ++ tailWord_892577) baseStart_892577 baseEnd_892577 := by
    simpa [prefixWord, tailWord_892577, baseEnd_892577] using wordTrace_append hprefix tailTrace_892577
  have hstable : (prefixWord ++ tailWord_892577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892577).length < 2 ^ (prefixWord ++ tailWord_892577).sum := by decide
  have hdescent : baseEnd_892577 < baseStart_892577 := by decide
  rcases family_descends (prefixWord ++ tailWord_892577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892657 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 6]
def baseStart_892657 : Nat := 118140960795 + 892657 * 2 ^ 59
def prefixEnd_892657 : Nat := 4983230072969 + 3 ^ 40 * 892657 * 2
def baseEnd_892657 : Nat := 407432978311661519184223

theorem tailTrace_892657 : CollatzResearch.WordTrace tailWord_892657 prefixEnd_892657 407432978311661519184223 := by
  unfold tailWord_892657
  simp only [CollatzResearch.WordTrace]
  refine ⟨32557875527063617523252225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21705250351375745015501483 32557875527063617523252225)
  ·
    refine ⟨24418406645297713142439169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32557875527063617523252225 24418406645297713142439169)
    ·
      refine ⟨18313804983973284856829377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24418406645297713142439169 18313804983973284856829377)
      ·
        refine ⟨13735353737979963642622033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18313804983973284856829377 13735353737979963642622033)
        ·
          refine ⟨10301515303484972731966525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13735353737979963642622033 10301515303484972731966525)
          ·
            refine ⟨3863068238806864774487447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10301515303484972731966525 3863068238806864774487447)
            ·
              refine ⟨5794602358210297161731171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3863068238806864774487447 5794602358210297161731171)
              ·
                refine ⟨8691903537315445742596757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5794602358210297161731171 8691903537315445742596757)
                ·
                  refine ⟨407432978311661519184223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8691903537315445742596757 407432978311661519184223)
                  ·
                    rfl

theorem cell20_892657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_892657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892657 prefixEnd_892657 := by exact prefixLift 892657
  have htrace : WordTrace (prefixWord ++ tailWord_892657) baseStart_892657 baseEnd_892657 := by
    simpa [prefixWord, tailWord_892657, baseEnd_892657] using wordTrace_append hprefix tailTrace_892657
  have hstable : (prefixWord ++ tailWord_892657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892657).length < 2 ^ (prefixWord ++ tailWord_892657).sum := by decide
  have hdescent : baseEnd_892657 < baseStart_892657 := by decide
  rcases family_descends (prefixWord ++ tailWord_892657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892674 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_892674 : Nat := 118140960795 + 892674 * 2 ^ 59
def prefixEnd_892674 : Nat := 4983230072969 + 3 ^ 40 * 892674 * 2
def baseEnd_892674 : Nat := 407440737574885015617487

theorem tailTrace_892674 : CollatzResearch.WordTrace tailWord_892674 prefixEnd_892674 407440737574885015617487 := by
  unfold tailWord_892674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8139623892000507356655269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21705663712001352951080717 8139623892000507356655269)
  ·
    refine ⟨1526179479750095129372863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8139623892000507356655269 1526179479750095129372863)
    ·
      refine ⟨2289269219625142694059295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1526179479750095129372863 2289269219625142694059295)
      ·
        refine ⟨3433903829437714041088943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2289269219625142694059295 3433903829437714041088943)
        ·
          refine ⟨5150855744156571061633415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3433903829437714041088943 5150855744156571061633415)
          ·
            refine ⟨7726283616234856592450123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5150855744156571061633415 7726283616234856592450123)
            ·
              refine ⟨11589425424352284888675185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7726283616234856592450123 11589425424352284888675185)
              ·
                refine ⟨8692069068264213666506389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11589425424352284888675185 8692069068264213666506389)
                ·
                  refine ⟨407440737574885015617487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8692069068264213666506389 407440737574885015617487)
                  ·
                    rfl

theorem cell20_892674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_892674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892674 prefixEnd_892674 := by exact prefixLift 892674
  have htrace : WordTrace (prefixWord ++ tailWord_892674) baseStart_892674 baseEnd_892674 := by
    simpa [prefixWord, tailWord_892674, baseEnd_892674] using wordTrace_append hprefix tailTrace_892674
  have hstable : (prefixWord ++ tailWord_892674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892674).length < 2 ^ (prefixWord ++ tailWord_892674).sum := by decide
  have hdescent : baseEnd_892674 < baseStart_892674 := by decide
  rcases family_descends (prefixWord ++ tailWord_892674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892712 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 4]
def baseStart_892712 : Nat := 118140960795 + 892712 * 2 ^ 59
def prefixEnd_892712 : Nat := 4983230072969 + 3 ^ 40 * 892712 * 2
def baseEnd_892712 : Nat := 407458081810325772350665

theorem tailTrace_892712 : CollatzResearch.WordTrace tailWord_892712 prefixEnd_892712 407458081810325772350665 := by
  unfold tailWord_892712
  simp only [CollatzResearch.WordTrace]
  refine ⟨16279940770932180958252195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21706587694576241277669593 16279940770932180958252195)
  ·
    refine ⟨24419911156398271437378293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16279940770932180958252195 24419911156398271437378293)
    ·
      refine ⟨2289366670912337947254215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24419911156398271437378293 2289366670912337947254215)
      ·
        refine ⟨3434050006368506920881323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2289366670912337947254215 3434050006368506920881323)
        ·
          refine ⟨5151075009552760381321985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3434050006368506920881323 5151075009552760381321985)
          ·
            refine ⟨3863306257164570285991489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5151075009552760381321985 3863306257164570285991489)
            ·
              refine ⟨2897479692873427714493617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3863306257164570285991489 2897479692873427714493617)
              ·
                refine ⟨2173109769655070785870213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2897479692873427714493617 2173109769655070785870213)
                ·
                  refine ⟨407458081810325772350665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2173109769655070785870213 407458081810325772350665)
                  ·
                    rfl

theorem cell20_892712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_892712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892712 prefixEnd_892712 := by exact prefixLift 892712
  have htrace : WordTrace (prefixWord ++ tailWord_892712) baseStart_892712 baseEnd_892712 := by
    simpa [prefixWord, tailWord_892712, baseEnd_892712] using wordTrace_append hprefix tailTrace_892712
  have hstable : (prefixWord ++ tailWord_892712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892712).length < 2 ^ (prefixWord ++ tailWord_892712).sum := by decide
  have hdescent : baseEnd_892712 < baseStart_892712 := by decide
  rcases family_descends (prefixWord ++ tailWord_892712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892725 : List Nat := [1, 3, 3, 1, 5, 1, 1, 3, 2]
def baseStart_892725 : Nat := 118140960795 + 892725 * 2 ^ 59
def prefixEnd_892725 : Nat := 4983230072969 + 3 ^ 40 * 892725 * 2
def baseEnd_892725 : Nat := 407464015364555504917279

theorem tailTrace_892725 : CollatzResearch.WordTrace tailWord_892725 prefixEnd_892725 407464015364555504917279 := by
  unfold tailWord_892725
  simp only [CollatzResearch.WordTrace]
  refine ⟨32560355690817265136727629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21706903793878176757818419 32560355690817265136727629)
  ·
    refine ⟨12210133384056474426272861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32560355690817265136727629 12210133384056474426272861)
    ·
      refine ⟨4578800019021177909852323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12210133384056474426272861 4578800019021177909852323)
      ·
        refine ⟨6868200028531766864778485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4578800019021177909852323 6868200028531766864778485)
        ·
          refine ⟨643893752674853143572983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6868200028531766864778485 643893752674853143572983)
          ·
            refine ⟨965840629012279715359475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643893752674853143572983 965840629012279715359475)
            ·
              refine ⟨1448760943518419573039213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965840629012279715359475 1448760943518419573039213)
              ·
                refine ⟨543285353819407339889705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1448760943518419573039213 543285353819407339889705)
                ·
                  refine ⟨407464015364555504917279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543285353819407339889705 407464015364555504917279)
                  ·
                    rfl

theorem cell20_892725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_892725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892725 prefixEnd_892725 := by exact prefixLift 892725
  have htrace : WordTrace (prefixWord ++ tailWord_892725) baseStart_892725 baseEnd_892725 := by
    simpa [prefixWord, tailWord_892725, baseEnd_892725] using wordTrace_append hprefix tailTrace_892725
  have hstable : (prefixWord ++ tailWord_892725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892725).length < 2 ^ (prefixWord ++ tailWord_892725).sum := by decide
  have hdescent : baseEnd_892725 < baseStart_892725 := by decide
  rcases family_descends (prefixWord ++ tailWord_892725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892742 : List Nat := [6, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_892742 : Nat := 118140960795 + 892742 * 2 ^ 59
def prefixEnd_892742 : Nat := 4983230072969 + 3 ^ 40 * 892742 * 2
def baseEnd_892742 : Nat := 407471774627779001350543

theorem tailTrace_892742 : CollatzResearch.WordTrace tailWord_892742 prefixEnd_892742 407471774627779001350543 := by
  unfold tailWord_892742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1017530491617364907503015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21707317154503784693397653 1017530491617364907503015)
  ·
    refine ⟨1526295737426047361254523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1017530491617364907503015 1526295737426047361254523)
    ·
      refine ⟨2289443606139071041881785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1526295737426047361254523 2289443606139071041881785)
      ·
        refine ⟨1717082704604303281411339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2289443606139071041881785 1717082704604303281411339)
        ·
          refine ⟨2575624056906454922117009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717082704604303281411339 2575624056906454922117009)
          ·
            refine ⟨1931718042679841191587757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2575624056906454922117009 1931718042679841191587757)
            ·
              refine ⟨724394266004940446845409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1931718042679841191587757 724394266004940446845409)
              ·
                refine ⟨543295699503705335134057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724394266004940446845409 543295699503705335134057)
                ·
                  refine ⟨407471774627779001350543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543295699503705335134057 407471774627779001350543)
                  ·
                    rfl

theorem cell20_892742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_892742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892742 prefixEnd_892742 := by exact prefixLift 892742
  have htrace : WordTrace (prefixWord ++ tailWord_892742) baseStart_892742 baseEnd_892742 := by
    simpa [prefixWord, tailWord_892742, baseEnd_892742] using wordTrace_append hprefix tailTrace_892742
  have hstable : (prefixWord ++ tailWord_892742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892742).length < 2 ^ (prefixWord ++ tailWord_892742).sum := by decide
  have hdescent : baseEnd_892742 < baseStart_892742 := by decide
  rcases family_descends (prefixWord ++ tailWord_892742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892757 : List Nat := [1, 3, 2, 2, 2, 3, 2, 5]
def baseStart_892757 : Nat := 118140960795 + 892757 * 2 ^ 59
def prefixEnd_892757 : Nat := 4983230072969 + 3 ^ 40 * 892757 * 2
def baseEnd_892757 : Nat := 135826207012168538616827

theorem tailTrace_892757 : CollatzResearch.WordTrace tailWord_892757 prefixEnd_892757 135826207012168538616827 := by
  unfold tailWord_892757
  simp only [CollatzResearch.WordTrace]
  refine ⟨32561522826701334601892525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21707681884467556401261683 32561522826701334601892525)
  ·
    refine ⟨12210571060013000475709697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32561522826701334601892525 12210571060013000475709697)
    ·
      refine ⟨9157928295009750356782273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12210571060013000475709697 9157928295009750356782273)
      ·
        refine ⟨6868446221257312767586705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9157928295009750356782273 6868446221257312767586705)
        ·
          refine ⟨5151334665942984575690029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6868446221257312767586705 5151334665942984575690029)
          ·
            refine ⟨1931750499728619215883761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5151334665942984575690029 1931750499728619215883761)
            ·
              refine ⟨1448812874796464411912821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1931750499728619215883761 1448812874796464411912821)
              ·
                refine ⟨135826207012168538616827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1448812874796464411912821 135826207012168538616827)
                ·
                  rfl

theorem cell20_892757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 5].length) (baseStart_892757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892757 prefixEnd_892757 := by exact prefixLift 892757
  have htrace : WordTrace (prefixWord ++ tailWord_892757) baseStart_892757 baseEnd_892757 := by
    simpa [prefixWord, tailWord_892757, baseEnd_892757] using wordTrace_append hprefix tailTrace_892757
  have hstable : (prefixWord ++ tailWord_892757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892757).length < 2 ^ (prefixWord ++ tailWord_892757).sum := by decide
  have hdescent : baseEnd_892757 < baseStart_892757 := by decide
  rcases family_descends (prefixWord ++ tailWord_892757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892798 : List Nat := [4, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_892798 : Nat := 118140960795 + 892798 * 2 ^ 59
def prefixEnd_892798 : Nat := 4983230072969 + 3 ^ 40 * 892798 * 2
def baseEnd_892798 : Nat := 407497334553691695483647

theorem tailTrace_892798 : CollatzResearch.WordTrace tailWord_892798 prefixEnd_892798 407497334553691695483647 := by
  unfold tailWord_892798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4070377277444099825516881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21708678813035199069423365 4070377277444099825516881)
  ·
    refine ⟨3052782958083074869137661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4070377277444099825516881 3052782958083074869137661)
    ·
      refine ⟨1144793609281153075926623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3052782958083074869137661 1144793609281153075926623)
      ·
        refine ⟨1717190413921729613889935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1144793609281153075926623 1717190413921729613889935)
        ·
          refine ⟨2575785620882594420834903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717190413921729613889935 2575785620882594420834903)
          ·
            refine ⟨3863678431323891631252355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575785620882594420834903 3863678431323891631252355)
            ·
              refine ⟨5795517646985837446878533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3863678431323891631252355 5795517646985837446878533)
              ·
                refine ⟨1086659558809844521289725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5795517646985837446878533 1086659558809844521289725)
                ·
                  refine ⟨407497334553691695483647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1086659558809844521289725 407497334553691695483647)
                  ·
                    rfl

theorem cell20_892798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_892798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892798 prefixEnd_892798 := by exact prefixLift 892798
  have htrace : WordTrace (prefixWord ++ tailWord_892798) baseStart_892798 baseEnd_892798 := by
    simpa [prefixWord, tailWord_892798, baseEnd_892798] using wordTrace_append hprefix tailTrace_892798
  have hstable : (prefixWord ++ tailWord_892798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892798).length < 2 ^ (prefixWord ++ tailWord_892798).sum := by decide
  have hdescent : baseEnd_892798 < baseStart_892798 := by decide
  rcases family_descends (prefixWord ++ tailWord_892798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892809 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 4]
def baseStart_892809 : Nat := 118140960795 + 892809 * 2 ^ 59
def prefixEnd_892809 : Nat := 4983230072969 + 3 ^ 40 * 892809 * 2
def baseEnd_892809 : Nat := 407502355253424546116935

theorem tailTrace_892809 : CollatzResearch.WordTrace tailWord_892809 prefixEnd_892809 407502355253424546116935 := by
  unfold tailWord_892809
  simp only [CollatzResearch.WordTrace]
  refine ⟨32563419422512947482785481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21708946281675298321856987 32563419422512947482785481)
  ·
    refine ⟨24422564566884710612089111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32563419422512947482785481 24422564566884710612089111)
    ·
      refine ⟨36633846850327065918133667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24422564566884710612089111 36633846850327065918133667)
      ·
        refine ⟨54950770275490598877200501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36633846850327065918133667 54950770275490598877200501)
        ·
          refine ⟨5151634713327243644737547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54950770275490598877200501 5151634713327243644737547)
          ·
            refine ⟨7727452069990865467106321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5151634713327243644737547 7727452069990865467106321)
            ·
              refine ⟨5795589052493149100329741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7727452069990865467106321 5795589052493149100329741)
              ·
                refine ⟨2173345894684930912623653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5795589052493149100329741 2173345894684930912623653)
                ·
                  refine ⟨407502355253424546116935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2173345894684930912623653 407502355253424546116935)
                  ·
                    rfl

theorem cell20_892809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_892809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892809 prefixEnd_892809 := by exact prefixLift 892809
  have htrace : WordTrace (prefixWord ++ tailWord_892809) baseStart_892809 baseEnd_892809 := by
    simpa [prefixWord, tailWord_892809, baseEnd_892809] using wordTrace_append hprefix tailTrace_892809
  have hstable : (prefixWord ++ tailWord_892809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892809).length < 2 ^ (prefixWord ++ tailWord_892809).sum := by decide
  have hdescent : baseEnd_892809 < baseStart_892809 := by decide
  rcases family_descends (prefixWord ++ tailWord_892809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892826 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_892826 : Nat := 118140960795 + 892826 * 2 ^ 59
def prefixEnd_892826 : Nat := 4983230072969 + 3 ^ 40 * 892826 * 2
def baseEnd_892826 : Nat := 407510114516648042550199

theorem tailTrace_892826 : CollatzResearch.WordTrace tailWord_892826 prefixEnd_892826 407510114516648042550199 := by
  unfold tailWord_892826
  simp only [CollatzResearch.WordTrace]
  refine ⟨8141009865862839846538583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21709359642300906257436221 8141009865862839846538583)
  ·
    refine ⟨12211514798794259769807875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8141009865862839846538583 12211514798794259769807875)
    ·
      refine ⟨18317272198191389654711813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12211514798794259769807875 18317272198191389654711813)
      ·
        refine ⟨3434488537160885560258465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18317272198191389654711813 3434488537160885560258465)
        ·
          refine ⟨2575866402870664170193849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3434488537160885560258465 2575866402870664170193849)
          ·
            refine ⟨1931899802152998127645387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2575866402870664170193849 1931899802152998127645387)
            ·
              refine ⟨2897849703229497191468081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1931899802152998127645387 2897849703229497191468081)
              ·
                refine ⟨2173387277422122893601061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2897849703229497191468081 2173387277422122893601061)
                ·
                  refine ⟨407510114516648042550199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2173387277422122893601061 407510114516648042550199)
                  ·
                    rfl

theorem cell20_892826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_892826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892826 prefixEnd_892826 := by exact prefixLift 892826
  have htrace : WordTrace (prefixWord ++ tailWord_892826) baseStart_892826 baseEnd_892826 := by
    simpa [prefixWord, tailWord_892826, baseEnd_892826] using wordTrace_append hprefix tailTrace_892826
  have hstable : (prefixWord ++ tailWord_892826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892826).length < 2 ^ (prefixWord ++ tailWord_892826).sum := by decide
  have hdescent : baseEnd_892826 < baseStart_892826 := by decide
  rcases family_descends (prefixWord ++ tailWord_892826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892864 : List Nat := [2, 1, 1, 2, 3, 2, 1, 6, 2]
def baseStart_892864 : Nat := 118140960795 + 892864 * 2 ^ 59
def prefixEnd_892864 : Nat := 4983230072969 + 3 ^ 40 * 892864 * 2
def baseEnd_892864 : Nat := 407527458752088799283377

theorem tailTrace_892864 : CollatzResearch.WordTrace tailWord_892864 prefixEnd_892864 407527458752088799283377 := by
  unfold tailWord_892864
  simp only [CollatzResearch.WordTrace]
  refine ⟨16282712718656845938018823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21710283624875794584025097 16282712718656845938018823)
  ·
    refine ⟨24424069077985268907028235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16282712718656845938018823 24424069077985268907028235)
    ·
      refine ⟨36636103616977903360542353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24424069077985268907028235 36636103616977903360542353)
      ·
        refine ⟨27477077712733427520406765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36636103616977903360542353 27477077712733427520406765)
        ·
          refine ⟨10303904142275035320152537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27477077712733427520406765 10303904142275035320152537)
          ·
            refine ⟨7727928106706276490114403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10303904142275035320152537 7727928106706276490114403)
            ·
              refine ⟨11591892160059414735171605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7727928106706276490114403 11591892160059414735171605)
              ·
                refine ⟨543369945002785065711169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11591892160059414735171605 543369945002785065711169)
                ·
                  refine ⟨407527458752088799283377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543369945002785065711169 407527458752088799283377)
                  ·
                    rfl

theorem cell20_892864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 2].length) (baseStart_892864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892864 prefixEnd_892864 := by exact prefixLift 892864
  have htrace : WordTrace (prefixWord ++ tailWord_892864) baseStart_892864 baseEnd_892864 := by
    simpa [prefixWord, tailWord_892864, baseEnd_892864] using wordTrace_append hprefix tailTrace_892864
  have hstable : (prefixWord ++ tailWord_892864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892864).length < 2 ^ (prefixWord ++ tailWord_892864).sum := by decide
  have hdescent : baseEnd_892864 < baseStart_892864 := by decide
  rcases family_descends (prefixWord ++ tailWord_892864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892923 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 4]
def baseStart_892923 : Nat := 118140960795 + 892923 * 2 ^ 59
def prefixEnd_892923 : Nat := 4983230072969 + 3 ^ 40 * 892923 * 2
def baseEnd_892923 : Nat := 407554387959746816316469

theorem tailTrace_892923 : CollatzResearch.WordTrace tailWord_892923 prefixEnd_892923 407554387959746816316469 := by
  unfold tailWord_892923
  simp only [CollatzResearch.WordTrace]
  refine ⟨32567577344099944952435423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21711718229399963301623615 32567577344099944952435423)
  ·
    refine ⟨48851366016149917428653135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32567577344099944952435423 48851366016149917428653135)
    ·
      refine ⟨73277049024224876142979703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48851366016149917428653135 73277049024224876142979703)
      ·
        refine ⟨109915573536337314214469555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73277049024224876142979703 109915573536337314214469555)
        ·
          refine ⟨164873360304505971321704333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109915573536337314214469555 164873360304505971321704333)
          ·
            refine ⟨61827510114189739245639125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164873360304505971321704333 61827510114189739245639125)
            ·
              refine ⟨1449082268301322013569667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 61827510114189739245639125 1449082268301322013569667)
              ·
                refine ⟨2173623402451983020354501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1449082268301322013569667 2173623402451983020354501)
                ·
                  refine ⟨407554387959746816316469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2173623402451983020354501 407554387959746816316469)
                  ·
                    rfl

theorem cell20_892923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 4].length) (baseStart_892923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892923 prefixEnd_892923 := by exact prefixLift 892923
  have htrace : WordTrace (prefixWord ++ tailWord_892923) baseStart_892923 baseEnd_892923 := by
    simpa [prefixWord, tailWord_892923, baseEnd_892923] using wordTrace_append hprefix tailTrace_892923
  have hstable : (prefixWord ++ tailWord_892923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892923).length < 2 ^ (prefixWord ++ tailWord_892923).sum := by decide
  have hdescent : baseEnd_892923 < baseStart_892923 := by decide
  rcases family_descends (prefixWord ++ tailWord_892923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892926 : List Nat := [4, 2, 2, 2, 1, 2, 2, 5]
def baseStart_892926 : Nat := 118140960795 + 892926 * 2 ^ 59
def prefixEnd_892926 : Nat := 4983230072969 + 3 ^ 40 * 892926 * 2
def baseEnd_892926 : Nat := 135851919080497379738819

theorem tailTrace_892926 : CollatzResearch.WordTrace tailWord_892926 prefixEnd_892926 135851919080497379738819 := by
  unfold tailWord_892926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4070960845386134558099329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21711791175392717643196421 4070960845386134558099329)
  ·
    refine ⟨3053220634039600918574497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4070960845386134558099329 3053220634039600918574497)
    ·
      refine ⟨2289915475529700688930873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3053220634039600918574497 2289915475529700688930873)
      ·
        refine ⟨1717436606647275516698155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2289915475529700688930873 1717436606647275516698155)
        ·
          refine ⟨2576154909970913275047233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717436606647275516698155 2576154909970913275047233)
          ·
            refine ⟨1932116182478184956285425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2576154909970913275047233 1932116182478184956285425)
            ·
              refine ⟨1449087136858638717214069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1932116182478184956285425 1449087136858638717214069)
              ·
                refine ⟨135851919080497379738819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1449087136858638717214069 135851919080497379738819)
                ·
                  rfl

theorem cell20_892926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_892926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892926 prefixEnd_892926 := by exact prefixLift 892926
  have htrace : WordTrace (prefixWord ++ tailWord_892926) baseStart_892926 baseEnd_892926 := by
    simpa [prefixWord, tailWord_892926, baseEnd_892926] using wordTrace_append hprefix tailTrace_892926
  have hstable : (prefixWord ++ tailWord_892926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892926).length < 2 ^ (prefixWord ++ tailWord_892926).sum := by decide
  have hdescent : baseEnd_892926 < baseStart_892926 := by decide
  rcases family_descends (prefixWord ++ tailWord_892926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892933 : List Nat := [1, 3, 1, 1, 2, 4, 4, 1, 3]
def baseStart_892933 : Nat := 118140960795 + 892933 * 2 ^ 59
def prefixEnd_892933 : Nat := 4983230072969 + 3 ^ 40 * 892933 * 2
def baseEnd_892933 : Nat := 407558952232231225983095

theorem tailTrace_892933 : CollatzResearch.WordTrace tailWord_892933 prefixEnd_892933 407558952232231225983095 := by
  unfold tailWord_892933
  simp only [CollatzResearch.WordTrace]
  refine ⟨32567942074063716660299453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21711961382709144440199635 32567942074063716660299453)
  ·
    refine ⟨12212978277773893747612295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32567942074063716660299453 12212978277773893747612295)
    ·
      refine ⟨18319467416660840621418443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12212978277773893747612295 18319467416660840621418443)
      ·
        refine ⟨27479201124991260932127665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18319467416660840621418443 27479201124991260932127665)
        ·
          refine ⟨20609400843743445699095749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27479201124991260932127665 20609400843743445699095749)
          ·
            refine ⟨3864262658201896068580453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20609400843743445699095749 3864262658201896068580453)
            ·
              refine ⟨724549248412855512858835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3864262658201896068580453 724549248412855512858835)
              ·
                refine ⟨1086823872619283269288253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724549248412855512858835 1086823872619283269288253)
                ·
                  refine ⟨407558952232231225983095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1086823872619283269288253 407558952232231225983095)
                  ·
                    rfl

theorem cell20_892933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_892933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892933 prefixEnd_892933 := by exact prefixLift 892933
  have htrace : WordTrace (prefixWord ++ tailWord_892933) baseStart_892933 baseEnd_892933 := by
    simpa [prefixWord, tailWord_892933, baseEnd_892933] using wordTrace_append hprefix tailTrace_892933
  have hstable : (prefixWord ++ tailWord_892933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892933).length < 2 ^ (prefixWord ++ tailWord_892933).sum := by decide
  have hdescent : baseEnd_892933 < baseStart_892933 := by decide
  rcases family_descends (prefixWord ++ tailWord_892933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892974 : List Nat := [4, 1, 3, 1, 1, 2, 4, 2, 2]
def baseStart_892974 : Nat := 118140960795 + 892974 * 2 ^ 59
def prefixEnd_892974 : Nat := 4983230072969 + 3 ^ 40 * 892974 * 2
def baseEnd_892974 : Nat := 407577665749417305616261

theorem tailTrace_892974 : CollatzResearch.WordTrace tailWord_892974 prefixEnd_892974 407577665749417305616261 := by
  unfold tailWord_892974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4071179683364397582817747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21712958311276787108361317 4071179683364397582817747)
  ·
    refine ⟨6106769525046596374226621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4071179683364397582817747 6106769525046596374226621)
    ·
      refine ⟨2290038571892473640334983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6106769525046596374226621 2290038571892473640334983)
      ·
        refine ⟨3435057857838710460502475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2290038571892473640334983 3435057857838710460502475)
        ·
          refine ⟨5152586786758065690753713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3435057857838710460502475 5152586786758065690753713)
          ·
            refine ⟨3864440090068549268065285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5152586786758065690753713 3864440090068549268065285)
            ·
              refine ⟨724582516887852987762241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3864440090068549268065285 724582516887852987762241)
              ·
                refine ⟨543436887665889740821681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724582516887852987762241 543436887665889740821681)
                ·
                  refine ⟨407577665749417305616261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543436887665889740821681 407577665749417305616261)
                  ·
                    rfl

theorem cell20_892974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_892974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892974 prefixEnd_892974 := by exact prefixLift 892974
  have htrace : WordTrace (prefixWord ++ tailWord_892974) baseStart_892974 baseEnd_892974 := by
    simpa [prefixWord, tailWord_892974, baseEnd_892974] using wordTrace_append hprefix tailTrace_892974
  have hstable : (prefixWord ++ tailWord_892974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892974).length < 2 ^ (prefixWord ++ tailWord_892974).sum := by decide
  have hdescent : baseEnd_892974 < baseStart_892974 := by decide
  rcases family_descends (prefixWord ++ tailWord_892974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892992 : List Nat := [2, 1, 1, 2, 2, 4, 2, 3, 3]
def baseStart_892992 : Nat := 118140960795 + 892992 * 2 ^ 59
def prefixEnd_892992 : Nat := 4983230072969 + 3 ^ 40 * 892992 * 2
def baseEnd_892992 : Nat := 407585881439889243016187

theorem tailTrace_892992 : CollatzResearch.WordTrace tailWord_892992 prefixEnd_892992 407585881439889243016187 := by
  unfold tailWord_892992
  simp only [CollatzResearch.WordTrace]
  refine ⟨16285046990424984868348615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21713395987233313157798153 16285046990424984868348615)
  ·
    refine ⟨24427570485637477302522923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16285046990424984868348615 24427570485637477302522923)
    ·
      refine ⟨36641355728456215953784385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24427570485637477302522923 36641355728456215953784385)
      ·
        refine ⟨27481016796342161965338289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36641355728456215953784385 27481016796342161965338289)
        ·
          refine ⟨20610762597256621474003717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27481016796342161965338289 20610762597256621474003717)
          ·
            refine ⟨3864517986985616526375697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20610762597256621474003717 3864517986985616526375697)
            ·
              refine ⟨2898388490239212394781773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3864517986985616526375697 2898388490239212394781773)
              ·
                refine ⟨1086895683839704648043165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2898388490239212394781773 1086895683839704648043165)
                ·
                  refine ⟨407585881439889243016187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1086895683839704648043165 407585881439889243016187)
                  ·
                    rfl

theorem cell20_892992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_892992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892992 prefixEnd_892992 := by exact prefixLift 892992
  have htrace : WordTrace (prefixWord ++ tailWord_892992) baseStart_892992 baseEnd_892992 := by
    simpa [prefixWord, tailWord_892992, baseEnd_892992] using wordTrace_append hprefix tailTrace_892992
  have hstable : (prefixWord ++ tailWord_892992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892992).length < 2 ^ (prefixWord ++ tailWord_892992).sum := by decide
  have hdescent : baseEnd_892992 < baseStart_892992 := by decide
  rcases family_descends (prefixWord ++ tailWord_892992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892999 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 4]
def baseStart_892999 : Nat := 118140960795 + 892999 * 2 ^ 59
def prefixEnd_892999 : Nat := 4983230072969 + 3 ^ 40 * 892999 * 2
def baseEnd_892999 : Nat := 407589076430628329782825

theorem tailTrace_892999 : CollatzResearch.WordTrace tailWord_892999 prefixEnd_892999 407589076430628329782825 := by
  unfold tailWord_892999
  simp only [CollatzResearch.WordTrace]
  refine ⟨32570349291824609932202051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21713566194549739954801367 32570349291824609932202051)
  ·
    refine ⟨48855523937736914898303077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32570349291824609932202051 48855523937736914898303077)
    ·
      refine ⟨9160410738325671543431827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48855523937736914898303077 9160410738325671543431827)
      ·
        refine ⟨13740616107488507315147741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9160410738325671543431827 13740616107488507315147741)
        ·
          refine ⟨5152731040308190243180403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13740616107488507315147741 5152731040308190243180403)
          ·
            refine ⟨7729096560462285364770605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5152731040308190243180403 7729096560462285364770605)
            ·
              refine ⟨2898411210173357011788977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7729096560462285364770605 2898411210173357011788977)
              ·
                refine ⟨2173808407630017758841733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2898411210173357011788977 2173808407630017758841733)
                ·
                  refine ⟨407589076430628329782825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2173808407630017758841733 407589076430628329782825)
                  ·
                    rfl

theorem cell20_892999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_892999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_892999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_892999 prefixEnd_892999 := by exact prefixLift 892999
  have htrace : WordTrace (prefixWord ++ tailWord_892999) baseStart_892999 baseEnd_892999 := by
    simpa [prefixWord, tailWord_892999, baseEnd_892999] using wordTrace_append hprefix tailTrace_892999
  have hstable : (prefixWord ++ tailWord_892999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892999).length < 2 ^ (prefixWord ++ tailWord_892999).sum := by decide
  have hdescent : baseEnd_892999 < baseStart_892999 := by decide
  rcases family_descends (prefixWord ++ tailWord_892999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893016 : List Nat := [2, 1, 2, 2, 1, 4, 1, 5, 2]
def baseStart_893016 : Nat := 118140960795 + 893016 * 2 ^ 59
def prefixEnd_893016 : Nat := 4983230072969 + 3 ^ 40 * 893016 * 2
def baseEnd_893016 : Nat := 407596835693851826216089

theorem tailTrace_893016 : CollatzResearch.WordTrace tailWord_893016 prefixEnd_893016 407596835693851826216089 := by
  unfold tailWord_893016
  simp only [CollatzResearch.WordTrace]
  refine ⟨16285484666381510917785451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21713979555175347890380601 16285484666381510917785451)
  ·
    refine ⟨24428226999572266376678177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16285484666381510917785451 24428226999572266376678177)
    ·
      refine ⟨18321170249679199782508633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24428226999572266376678177 18321170249679199782508633)
      ·
        refine ⟨13740877687259399836881475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18321170249679199782508633 13740877687259399836881475)
        ·
          refine ⟨20611316530889099755322213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13740877687259399836881475 20611316530889099755322213)
          ·
            refine ⟨3864621849541706204122915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20611316530889099755322213 3864621849541706204122915)
            ·
              refine ⟨5796932774312559306184373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3864621849541706204122915 5796932774312559306184373)
              ·
                refine ⟨543462447591802434954785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5796932774312559306184373 543462447591802434954785)
                ·
                  refine ⟨407596835693851826216089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543462447591802434954785 407596835693851826216089)
                  ·
                    rfl

theorem cell20_893016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 2].length) (baseStart_893016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893016 prefixEnd_893016 := by exact prefixLift 893016
  have htrace : WordTrace (prefixWord ++ tailWord_893016) baseStart_893016 baseEnd_893016 := by
    simpa [prefixWord, tailWord_893016, baseEnd_893016] using wordTrace_append hprefix tailTrace_893016
  have hstable : (prefixWord ++ tailWord_893016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893016).length < 2 ^ (prefixWord ++ tailWord_893016).sum := by decide
  have hdescent : baseEnd_893016 < baseStart_893016 := by decide
  rcases family_descends (prefixWord ++ tailWord_893016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893022 : List Nat := [4, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_893022 : Nat := 118140960795 + 893022 * 2 ^ 59
def prefixEnd_893022 : Nat := 4983230072969 + 3 ^ 40 * 893022 * 2
def baseEnd_893022 : Nat := 407599574257342472016065

theorem tailTrace_893022 : CollatzResearch.WordTrace tailWord_893022 prefixEnd_893022 407599574257342472016065 := by
  unfold tailWord_893022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4071398521342660607536165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21714125447160856573526213 4071398521342660607536165)
  ·
    refine ⟨763387222751748863913031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4071398521342660607536165 763387222751748863913031)
    ·
      refine ⟨1145080834127623295869547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 763387222751748863913031 1145080834127623295869547)
      ·
        refine ⟨1717621251191434943804321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145080834127623295869547 1717621251191434943804321)
        ·
          refine ⟨1288215938393576207853241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1717621251191434943804321 1288215938393576207853241)
          ·
            refine ⟨966161953795182155889931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1288215938393576207853241 966161953795182155889931)
            ·
              refine ⟨1449242930692773233834897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966161953795182155889931 1449242930692773233834897)
              ·
                refine ⟨1086932198019579925376173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449242930692773233834897 1086932198019579925376173)
                ·
                  refine ⟨407599574257342472016065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1086932198019579925376173 407599574257342472016065)
                  ·
                    rfl

theorem cell20_893022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_893022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893022 prefixEnd_893022 := by exact prefixLift 893022
  have htrace : WordTrace (prefixWord ++ tailWord_893022) baseStart_893022 baseEnd_893022 := by
    simpa [prefixWord, tailWord_893022, baseEnd_893022] using wordTrace_append hprefix tailTrace_893022
  have hstable : (prefixWord ++ tailWord_893022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893022).length < 2 ^ (prefixWord ++ tailWord_893022).sum := by decide
  have hdescent : baseEnd_893022 < baseStart_893022 := by decide
  rcases family_descends (prefixWord ++ tailWord_893022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893047 : List Nat := [1, 1, 3, 1, 1, 6, 3, 1, 3]
def baseStart_893047 : Nat := 118140960795 + 893047 * 2 ^ 59
def prefixEnd_893047 : Nat := 4983230072969 + 3 ^ 40 * 893047 * 2
def baseEnd_893047 : Nat := 407610984938553496182629

theorem tailTrace_893047 : CollatzResearch.WordTrace tailWord_893047 prefixEnd_893047 407610984938553496182629 := by
  unfold tailWord_893047
  simp only [CollatzResearch.WordTrace]
  refine ⟨32572099995650714129949395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21714733330433809419966263 32572099995650714129949395)
  ·
    refine ⟨48858149993476071194924093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32572099995650714129949395 48858149993476071194924093)
    ·
      refine ⟨18321806247553526698096535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48858149993476071194924093 18321806247553526698096535)
      ·
        refine ⟨27482709371330290047144803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18321806247553526698096535 27482709371330290047144803)
        ·
          refine ⟨41224064056995435070717205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27482709371330290047144803 41224064056995435070717205)
          ·
            refine ⟨1932378002671661018939869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41224064056995435070717205 1932378002671661018939869)
            ·
              refine ⟨724641751001872882102451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1932378002671661018939869 724641751001872882102451)
              ·
                refine ⟨1086962626502809323153677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724641751001872882102451 1086962626502809323153677)
                ·
                  refine ⟨407610984938553496182629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1086962626502809323153677 407610984938553496182629)
                  ·
                    rfl

theorem cell20_893047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 3].length) (baseStart_893047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893047 prefixEnd_893047 := by exact prefixLift 893047
  have htrace : WordTrace (prefixWord ++ tailWord_893047) baseStart_893047 baseEnd_893047 := by
    simpa [prefixWord, tailWord_893047, baseEnd_893047] using wordTrace_append hprefix tailTrace_893047
  have hstable : (prefixWord ++ tailWord_893047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893047).length < 2 ^ (prefixWord ++ tailWord_893047).sum := by decide
  have hdescent : baseEnd_893047 < baseStart_893047 := by decide
  rcases family_descends (prefixWord ++ tailWord_893047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893057 : List Nat := [1, 2, 4, 2, 4, 1, 2, 4]
def baseStart_893057 : Nat := 118140960795 + 893057 * 2 ^ 59
def prefixEnd_893057 : Nat := 4983230072969 + 3 ^ 40 * 893057 * 2
def baseEnd_893057 : Nat := 135871849737012635283085

theorem tailTrace_893057 : CollatzResearch.WordTrace tailWord_893057 prefixEnd_893057 135871849737012635283085 := by
  unfold tailWord_893057
  simp only [CollatzResearch.WordTrace]
  refine ⟨32572464725614485837813425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21714976483742990558542283 32572464725614485837813425)
  ·
    refine ⟨24429348544210864378360069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32572464725614485837813425 24429348544210864378360069)
    ·
      refine ⟨4580502852039537070942513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24429348544210864378360069 4580502852039537070942513)
      ·
        refine ⟨3435377139029652803206885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4580502852039537070942513 3435377139029652803206885)
        ·
          refine ⟨644133213568059900601291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3435377139029652803206885 644133213568059900601291)
          ·
            refine ⟨966199820352089850901937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644133213568059900601291 966199820352089850901937)
            ·
              refine ⟨724649865264067388176453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 966199820352089850901937 724649865264067388176453)
              ·
                refine ⟨135871849737012635283085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 724649865264067388176453 135871849737012635283085)
                ·
                  rfl

theorem cell20_893057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 4].length) (baseStart_893057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893057 prefixEnd_893057 := by exact prefixLift 893057
  have htrace : WordTrace (prefixWord ++ tailWord_893057) baseStart_893057 baseEnd_893057 := by
    simpa [prefixWord, tailWord_893057, baseEnd_893057] using wordTrace_append hprefix tailTrace_893057
  have hstable : (prefixWord ++ tailWord_893057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893057).length < 2 ^ (prefixWord ++ tailWord_893057).sum := by decide
  have hdescent : baseEnd_893057 < baseStart_893057 := by decide
  rcases family_descends (prefixWord ++ tailWord_893057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893061 : List Nat := [1, 3, 1, 1, 5, 1, 4, 4]
def baseStart_893061 : Nat := 118140960795 + 893061 * 2 ^ 59
def prefixEnd_893061 : Nat := 4983230072969 + 3 ^ 40 * 893061 * 2
def baseEnd_893061 : Nat := 135872458306677223238635

theorem tailTrace_893061 : CollatzResearch.WordTrace tailWord_893061 prefixEnd_893061 135872458306677223238635 := by
  unfold tailWord_893061
  simp only [CollatzResearch.WordTrace]
  refine ⟨32572610617599994520959037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21715073745066663013972691 32572610617599994520959037)
  ·
    refine ⟨12214728981599997945359639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32572610617599994520959037 12214728981599997945359639)
    ·
      refine ⟨18322093472399996918039459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12214728981599997945359639 18322093472399996918039459)
      ·
        refine ⟨27483140208599995377059189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18322093472399996918039459 27483140208599995377059189)
        ·
          refine ⟨2576544394556249566599299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27483140208599995377059189 2576544394556249566599299)
          ·
            refine ⟨3864816591834374349898949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2576544394556249566599299 3864816591834374349898949)
            ·
              refine ⟨724653110968945190606053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3864816591834374349898949 724653110968945190606053)
              ·
                refine ⟨135872458306677223238635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 724653110968945190606053 135872458306677223238635)
                ·
                  rfl

theorem cell20_893061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 4].length) (baseStart_893061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893061 prefixEnd_893061 := by exact prefixLift 893061
  have htrace : WordTrace (prefixWord ++ tailWord_893061) baseStart_893061 baseEnd_893061 := by
    simpa [prefixWord, tailWord_893061, baseEnd_893061] using wordTrace_append hprefix tailTrace_893061
  have hstable : (prefixWord ++ tailWord_893061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893061).length < 2 ^ (prefixWord ++ tailWord_893061).sum := by decide
  have hdescent : baseEnd_893061 < baseStart_893061 := by decide
  rcases family_descends (prefixWord ++ tailWord_893061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893098 : List Nat := [3, 1, 5, 1, 3, 1, 2, 1, 3]
def baseStart_893098 : Nat := 118140960795 + 893098 * 2 ^ 59
def prefixEnd_893098 : Nat := 4983230072969 + 3 ^ 40 * 893098 * 2
def baseEnd_893098 : Nat := 407634262728223985482421

theorem tailTrace_893098 : CollatzResearch.WordTrace tailWord_893098 prefixEnd_893098 407634262728223985482421 := by
  unfold tailWord_893098
  simp only [CollatzResearch.WordTrace]
  refine ⟨8143490029616487460013987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21715973412310633226703965 8143490029616487460013987)
  ·
    refine ⟨12215235044424731190020981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8143490029616487460013987 12215235044424731190020981)
    ·
      refine ⟨1145178285414818549064467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12215235044424731190020981 1145178285414818549064467)
      ·
        refine ⟨1717767428122227823596701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145178285414818549064467 1717767428122227823596701)
        ·
          refine ⟨644162785545835433848763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1717767428122227823596701 644162785545835433848763)
          ·
            refine ⟨966244178318753150773145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644162785545835433848763 966244178318753150773145)
            ·
              refine ⟨724683133739064863079859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 966244178318753150773145 724683133739064863079859)
              ·
                refine ⟨1087024700608597294619789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724683133739064863079859 1087024700608597294619789)
                ·
                  refine ⟨407634262728223985482421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1087024700608597294619789 407634262728223985482421)
                  ·
                    rfl

theorem cell20_893098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_893098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893098 prefixEnd_893098 := by exact prefixLift 893098
  have htrace : WordTrace (prefixWord ++ tailWord_893098) baseStart_893098 baseEnd_893098 := by
    simpa [prefixWord, tailWord_893098, baseEnd_893098] using wordTrace_append hprefix tailTrace_893098
  have hstable : (prefixWord ++ tailWord_893098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893098).length < 2 ^ (prefixWord ++ tailWord_893098).sum := by decide
  have hdescent : baseEnd_893098 < baseStart_893098 := by decide
  rcases family_descends (prefixWord ++ tailWord_893098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893106 : List Nat := [3, 2, 1, 1, 1, 3, 3, 3, 3]
def baseStart_893106 : Nat := 118140960795 + 893106 * 2 ^ 59
def prefixEnd_893106 : Nat := 4983230072969 + 3 ^ 40 * 893106 * 2
def baseEnd_893106 : Nat := 407637914146211513215721

theorem tailTrace_893106 : CollatzResearch.WordTrace tailWord_893106 prefixEnd_893106 407637914146211513215721 := by
  unfold tailWord_893106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8143562975609241801586793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21716167934957978137564781 8143562975609241801586793)
  ·
    refine ⟨6107672231706931351190095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8143562975609241801586793 6107672231706931351190095)
    ·
      refine ⟨9161508347560397026785143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6107672231706931351190095 9161508347560397026785143)
      ·
        refine ⟨13742262521340595540177715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9161508347560397026785143 13742262521340595540177715)
        ·
          refine ⟨20613393782010893310266573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13742262521340595540177715 20613393782010893310266573)
          ·
            refine ⟨7730022668254084991349965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20613393782010893310266573 7730022668254084991349965)
            ·
              refine ⟨2898758500595281871756237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7730022668254084991349965 2898758500595281871756237)
              ·
                refine ⟨1087034437723230701908589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2898758500595281871756237 1087034437723230701908589)
                ·
                  refine ⟨407637914146211513215721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1087034437723230701908589 407637914146211513215721)
                  ·
                    rfl

theorem cell20_893106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_893106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893106 prefixEnd_893106 := by exact prefixLift 893106
  have htrace : WordTrace (prefixWord ++ tailWord_893106) baseStart_893106 baseEnd_893106 := by
    simpa [prefixWord, tailWord_893106, baseEnd_893106] using wordTrace_append hprefix tailTrace_893106
  have hstable : (prefixWord ++ tailWord_893106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893106).length < 2 ^ (prefixWord ++ tailWord_893106).sum := by decide
  have hdescent : baseEnd_893106 < baseStart_893106 := by decide
  rcases family_descends (prefixWord ++ tailWord_893106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893120 : List Nat := [2, 1, 1, 2, 5, 1, 2, 6]
def baseStart_893120 : Nat := 118140960795 + 893120 * 2 ^ 59
def prefixEnd_893120 : Nat := 4983230072969 + 3 ^ 40 * 893120 * 2
def baseEnd_893120 : Nat := 135881434709229895582999

theorem tailTrace_893120 : CollatzResearch.WordTrace tailWord_893120 prefixEnd_893120 135881434709229895582999 := by
  unfold tailWord_893120
  simp only [CollatzResearch.WordTrace]
  refine ⟨16287381262193123798678407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21716508349590831731571209 16287381262193123798678407)
  ·
    refine ⟨24431071893289685698017611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16287381262193123798678407 24431071893289685698017611)
    ·
      refine ⟨36646607839934528547026417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24431071893289685698017611 36646607839934528547026417)
      ·
        refine ⟨27484955879950896410269813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36646607839934528547026417 27484955879950896410269813)
        ·
          refine ⟨2576714613745396538462795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27484955879950896410269813 2576714613745396538462795)
          ·
            refine ⟨3865071920618094807694193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2576714613745396538462795 3865071920618094807694193)
            ·
              refine ⟨2898803940463571105770645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3865071920618094807694193 2898803940463571105770645)
              ·
                refine ⟨135881434709229895582999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2898803940463571105770645 135881434709229895582999)
                ·
                  rfl

theorem cell20_893120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_893120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893120 prefixEnd_893120 := by exact prefixLift 893120
  have htrace : WordTrace (prefixWord ++ tailWord_893120) baseStart_893120 baseEnd_893120 := by
    simpa [prefixWord, tailWord_893120, baseEnd_893120] using wordTrace_append hprefix tailTrace_893120
  have hstable : (prefixWord ++ tailWord_893120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893120).length < 2 ^ (prefixWord ++ tailWord_893120).sum := by decide
  have hdescent : baseEnd_893120 < baseStart_893120 := by decide
  rcases family_descends (prefixWord ++ tailWord_893120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893130 : List Nat := [3, 1, 2, 1, 3, 1, 2, 5, 2]
def baseStart_893130 : Nat := 118140960795 + 893130 * 2 ^ 59
def prefixEnd_893130 : Nat := 4983230072969 + 3 ^ 40 * 893130 * 2
def baseEnd_893130 : Nat := 407648868400174096415623

theorem tailTrace_893130 : CollatzResearch.WordTrace tailWord_893130 prefixEnd_893130 407648868400174096415623 := by
  unfold tailWord_893130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8143781813587504826305211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21716751502900012870147229 8143781813587504826305211)
  ·
    refine ⟨12215672720381257239457817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8143781813587504826305211 12215672720381257239457817)
    ·
      refine ⟨9161754540285942929593363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12215672720381257239457817 9161754540285942929593363)
      ·
        refine ⟨13742631810428914394390045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9161754540285942929593363 13742631810428914394390045)
        ·
          refine ⟨5153486928910842897896267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13742631810428914394390045 5153486928910842897896267)
          ·
            refine ⟨7730230393366264346844401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5153486928910842897896267 7730230393366264346844401)
            ·
              refine ⟨5797672795024698260133301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7730230393366264346844401 5797672795024698260133301)
              ·
                refine ⟨543531824533565461887497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5797672795024698260133301 543531824533565461887497)
                ·
                  refine ⟨407648868400174096415623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543531824533565461887497 407648868400174096415623)
                  ·
                    rfl

theorem cell20_893130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_893130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893130 prefixEnd_893130 := by exact prefixLift 893130
  have htrace : WordTrace (prefixWord ++ tailWord_893130) baseStart_893130 baseEnd_893130 := by
    simpa [prefixWord, tailWord_893130, baseEnd_893130] using wordTrace_append hprefix tailTrace_893130
  have hstable : (prefixWord ++ tailWord_893130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893130).length < 2 ^ (prefixWord ++ tailWord_893130).sum := by decide
  have hdescent : baseEnd_893130 < baseStart_893130 := by decide
  rcases family_descends (prefixWord ++ tailWord_893130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893144 : List Nat := [2, 1, 2, 2, 4, 1, 1, 4, 3]
def baseStart_893144 : Nat := 118140960795 + 893144 * 2 ^ 59
def prefixEnd_893144 : Nat := 4983230072969 + 3 ^ 40 * 893144 * 2
def baseEnd_893144 : Nat := 407655258381652269948899

theorem tailTrace_893144 : CollatzResearch.WordTrace tailWord_893144 prefixEnd_893144 407655258381652269948899 := by
  unfold tailWord_893144
  simp only [CollatzResearch.WordTrace]
  refine ⟨16287818938149649848115243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21717091917532866464153657 16287818938149649848115243)
  ·
    refine ⟨24431728407224474772172865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16287818938149649848115243 24431728407224474772172865)
    ·
      refine ⟨18323796305418356079129649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24431728407224474772172865 18323796305418356079129649)
      ·
        refine ⟨13742847229063767059347237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18323796305418356079129649 13742847229063767059347237)
        ·
          refine ⟨2576783855449456323627607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13742847229063767059347237 2576783855449456323627607)
          ·
            refine ⟨3865175783174184485441411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2576783855449456323627607 3865175783174184485441411)
            ·
              refine ⟨5797763674761276728162117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3865175783174184485441411 5797763674761276728162117)
              ·
                refine ⟨1087080689017739386530397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5797763674761276728162117 1087080689017739386530397)
                ·
                  refine ⟨407655258381652269948899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1087080689017739386530397 407655258381652269948899)
                  ·
                    rfl

theorem cell20_893144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_893144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893144 prefixEnd_893144 := by exact prefixLift 893144
  have htrace : WordTrace (prefixWord ++ tailWord_893144) baseStart_893144 baseEnd_893144 := by
    simpa [prefixWord, tailWord_893144, baseEnd_893144] using wordTrace_append hprefix tailTrace_893144
  have hstable : (prefixWord ++ tailWord_893144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893144).length < 2 ^ (prefixWord ++ tailWord_893144).sum := by decide
  have hdescent : baseEnd_893144 < baseStart_893144 := by decide
  rcases family_descends (prefixWord ++ tailWord_893144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893182 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_893182 : Nat := 118140960795 + 893182 * 2 ^ 59
def prefixEnd_893182 : Nat := 4983230072969 + 3 ^ 40 * 893182 * 2
def baseEnd_893182 : Nat := 407672602617093026682077

theorem tailTrace_893182 : CollatzResearch.WordTrace tailWord_893182 prefixEnd_893182 407672602617093026682077 := by
  unfold tailWord_893182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4072127981270204023264225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21718015900107754790742533 4072127981270204023264225)
  ·
    refine ⟨3054095985952653017448169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4072127981270204023264225 3054095985952653017448169)
    ·
      refine ⟨2290571989464489763086127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3054095985952653017448169 2290571989464489763086127)
      ·
        refine ⟨3435857984196734644629191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2290571989464489763086127 3435857984196734644629191)
        ·
          refine ⟨5153786976295101966943787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3435857984196734644629191 5153786976295101966943787)
          ·
            refine ⟨7730680464442652950415681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5153786976295101966943787 7730680464442652950415681)
            ·
              refine ⟨5798010348331989712811761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7730680464442652950415681 5798010348331989712811761)
              ·
                refine ⟨4348507761248992284608821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5798010348331989712811761 4348507761248992284608821)
                ·
                  refine ⟨407672602617093026682077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4348507761248992284608821 407672602617093026682077)
                  ·
                    rfl

theorem cell20_893182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_893182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893182 prefixEnd_893182 := by exact prefixLift 893182
  have htrace : WordTrace (prefixWord ++ tailWord_893182) baseStart_893182 baseEnd_893182 := by
    simpa [prefixWord, tailWord_893182, baseEnd_893182] using wordTrace_append hprefix tailTrace_893182
  have hstable : (prefixWord ++ tailWord_893182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893182).length < 2 ^ (prefixWord ++ tailWord_893182).sum := by decide
  have hdescent : baseEnd_893182 < baseStart_893182 := by decide
  rcases family_descends (prefixWord ++ tailWord_893182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893230 : List Nat := [4, 1, 3, 3, 1, 1, 1, 6]
def baseStart_893230 : Nat := 118140960795 + 893230 * 2 ^ 59
def prefixEnd_893230 : Nat := 4983230072969 + 3 ^ 40 * 893230 * 2
def baseEnd_893230 : Nat := 135898170375006064360627

theorem tailTrace_893230 : CollatzResearch.WordTrace tailWord_893230 prefixEnd_893230 135898170375006064360627 := by
  unfold tailWord_893230
  simp only [CollatzResearch.WordTrace]
  refine ⟨4072346819248467047982643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21719183035991824255907429 4072346819248467047982643)
  ·
    refine ⟨6108520228872700571973965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4072346819248467047982643 6108520228872700571973965)
    ·
      refine ⟨2290695085827262714490237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6108520228872700571973965 2290695085827262714490237)
      ·
        refine ⟨859010657185223517933839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2290695085827262714490237 859010657185223517933839)
        ·
          refine ⟨1288515985777835276900759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859010657185223517933839 1288515985777835276900759)
          ·
            refine ⟨1932773978666752915351139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288515985777835276900759 1932773978666752915351139)
            ·
              refine ⟨2899160968000129373026709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1932773978666752915351139 2899160968000129373026709)
              ·
                refine ⟨135898170375006064360627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2899160968000129373026709 135898170375006064360627)
                ·
                  rfl

theorem cell20_893230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_893230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893230 prefixEnd_893230 := by exact prefixLift 893230
  have htrace : WordTrace (prefixWord ++ tailWord_893230) baseStart_893230 baseEnd_893230 := by
    simpa [prefixWord, tailWord_893230, baseEnd_893230] using wordTrace_append hprefix tailTrace_893230
  have hstable : (prefixWord ++ tailWord_893230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893230).length < 2 ^ (prefixWord ++ tailWord_893230).sum := by decide
  have hdescent : baseEnd_893230 < baseStart_893230 := by decide
  rcases family_descends (prefixWord ++ tailWord_893230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893265 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 4]
def baseStart_893265 : Nat := 118140960795 + 893265 * 2 ^ 59
def prefixEnd_893265 : Nat := 4983230072969 + 3 ^ 40 * 893265 * 2
def baseEnd_893265 : Nat := 407710486078713626915071

theorem tailTrace_893265 : CollatzResearch.WordTrace tailWord_893265 prefixEnd_893265 407710486078713626915071 := by
  unfold tailWord_893265
  simp only [CollatzResearch.WordTrace]
  refine ⟨32580051108860937361385249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21720034072573958240923499 32580051108860937361385249)
  ·
    refine ⟨24435038331645703021038937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32580051108860937361385249 24435038331645703021038937)
    ·
      refine ⟨18326278748734277265779203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24435038331645703021038937 18326278748734277265779203)
      ·
        refine ⟨27489418123101415898668805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18326278748734277265779203 27489418123101415898668805)
        ·
          refine ⟨5154265898081515481000401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27489418123101415898668805 5154265898081515481000401)
          ·
            refine ⟨3865699423561136610750301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5154265898081515481000401 3865699423561136610750301)
            ·
              refine ⟨1449637283835426229031363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3865699423561136610750301 1449637283835426229031363)
              ·
                refine ⟨2174455925753139343547045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1449637283835426229031363 2174455925753139343547045)
                ·
                  refine ⟨407710486078713626915071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2174455925753139343547045 407710486078713626915071)
                  ·
                    rfl

theorem cell20_893265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_893265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893265 prefixEnd_893265 := by exact prefixLift 893265
  have htrace : WordTrace (prefixWord ++ tailWord_893265) baseStart_893265 baseEnd_893265 := by
    simpa [prefixWord, tailWord_893265, baseEnd_893265] using wordTrace_append hprefix tailTrace_893265
  have hstable : (prefixWord ++ tailWord_893265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893265).length < 2 ^ (prefixWord ++ tailWord_893265).sum := by decide
  have hdescent : baseEnd_893265 < baseStart_893265 := by decide
  rcases family_descends (prefixWord ++ tailWord_893265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893310 : List Nat := [4, 2, 3, 11]
def baseStart_893310 : Nat := 118140960795 + 893310 * 2 ^ 59
def prefixEnd_893310 : Nat := 4983230072969 + 3 ^ 40 * 893310 * 2
def baseEnd_893310 : Nat := 1677905453929602758909

theorem tailTrace_893310 : CollatzResearch.WordTrace tailWord_893310 prefixEnd_893310 1677905453929602758909 := by
  unfold tailWord_893310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4072711549212238755846673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21721128262465273364515589 4072711549212238755846673)
  ·
    refine ⟨3054533661909179066885005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4072711549212238755846673 3054533661909179066885005)
    ·
      refine ⟨1145450123215942150081877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3054533661909179066885005 1145450123215942150081877)
      ·
        refine ⟨1677905453929602758909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1145450123215942150081877 1677905453929602758909)
        ·
          rfl

theorem cell20_893310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 11].length) (baseStart_893310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893310 prefixEnd_893310 := by exact prefixLift 893310
  have htrace : WordTrace (prefixWord ++ tailWord_893310) baseStart_893310 baseEnd_893310 := by
    simpa [prefixWord, tailWord_893310, baseEnd_893310] using wordTrace_append hprefix tailTrace_893310
  have hstable : (prefixWord ++ tailWord_893310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893310).length < 2 ^ (prefixWord ++ tailWord_893310).sum := by decide
  have hdescent : baseEnd_893310 < baseStart_893310 := by decide
  rcases family_descends (prefixWord ++ tailWord_893310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893313 : List Nat := [1, 2, 4, 3, 1, 2, 2, 2, 3]
def baseStart_893313 : Nat := 118140960795 + 893313 * 2 ^ 59
def prefixEnd_893313 : Nat := 4983230072969 + 3 ^ 40 * 893313 * 2
def baseEnd_893313 : Nat := 407732394586638793314875

theorem tailTrace_893313 : CollatzResearch.WordTrace tailWord_893313 prefixEnd_893313 407732394586638793314875 := by
  unfold tailWord_893313
  simp only [CollatzResearch.WordTrace]
  refine ⟨32581801812687041559132593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21721201208458027706088395 32581801812687041559132593)
  ·
    refine ⟨24436351359515281169349445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32581801812687041559132593 24436351359515281169349445)
    ·
      refine ⟨4581815879909115219253021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24436351359515281169349445 4581815879909115219253021)
      ·
        refine ⟨1718180954965918207219883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4581815879909115219253021 1718180954965918207219883)
        ·
          refine ⟨2577271432448877310829825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718180954965918207219883 2577271432448877310829825)
          ·
            refine ⟨1932953574336657983122369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2577271432448877310829825 1932953574336657983122369)
            ·
              refine ⟨1449715180752493487341777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1932953574336657983122369 1449715180752493487341777)
              ·
                refine ⟨1087286385564370115506333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449715180752493487341777 1087286385564370115506333)
                ·
                  refine ⟨407732394586638793314875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1087286385564370115506333 407732394586638793314875)
                  ·
                    rfl

theorem cell20_893313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_893313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893313 prefixEnd_893313 := by exact prefixLift 893313
  have htrace : WordTrace (prefixWord ++ tailWord_893313) baseStart_893313 baseEnd_893313 := by
    simpa [prefixWord, tailWord_893313, baseEnd_893313] using wordTrace_append hprefix tailTrace_893313
  have hstable : (prefixWord ++ tailWord_893313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893313).length < 2 ^ (prefixWord ++ tailWord_893313).sum := by decide
  have hdescent : baseEnd_893313 < baseStart_893313 := by decide
  rcases family_descends (prefixWord ++ tailWord_893313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893320 : List Nat := [2, 1, 3, 3, 1, 1, 3, 4, 2]
def baseStart_893320 : Nat := 118140960795 + 893320 * 2 ^ 59
def prefixEnd_893320 : Nat := 4983230072969 + 3 ^ 40 * 893320 * 2
def baseEnd_893320 : Nat := 407735589577377880081513

theorem tailTrace_893320 : CollatzResearch.WordTrace tailWord_893320 prefixEnd_893320 407735589577377880081513 := by
  unfold tailWord_893320
  simp only [CollatzResearch.WordTrace]
  refine ⟨16291028561830840877318707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21721371415774454503091609 16291028561830840877318707)
  ·
    refine ⟨24436542842746261315978061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16291028561830840877318707 24436542842746261315978061)
    ·
      refine ⟨9163703566029847993491773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24436542842746261315978061 9163703566029847993491773)
      ·
        refine ⟨3436388837261192997559415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9163703566029847993491773 3436388837261192997559415)
        ·
          refine ⟨5154583255891789496339123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436388837261192997559415 5154583255891789496339123)
          ·
            refine ⟨7731874883837684244508685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154583255891789496339123 7731874883837684244508685)
            ·
              refine ⟨2899453081439131591690757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7731874883837684244508685 2899453081439131591690757)
              ·
                refine ⟨543647452769837173442017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2899453081439131591690757 543647452769837173442017)
                ·
                  refine ⟨407735589577377880081513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543647452769837173442017 407735589577377880081513)
                  ·
                    rfl

theorem cell20_893320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 2].length) (baseStart_893320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893320 prefixEnd_893320 := by exact prefixLift 893320
  have htrace : WordTrace (prefixWord ++ tailWord_893320) baseStart_893320 baseEnd_893320 := by
    simpa [prefixWord, tailWord_893320, baseEnd_893320] using wordTrace_append hprefix tailTrace_893320
  have hstable : (prefixWord ++ tailWord_893320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893320).length < 2 ^ (prefixWord ++ tailWord_893320).sum := by decide
  have hdescent : baseEnd_893320 < baseStart_893320 := by decide
  rcases family_descends (prefixWord ++ tailWord_893320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893362 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_893362 : Nat := 118140960795 + 893362 * 2 ^ 59
def prefixEnd_893362 : Nat := 4983230072969 + 3 ^ 40 * 893362 * 2
def baseEnd_893362 : Nat := 407754759521812400681341

theorem tailTrace_893362 : CollatzResearch.WordTrace tailWord_893362 prefixEnd_893362 407754759521812400681341 := by
  unfold tailWord_893362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8145897247377380731916585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21722392659673015285110893 8145897247377380731916585)
  ·
    refine ⟨6109422935533035548937439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8145897247377380731916585 6109422935533035548937439)
    ·
      refine ⟨9164134403299553323406159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6109422935533035548937439 9164134403299553323406159)
      ·
        refine ⟨13746201604949329985109239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9164134403299553323406159 13746201604949329985109239)
        ·
          refine ⟨20619302407423994977663859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13746201604949329985109239 20619302407423994977663859)
          ·
            refine ⟨30928953611135992466495789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20619302407423994977663859 30928953611135992466495789)
            ·
              refine ⟨11598357604175997174935921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30928953611135992466495789 11598357604175997174935921)
              ·
                refine ⟨8698768203131997881201941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11598357604175997174935921 8698768203131997881201941)
                ·
                  refine ⟨407754759521812400681341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8698768203131997881201941 407754759521812400681341)
                  ·
                    rfl

theorem cell20_893362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_893362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893362 prefixEnd_893362 := by exact prefixLift 893362
  have htrace : WordTrace (prefixWord ++ tailWord_893362) baseStart_893362 baseEnd_893362 := by
    simpa [prefixWord, tailWord_893362, baseEnd_893362] using wordTrace_append hprefix tailTrace_893362
  have hstable : (prefixWord ++ tailWord_893362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893362).length < 2 ^ (prefixWord ++ tailWord_893362).sum := by decide
  have hdescent : baseEnd_893362 < baseStart_893362 := by decide
  rcases family_descends (prefixWord ++ tailWord_893362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893364 : List Nat := [2, 5, 2, 2, 2, 1, 1, 2, 3]
def baseStart_893364 : Nat := 118140960795 + 893364 * 2 ^ 59
def prefixEnd_893364 : Nat := 4983230072969 + 3 ^ 40 * 893364 * 2
def baseEnd_893364 : Nat := 407755672376309282614667

theorem tailTrace_893364 : CollatzResearch.WordTrace tailWord_893364 prefixEnd_893364 407755672376309282614667 := by
  unfold tailWord_893364
  simp only [CollatzResearch.WordTrace]
  refine ⟨16291830967751138634619573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21722441290334851512826097 16291830967751138634619573)
  ·
    refine ⟨1527359153226669246995585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16291830967751138634619573 1527359153226669246995585)
    ·
      refine ⟨1145519364920001935246689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1527359153226669246995585 1145519364920001935246689)
      ·
        refine ⟨859139523690001451435017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1145519364920001935246689 859139523690001451435017)
        ·
          refine ⟨644354642767501088576263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 859139523690001451435017 644354642767501088576263)
          ·
            refine ⟨966531964151251632864395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644354642767501088576263 966531964151251632864395)
            ·
              refine ⟨1449797946226877449296593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966531964151251632864395 1449797946226877449296593)
              ·
                refine ⟨1087348459670158086972445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449797946226877449296593 1087348459670158086972445)
                ·
                  refine ⟨407755672376309282614667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1087348459670158086972445 407755672376309282614667)
                  ·
                    rfl

theorem cell20_893364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_893364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893364 prefixEnd_893364 := by exact prefixLift 893364
  have htrace : WordTrace (prefixWord ++ tailWord_893364) baseStart_893364 baseEnd_893364 := by
    simpa [prefixWord, tailWord_893364, baseEnd_893364] using wordTrace_append hprefix tailTrace_893364
  have hstable : (prefixWord ++ tailWord_893364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893364).length < 2 ^ (prefixWord ++ tailWord_893364).sum := by decide
  have hdescent : baseEnd_893364 < baseStart_893364 := by decide
  rcases family_descends (prefixWord ++ tailWord_893364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893372 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 5]
def baseStart_893372 : Nat := 118140960795 + 893372 * 2 ^ 59
def prefixEnd_893372 : Nat := 4983230072969 + 3 ^ 40 * 893372 * 2
def baseEnd_893372 : Nat := 407759323794296810347967

theorem tailTrace_893372 : CollatzResearch.WordTrace tailWord_893372 prefixEnd_893372 407759323794296810347967 := by
  unfold tailWord_893372
  simp only [CollatzResearch.WordTrace]
  refine ⟨16291976859736647317765185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21722635812982196423686913 16291976859736647317765185)
  ·
    refine ⟨12218982644802485488323889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16291976859736647317765185 12218982644802485488323889)
    ·
      refine ⟨9164236983601864116242917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12218982644802485488323889 9164236983601864116242917)
      ·
        refine ⟨1718294434425349521795547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9164236983601864116242917 1718294434425349521795547)
        ·
          refine ⟨2577441651638024282693321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718294434425349521795547 2577441651638024282693321)
          ·
            refine ⟨1933081238728518212019991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2577441651638024282693321 1933081238728518212019991)
            ·
              refine ⟨2899621858092777318029987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1933081238728518212019991 2899621858092777318029987)
              ·
                refine ⟨4349432787139165977044981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2899621858092777318029987 4349432787139165977044981)
                ·
                  refine ⟨407759323794296810347967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4349432787139165977044981 407759323794296810347967)
                  ·
                    rfl

theorem cell20_893372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_893372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893372 prefixEnd_893372 := by exact prefixLift 893372
  have htrace : WordTrace (prefixWord ++ tailWord_893372) baseStart_893372 baseEnd_893372 := by
    simpa [prefixWord, tailWord_893372, baseEnd_893372] using wordTrace_append hprefix tailTrace_893372
  have hstable : (prefixWord ++ tailWord_893372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893372).length < 2 ^ (prefixWord ++ tailWord_893372).sum := by decide
  have hdescent : baseEnd_893372 < baseStart_893372 := by decide
  rcases family_descends (prefixWord ++ tailWord_893372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893393 : List Nat := [1, 2, 2, 1, 2, 1, 1, 7, 3]
def baseStart_893393 : Nat := 118140960795 + 893393 * 2 ^ 59
def prefixEnd_893393 : Nat := 4983230072969 + 3 ^ 40 * 893393 * 2
def baseEnd_893393 : Nat := 407768908766514070647881

theorem tailTrace_893393 : CollatzResearch.WordTrace tailWord_893393 prefixEnd_893393 407768908766514070647881 := by
  unfold tailWord_893393
  simp only [CollatzResearch.WordTrace]
  refine ⟨32584719652397215222044833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21723146434931476814696555 32584719652397215222044833)
  ·
    refine ⟨24438539739297911416533625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32584719652397215222044833 24438539739297911416533625)
    ·
      refine ⟨18328904804473433562400219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24438539739297911416533625 18328904804473433562400219)
      ·
        refine ⟨27493357206710150343600329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18328904804473433562400219 27493357206710150343600329)
        ·
          refine ⟨20620017905032612757700247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27493357206710150343600329 20620017905032612757700247)
          ·
            refine ⟨30930026857548919136550371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20620017905032612757700247 30930026857548919136550371)
            ·
              refine ⟨46395040286323378704825557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30930026857548919136550371 46395040286323378704825557)
              ·
                refine ⟨1087383756710704188394349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 46395040286323378704825557 1087383756710704188394349)
                ·
                  refine ⟨407768908766514070647881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1087383756710704188394349 407768908766514070647881)
                  ·
                    rfl

theorem cell20_893393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_893393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893393 prefixEnd_893393 := by exact prefixLift 893393
  have htrace : WordTrace (prefixWord ++ tailWord_893393) baseStart_893393 baseEnd_893393 := by
    simpa [prefixWord, tailWord_893393, baseEnd_893393] using wordTrace_append hprefix tailTrace_893393
  have hstable : (prefixWord ++ tailWord_893393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893393).length < 2 ^ (prefixWord ++ tailWord_893393).sum := by decide
  have hdescent : baseEnd_893393 < baseStart_893393 := by decide
  rcases family_descends (prefixWord ++ tailWord_893393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893417 : List Nat := [1, 2, 1, 1, 1, 2, 1, 9, 2]
def baseStart_893417 : Nat := 118140960795 + 893417 * 2 ^ 59
def prefixEnd_893417 : Nat := 4983230072969 + 3 ^ 40 * 893417 * 2
def baseEnd_893417 : Nat := 407779863020476653847783

theorem tailTrace_893417 : CollatzResearch.WordTrace tailWord_893417 prefixEnd_893417 407779863020476653847783 := by
  unfold tailWord_893417
  simp only [CollatzResearch.WordTrace]
  refine ⟨32585595004310267320918505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21723730002873511547279003 32585595004310267320918505)
  ·
    refine ⟨24439196253232700490688879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32585595004310267320918505 24439196253232700490688879)
    ·
      refine ⟨36658794379849050736033319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24439196253232700490688879 36658794379849050736033319)
      ·
        refine ⟨54988191569773576104049979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36658794379849050736033319 54988191569773576104049979)
        ·
          refine ⟨82482287354660364156074969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54988191569773576104049979 82482287354660364156074969)
          ·
            refine ⟨61861715515995273117056227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82482287354660364156074969 61861715515995273117056227)
            ·
              refine ⟨92792573273992909675584341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61861715515995273117056227 92792573273992909675584341)
              ·
                refine ⟨543706484027302205130377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 92792573273992909675584341 543706484027302205130377)
                ·
                  refine ⟨407779863020476653847783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543706484027302205130377 407779863020476653847783)
                  ·
                    rfl

theorem cell20_893417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 2].length) (baseStart_893417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893417 prefixEnd_893417 := by exact prefixLift 893417
  have htrace : WordTrace (prefixWord ++ tailWord_893417) baseStart_893417 baseEnd_893417 := by
    simpa [prefixWord, tailWord_893417, baseEnd_893417] using wordTrace_append hprefix tailTrace_893417
  have hstable : (prefixWord ++ tailWord_893417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893417).length < 2 ^ (prefixWord ++ tailWord_893417).sum := by decide
  have hdescent : baseEnd_893417 < baseStart_893417 := by decide
  rcases family_descends (prefixWord ++ tailWord_893417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893444 : List Nat := [2, 3, 2, 3, 1, 3, 2, 1, 3]
def baseStart_893444 : Nat := 118140960795 + 893444 * 2 ^ 59
def prefixEnd_893444 : Nat := 4983230072969 + 3 ^ 40 * 893444 * 2
def baseEnd_893444 : Nat := 407792186556184559947673

theorem tailTrace_893444 : CollatzResearch.WordTrace tailWord_893444 prefixEnd_893444 407792186556184559947673 := by
  unfold tailWord_893444
  simp only [CollatzResearch.WordTrace]
  refine ⟨16293289887606225466075693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21724386516808300621434257 16293289887606225466075693)
  ·
    refine ⟨6109983707852334549778385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16293289887606225466075693 6109983707852334549778385)
    ·
      refine ⟨4582487780889250912333789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6109983707852334549778385 4582487780889250912333789)
      ·
        refine ⟨1718432917833469092125171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4582487780889250912333789 1718432917833469092125171)
        ·
          refine ⟨2577649376750203638187757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718432917833469092125171 2577649376750203638187757)
          ·
            refine ⟨966618516281326364320409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2577649376750203638187757 966618516281326364320409)
            ·
              refine ⟨724963887210994773240307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 966618516281326364320409 724963887210994773240307)
              ·
                refine ⟨1087445830816492159860461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724963887210994773240307 1087445830816492159860461)
                ·
                  refine ⟨407792186556184559947673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1087445830816492159860461 407792186556184559947673)
                  ·
                    rfl

theorem cell20_893444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_893444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893444 prefixEnd_893444 := by exact prefixLift 893444
  have htrace : WordTrace (prefixWord ++ tailWord_893444) baseStart_893444 baseEnd_893444 := by
    simpa [prefixWord, tailWord_893444, baseEnd_893444] using wordTrace_append hprefix tailTrace_893444
  have hstable : (prefixWord ++ tailWord_893444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893444).length < 2 ^ (prefixWord ++ tailWord_893444).sum := by decide
  have hdescent : baseEnd_893444 < baseStart_893444 := by decide
  rcases family_descends (prefixWord ++ tailWord_893444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893445 : List Nat := [1, 3, 1, 1, 2, 2, 3, 7]
def baseStart_893445 : Nat := 118140960795 + 893445 * 2 ^ 59
def prefixEnd_893445 : Nat := 4983230072969 + 3 ^ 40 * 893445 * 2
def baseEnd_893445 : Nat := 135930880994477666971445

theorem tailTrace_893445 : CollatzResearch.WordTrace tailWord_893445 prefixEnd_893445 135930880994477666971445 := by
  unfold tailWord_893445
  simp only [CollatzResearch.WordTrace]
  refine ⟨32586616248208828102937789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21724410832139218735291859 32586616248208828102937789)
  ·
    refine ⟨12219981093078310538601671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32586616248208828102937789 12219981093078310538601671)
    ·
      refine ⟨18329971639617465807902507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12219981093078310538601671 18329971639617465807902507)
      ·
        refine ⟨27494957459426198711853761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18329971639617465807902507 27494957459426198711853761)
        ·
          refine ⟨20621218094569649033890321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27494957459426198711853761 20621218094569649033890321)
          ·
            refine ⟨15465913570927236775417741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20621218094569649033890321 15465913570927236775417741)
            ·
              refine ⟨5799717589097713790781653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15465913570927236775417741 5799717589097713790781653)
              ·
                refine ⟨135930880994477666971445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5799717589097713790781653 135930880994477666971445)
                ·
                  rfl

theorem cell20_893445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 7].length) (baseStart_893445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893445 prefixEnd_893445 := by exact prefixLift 893445
  have htrace : WordTrace (prefixWord ++ tailWord_893445) baseStart_893445 baseEnd_893445 := by
    simpa [prefixWord, tailWord_893445, baseEnd_893445] using wordTrace_append hprefix tailTrace_893445
  have hstable : (prefixWord ++ tailWord_893445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893445).length < 2 ^ (prefixWord ++ tailWord_893445).sum := by decide
  have hdescent : baseEnd_893445 < baseStart_893445 := by decide
  rcases family_descends (prefixWord ++ tailWord_893445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893479 : List Nat := [1, 1, 7, 2, 1, 8]
def baseStart_893479 : Nat := 118140960795 + 893479 * 2 ^ 59
def prefixEnd_893479 : Nat := 4983230072969 + 3 ^ 40 * 893479 * 2
def baseEnd_893479 : Nat := 15104005981847407177069

theorem tailTrace_893479 : CollatzResearch.WordTrace tailWord_893479 prefixEnd_893479 15104005981847407177069 := by
  unfold tailWord_893479
  simp only [CollatzResearch.WordTrace]
  refine ⟨32587856330085651909675491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21725237553390434606450327 32587856330085651909675491)
  ·
    refine ⟨48881784495128477864513237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32587856330085651909675491 48881784495128477864513237)
    ·
      refine ⟨1145666824104573699949529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 48881784495128477864513237 1145666824104573699949529)
      ·
        refine ⟨859250118078430274962147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1145666824104573699949529 859250118078430274962147)
        ·
          refine ⟨1288875177117645412443221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859250118078430274962147 1288875177117645412443221)
          ·
            refine ⟨15104005981847407177069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1288875177117645412443221 15104005981847407177069)
            ·
              rfl

theorem cell20_893479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 8].length) (baseStart_893479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893479 prefixEnd_893479 := by exact prefixLift 893479
  have htrace : WordTrace (prefixWord ++ tailWord_893479) baseStart_893479 baseEnd_893479 := by
    simpa [prefixWord, tailWord_893479, baseEnd_893479] using wordTrace_append hprefix tailTrace_893479
  have hstable : (prefixWord ++ tailWord_893479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893479).length < 2 ^ (prefixWord ++ tailWord_893479).sum := by decide
  have hdescent : baseEnd_893479 < baseStart_893479 := by decide
  rcases family_descends (prefixWord ++ tailWord_893479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893485 : List Nat := [1, 5, 4, 1, 1, 1, 1, 4, 2]
def baseStart_893485 : Nat := 118140960795 + 893485 * 2 ^ 59
def prefixEnd_893485 : Nat := 4983230072969 + 3 ^ 40 * 893485 * 2
def baseEnd_893485 : Nat := 407810900073370639580839

theorem tailTrace_893485 : CollatzResearch.WordTrace tailWord_893485 prefixEnd_893485 407810900073370639580839 := by
  unfold tailWord_893485
  simp only [CollatzResearch.WordTrace]
  refine ⟨32588075168063914934393909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21725383445375943289595939 32588075168063914934393909)
  ·
    refine ⟨3055132047005992025099429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32588075168063914934393909 3055132047005992025099429)
    ·
      refine ⟨572837258813623504706143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3055132047005992025099429 572837258813623504706143)
      ·
        refine ⟨859255888220435257059215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572837258813623504706143 859255888220435257059215)
        ·
          refine ⟨1288883832330652885588823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859255888220435257059215 1288883832330652885588823)
          ·
            refine ⟨1933325748495979328383235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288883832330652885588823 1933325748495979328383235)
            ·
              refine ⟨2899988622743968992574853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1933325748495979328383235 2899988622743968992574853)
              ·
                refine ⟨543747866764494186107785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2899988622743968992574853 543747866764494186107785)
                ·
                  refine ⟨407810900073370639580839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543747866764494186107785 407810900073370639580839)
                  ·
                    rfl

theorem cell20_893485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_893485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893485 prefixEnd_893485 := by exact prefixLift 893485
  have htrace : WordTrace (prefixWord ++ tailWord_893485) baseStart_893485 baseEnd_893485 := by
    simpa [prefixWord, tailWord_893485, baseEnd_893485] using wordTrace_append hprefix tailTrace_893485
  have hstable : (prefixWord ++ tailWord_893485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893485).length < 2 ^ (prefixWord ++ tailWord_893485).sum := by decide
  have hdescent : baseEnd_893485 < baseStart_893485 := by decide
  rcases family_descends (prefixWord ++ tailWord_893485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893500 : List Nat := [2, 2, 2, 2, 3, 1, 3, 5]
def baseStart_893500 : Nat := 118140960795 + 893500 * 2 ^ 59
def prefixEnd_893500 : Nat := 4983230072969 + 3 ^ 40 * 893500 * 2
def baseEnd_893500 : Nat := 135939248827365751360259

theorem tailTrace_893500 : CollatzResearch.WordTrace tailWord_893500 prefixEnd_893500 135939248827365751360259 := by
  unfold tailWord_893500
  simp only [CollatzResearch.WordTrace]
  refine ⟨16294311131504786248094977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21725748175339714997459969 16294311131504786248094977)
  ·
    refine ⟨12220733348628589686071233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16294311131504786248094977 12220733348628589686071233)
    ·
      refine ⟨9165550011471442264553425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12220733348628589686071233 9165550011471442264553425)
      ·
        refine ⟨6874162508603581698415069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9165550011471442264553425 6874162508603581698415069)
        ·
          refine ⟨2577810940726343136905651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6874162508603581698415069 2577810940726343136905651)
          ·
            refine ⟨3866716411089514705358477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577810940726343136905651 3866716411089514705358477)
            ·
              refine ⟨1450018654158568014509429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3866716411089514705358477 1450018654158568014509429)
              ·
                refine ⟨135939248827365751360259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1450018654158568014509429 135939248827365751360259)
                ·
                  rfl

theorem cell20_893500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_893500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893500 prefixEnd_893500 := by exact prefixLift 893500
  have htrace : WordTrace (prefixWord ++ tailWord_893500) baseStart_893500 baseEnd_893500 := by
    simpa [prefixWord, tailWord_893500, baseEnd_893500] using wordTrace_append hprefix tailTrace_893500
  have hstable : (prefixWord ++ tailWord_893500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893500).length < 2 ^ (prefixWord ++ tailWord_893500).sum := by decide
  have hdescent : baseEnd_893500 < baseStart_893500 := by decide
  rcases family_descends (prefixWord ++ tailWord_893500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893510 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_893510 : Nat := 118140960795 + 893510 * 2 ^ 59
def prefixEnd_893510 : Nat := 4983230072969 + 3 ^ 40 * 893510 * 2
def baseEnd_893510 : Nat := 407822310754581663747403

theorem tailTrace_893510 : CollatzResearch.WordTrace tailWord_893510 prefixEnd_893510 407822310754581663747403 := by
  unfold tailWord_893510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018405843530417006376687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21725991328648896136035989 1018405843530417006376687)
  ·
    refine ⟨1527608765295625509565031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1018405843530417006376687 1527608765295625509565031)
    ·
      refine ⟨2291413147943438264347547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1527608765295625509565031 2291413147943438264347547)
      ·
        refine ⟨3437119721915157396521321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2291413147943438264347547 3437119721915157396521321)
        ·
          refine ⟨2577839791436368047390991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3437119721915157396521321 2577839791436368047390991)
          ·
            refine ⟨3866759687154552071086487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577839791436368047390991 3866759687154552071086487)
            ·
              refine ⟨5800139530731828106629731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3866759687154552071086487 5800139530731828106629731)
              ·
                refine ⟨8700209296097742159944597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5800139530731828106629731 8700209296097742159944597)
                ·
                  refine ⟨407822310754581663747403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8700209296097742159944597 407822310754581663747403)
                  ·
                    rfl

theorem cell20_893510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_893510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893510 prefixEnd_893510 := by exact prefixLift 893510
  have htrace : WordTrace (prefixWord ++ tailWord_893510) baseStart_893510 baseEnd_893510 := by
    simpa [prefixWord, tailWord_893510, baseEnd_893510] using wordTrace_append hprefix tailTrace_893510
  have hstable : (prefixWord ++ tailWord_893510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893510).length < 2 ^ (prefixWord ++ tailWord_893510).sum := by decide
  have hdescent : baseEnd_893510 < baseStart_893510 := by decide
  rcases family_descends (prefixWord ++ tailWord_893510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893514 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_893514 : Nat := 118140960795 + 893514 * 2 ^ 59
def prefixEnd_893514 : Nat := 4983230072969 + 3 ^ 40 * 893514 * 2
def baseEnd_893514 : Nat := 407824136463575427614053

theorem tailTrace_893514 : CollatzResearch.WordTrace tailWord_893514 prefixEnd_893514 407824136463575427614053 := by
  unfold tailWord_893514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8147283221239713221799899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21726088589972568591466397 8147283221239713221799899)
  ·
    refine ⟨12220924831859569832699849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8147283221239713221799899 12220924831859569832699849)
    ·
      refine ⟨9165693623894677374524887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12220924831859569832699849 9165693623894677374524887)
      ·
        refine ⟨13748540435842016061787331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9165693623894677374524887 13748540435842016061787331)
        ·
          refine ⟨20622810653763024092680997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13748540435842016061787331 20622810653763024092680997)
          ·
            refine ⟨3866776997580567017377687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20622810653763024092680997 3866776997580567017377687)
            ·
              refine ⟨5800165496370850526066531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3866776997580567017377687 5800165496370850526066531)
              ·
                refine ⟨8700248244556275789099797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5800165496370850526066531 8700248244556275789099797)
                ·
                  refine ⟨407824136463575427614053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8700248244556275789099797 407824136463575427614053)
                  ·
                    rfl

theorem cell20_893514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_893514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893514 prefixEnd_893514 := by exact prefixLift 893514
  have htrace : WordTrace (prefixWord ++ tailWord_893514) baseStart_893514 baseEnd_893514 := by
    simpa [prefixWord, tailWord_893514, baseEnd_893514] using wordTrace_append hprefix tailTrace_893514
  have hstable : (prefixWord ++ tailWord_893514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893514).length < 2 ^ (prefixWord ++ tailWord_893514).sum := by decide
  have hdescent : baseEnd_893514 < baseStart_893514 := by decide
  rcases family_descends (prefixWord ++ tailWord_893514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893541 : List Nat := [1, 3, 1, 3, 4, 2, 1, 2, 3]
def baseStart_893541 : Nat := 118140960795 + 893541 * 2 ^ 59
def prefixEnd_893541 : Nat := 4983230072969 + 3 ^ 40 * 893541 * 2
def baseEnd_893541 : Nat := 407836459999283333713943

theorem tailTrace_893541 : CollatzResearch.WordTrace tailWord_893541 prefixEnd_893541 407836459999283333713943 := by
  unfold tailWord_893541
  simp only [CollatzResearch.WordTrace]
  refine ⟨32590117655861036498432477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21726745103907357665621651 32590117655861036498432477)
  ·
    refine ⟨12221294120947888686912179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32590117655861036498432477 12221294120947888686912179)
    ·
      refine ⟨18331941181421833030368269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12221294120947888686912179 18331941181421833030368269)
      ·
        refine ⟨6874477943033187386388101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18331941181421833030368269 6874477943033187386388101)
        ·
          refine ⟨1288964614318722634947769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6874477943033187386388101 1288964614318722634947769)
          ·
            refine ⟨966723460739041976210827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1288964614318722634947769 966723460739041976210827)
            ·
              refine ⟨1450085191108562964316241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966723460739041976210827 1450085191108562964316241)
              ·
                refine ⟨1087563893331422223237181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1450085191108562964316241 1087563893331422223237181)
                ·
                  refine ⟨407836459999283333713943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1087563893331422223237181 407836459999283333713943)
                  ·
                    rfl

theorem cell20_893541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_893541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893541 prefixEnd_893541 := by exact prefixLift 893541
  have htrace : WordTrace (prefixWord ++ tailWord_893541) baseStart_893541 baseEnd_893541 := by
    simpa [prefixWord, tailWord_893541, baseEnd_893541] using wordTrace_append hprefix tailTrace_893541
  have hstable : (prefixWord ++ tailWord_893541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893541).length < 2 ^ (prefixWord ++ tailWord_893541).sum := by decide
  have hdescent : baseEnd_893541 < baseStart_893541 := by decide
  rcases family_descends (prefixWord ++ tailWord_893541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893558 : List Nat := [5, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_893558 : Nat := 118140960795 + 893558 * 2 ^ 59
def prefixEnd_893558 : Nat := 4983230072969 + 3 ^ 40 * 893558 * 2
def baseEnd_893558 : Nat := 407844219262506830147207

theorem tailTrace_893558 : CollatzResearch.WordTrace tailWord_893558 prefixEnd_893558 407844219262506830147207 := by
  unfold tailWord_893558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2036921106049965525112583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21727158464532965601200885 2036921106049965525112583)
  ·
    refine ⟨3055381659074948287668875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2036921106049965525112583 3055381659074948287668875)
    ·
      refine ⟨4583072488612422431503313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3055381659074948287668875 4583072488612422431503313)
      ·
        refine ⟨3437304366459316823627485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4583072488612422431503313 3437304366459316823627485)
        ·
          refine ⟨1288989137422243808860307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3437304366459316823627485 1288989137422243808860307)
          ·
            refine ⟨1933483706133365713290461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288989137422243808860307 1933483706133365713290461)
            ·
              refine ⟨725056389800012142483923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1933483706133365713290461 725056389800012142483923)
              ·
                refine ⟨1087584584700018213725885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725056389800012142483923 1087584584700018213725885)
                ·
                  refine ⟨407844219262506830147207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1087584584700018213725885 407844219262506830147207)
                  ·
                    rfl

theorem cell20_893558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_893558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893558 prefixEnd_893558 := by exact prefixLift 893558
  have htrace : WordTrace (prefixWord ++ tailWord_893558) baseStart_893558 baseEnd_893558 := by
    simpa [prefixWord, tailWord_893558, baseEnd_893558] using wordTrace_append hprefix tailTrace_893558
  have hstable : (prefixWord ++ tailWord_893558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893558).length < 2 ^ (prefixWord ++ tailWord_893558).sum := by decide
  have hdescent : baseEnd_893558 < baseStart_893558 := by decide
  rcases family_descends (prefixWord ++ tailWord_893558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893597 : List Nat := [1, 4, 2, 1, 1, 1, 10]
def baseStart_893597 : Nat := 118140960795 + 893597 * 2 ^ 59
def prefixEnd_893597 : Nat := 4983230072969 + 3 ^ 40 * 893597 * 2
def baseEnd_893597 : Nat := 45318002213910669760783

theorem tailTrace_893597 : CollatzResearch.WordTrace tailWord_893597 prefixEnd_893597 45318002213910669760783 := by
  unfold tailWord_893597
  simp only [CollatzResearch.WordTrace]
  refine ⟨32592160143658158062471045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21728106762438772041647363 32592160143658158062471045)
  ·
    refine ⟨6111030026935904636713321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32592160143658158062471045 6111030026935904636713321)
    ·
      refine ⟨4583272520201928477534991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6111030026935904636713321 4583272520201928477534991)
      ·
        refine ⟨6874908780302892716302487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4583272520201928477534991 6874908780302892716302487)
        ·
          refine ⟨10312363170454339074453731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6874908780302892716302487 10312363170454339074453731)
          ·
            refine ⟨15468544755681508611680597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10312363170454339074453731 15468544755681508611680597)
            ·
              refine ⟨45318002213910669760783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15468544755681508611680597 45318002213910669760783)
              ·
                rfl

theorem cell20_893597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 10].length) (baseStart_893597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893597 prefixEnd_893597 := by exact prefixLift 893597
  have htrace : WordTrace (prefixWord ++ tailWord_893597) baseStart_893597 baseEnd_893597 := by
    simpa [prefixWord, tailWord_893597, baseEnd_893597] using wordTrace_append hprefix tailTrace_893597
  have hstable : (prefixWord ++ tailWord_893597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893597).length < 2 ^ (prefixWord ++ tailWord_893597).sum := by decide
  have hdescent : baseEnd_893597 < baseStart_893597 := by decide
  rcases family_descends (prefixWord ++ tailWord_893597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893610 : List Nat := [3, 1, 5, 2, 1, 1, 2, 5]
def baseStart_893610 : Nat := 118140960795 + 893610 * 2 ^ 59
def prefixEnd_893610 : Nat := 4983230072969 + 3 ^ 40 * 893610 * 2
def baseEnd_893610 : Nat := 135955984493141920137887

theorem tailTrace_893610 : CollatzResearch.WordTrace tailWord_893610 prefixEnd_893610 135955984493141920137887 := by
  unfold tailWord_893610
  simp only [CollatzResearch.WordTrace]
  refine ⟨8148158573152765320673571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21728422861740707521796189 8148158573152765320673571)
  ·
    refine ⟨12222237859729147981010357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8148158573152765320673571 12222237859729147981010357)
    ·
      refine ⟨1145834799349607623219721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12222237859729147981010357 1145834799349607623219721)
      ·
        refine ⟨859376099512205717414791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1145834799349607623219721 859376099512205717414791)
        ·
          refine ⟨1289064149268308576122187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859376099512205717414791 1289064149268308576122187)
          ·
            refine ⟨1933596223902462864183281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1289064149268308576122187 1933596223902462864183281)
            ·
              refine ⟨1450197167926847148137461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1933596223902462864183281 1450197167926847148137461)
              ·
                refine ⟨135955984493141920137887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1450197167926847148137461 135955984493141920137887)
                ·
                  rfl

theorem cell20_893610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_893610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893610 prefixEnd_893610 := by exact prefixLift 893610
  have htrace : WordTrace (prefixWord ++ tailWord_893610) baseStart_893610 baseEnd_893610 := by
    simpa [prefixWord, tailWord_893610, baseEnd_893610] using wordTrace_append hprefix tailTrace_893610
  have hstable : (prefixWord ++ tailWord_893610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893610).length < 2 ^ (prefixWord ++ tailWord_893610).sum := by decide
  have hdescent : baseEnd_893610 < baseStart_893610 := by decide
  rcases family_descends (prefixWord ++ tailWord_893610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893617 : List Nat := [1, 2, 2, 6, 1, 1, 1, 3, 3]
def baseStart_893617 : Nat := 118140960795 + 893617 * 2 ^ 59
def prefixEnd_893617 : Nat := 4983230072969 + 3 ^ 40 * 893617 * 2
def baseEnd_893617 : Nat := 407871148470164847180299

theorem tailTrace_893617 : CollatzResearch.WordTrace tailWord_893617 prefixEnd_893617 407871148470164847180299 := by
  unfold tailWord_893617
  simp only [CollatzResearch.WordTrace]
  refine ⟨32592889603585701478199105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21728593069057134318799403 32592889603585701478199105)
  ·
    refine ⟨24444667202689276108649329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32592889603585701478199105 24444667202689276108649329)
    ·
      refine ⟨18333500402016957081486997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24444667202689276108649329 18333500402016957081486997)
      ·
        refine ⟨859382831344544863194703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18333500402016957081486997 859382831344544863194703)
        ·
          refine ⟨1289074247016817294792055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859382831344544863194703 1289074247016817294792055)
          ·
            refine ⟨1933611370525225942188083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1289074247016817294792055 1933611370525225942188083)
            ·
              refine ⟨2900417055787838913282125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1933611370525225942188083 2900417055787838913282125)
              ·
                refine ⟨1087656395920439592480797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2900417055787838913282125 1087656395920439592480797)
                ·
                  refine ⟨407871148470164847180299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1087656395920439592480797 407871148470164847180299)
                  ·
                    rfl

theorem cell20_893617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_893617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893617 prefixEnd_893617 := by exact prefixLift 893617
  have htrace : WordTrace (prefixWord ++ tailWord_893617) baseStart_893617 baseEnd_893617 := by
    simpa [prefixWord, tailWord_893617, baseEnd_893617] using wordTrace_append hprefix tailTrace_893617
  have hstable : (prefixWord ++ tailWord_893617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893617).length < 2 ^ (prefixWord ++ tailWord_893617).sum := by decide
  have hdescent : baseEnd_893617 < baseStart_893617 := by decide
  rcases family_descends (prefixWord ++ tailWord_893617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893628 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 6]
def baseStart_893628 : Nat := 118140960795 + 893628 * 2 ^ 59
def prefixEnd_893628 : Nat := 4983230072969 + 3 ^ 40 * 893628 * 2
def baseEnd_893628 : Nat := 407876169169897697813587

theorem tailTrace_893628 : CollatzResearch.WordTrace tailWord_893628 prefixEnd_893628 407876169169897697813587 := by
  unfold tailWord_893628
  simp only [CollatzResearch.WordTrace]
  refine ⟨16296645403272925178424769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21728860537697233571233025 16296645403272925178424769)
  ·
    refine ⟨12222484052454693883818577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16296645403272925178424769 12222484052454693883818577)
    ·
      refine ⟨9166863039341020412863933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12222484052454693883818577 9166863039341020412863933)
      ·
        refine ⟨3437573639752882654823975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9166863039341020412863933 3437573639752882654823975)
        ·
          refine ⟨5156360459629323982235963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3437573639752882654823975 5156360459629323982235963)
          ·
            refine ⟨7734540689443985973353945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5156360459629323982235963 7734540689443985973353945)
            ·
              refine ⟨5800905517082989480015459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7734540689443985973353945 5800905517082989480015459)
              ·
                refine ⟨8701358275624484220023189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5800905517082989480015459 8701358275624484220023189)
                ·
                  refine ⟨407876169169897697813587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8701358275624484220023189 407876169169897697813587)
                  ·
                    rfl

theorem cell20_893628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_893628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893628 prefixEnd_893628 := by exact prefixLift 893628
  have htrace : WordTrace (prefixWord ++ tailWord_893628) baseStart_893628 baseEnd_893628 := by
    simpa [prefixWord, tailWord_893628, baseEnd_893628] using wordTrace_append hprefix tailTrace_893628
  have hstable : (prefixWord ++ tailWord_893628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893628).length < 2 ^ (prefixWord ++ tailWord_893628).sum := by decide
  have hdescent : baseEnd_893628 < baseStart_893628 := by decide
  rcases family_descends (prefixWord ++ tailWord_893628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893652 : List Nat := [2, 4, 1, 3, 2, 8]
def baseStart_893652 : Nat := 118140960795 + 893652 * 2 ^ 59
def prefixEnd_893652 : Nat := 4983230072969 + 3 ^ 40 * 893652 * 2
def baseEnd_893652 : Nat := 15106930497180010407907

theorem tailTrace_893652 : CollatzResearch.WordTrace tailWord_893652 prefixEnd_893652 15106930497180010407907 := by
  unfold tailWord_893652
  simp only [CollatzResearch.WordTrace]
  refine ⟨16297083079229451227861605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21729444105639268303815473 16297083079229451227861605)
  ·
    refine ⟨3055703077355522105224051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16297083079229451227861605 3055703077355522105224051)
    ·
      refine ⟨4583554616033283157836077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3055703077355522105224051 4583554616033283157836077)
      ·
        refine ⟨1718832981012481184188529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4583554616033283157836077 1718832981012481184188529)
        ·
          refine ⟨1289124735759360888141397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1718832981012481184188529 1289124735759360888141397)
          ·
            refine ⟨15106930497180010407907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1289124735759360888141397 15106930497180010407907)
            ·
              rfl

theorem cell20_893652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 8].length) (baseStart_893652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893652 prefixEnd_893652 := by exact prefixLift 893652
  have htrace : WordTrace (prefixWord ++ tailWord_893652) baseStart_893652 baseEnd_893652 := by
    simpa [prefixWord, tailWord_893652, baseEnd_893652] using wordTrace_append hprefix tailTrace_893652
  have hstable : (prefixWord ++ tailWord_893652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893652).length < 2 ^ (prefixWord ++ tailWord_893652).sum := by decide
  have hdescent : baseEnd_893652 < baseStart_893652 := by decide
  rcases family_descends (prefixWord ++ tailWord_893652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893673 : List Nat := [1, 2, 1, 1, 1, 2, 7, 5]
def baseStart_893673 : Nat := 118140960795 + 893673 * 2 ^ 59
def prefixEnd_893673 : Nat := 4983230072969 + 3 ^ 40 * 893673 * 2
def baseEnd_893673 : Nat := 135965569465359180437801

theorem tailTrace_893673 : CollatzResearch.WordTrace tailWord_893673 prefixEnd_893673 135965569465359180437801 := by
  unfold tailWord_893673
  simp only [CollatzResearch.WordTrace]
  refine ⟨32594932091382823042237673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21729954727588548694825115 32594932091382823042237673)
  ·
    refine ⟨24446199068537117281678255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32594932091382823042237673 24446199068537117281678255)
    ·
      refine ⟨36669298602805675922517383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24446199068537117281678255 36669298602805675922517383)
      ·
        refine ⟨55003947904208513883776075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36669298602805675922517383 55003947904208513883776075)
        ·
          refine ⟨82505921856312770825664113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55003947904208513883776075 82505921856312770825664113)
          ·
            refine ⟨61879441392234578119248085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82505921856312770825664113 61879441392234578119248085)
            ·
              refine ⟨1450299407630497924669877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 61879441392234578119248085 1450299407630497924669877)
              ·
                refine ⟨135965569465359180437801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1450299407630497924669877 135965569465359180437801)
                ·
                  rfl

theorem cell20_893673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 5].length) (baseStart_893673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893673 prefixEnd_893673 := by exact prefixLift 893673
  have htrace : WordTrace (prefixWord ++ tailWord_893673) baseStart_893673 baseEnd_893673 := by
    simpa [prefixWord, tailWord_893673, baseEnd_893673] using wordTrace_append hprefix tailTrace_893673
  have hstable : (prefixWord ++ tailWord_893673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893673).length < 2 ^ (prefixWord ++ tailWord_893673).sum := by decide
  have hdescent : baseEnd_893673 < baseStart_893673 := by decide
  rcases family_descends (prefixWord ++ tailWord_893673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893700 : List Nat := [2, 3, 2, 2, 1, 1, 4, 3, 2]
def baseStart_893700 : Nat := 118140960795 + 893700 * 2 ^ 59
def prefixEnd_893700 : Nat := 4983230072969 + 3 ^ 40 * 893700 * 2
def baseEnd_893700 : Nat := 407909031931785447413293

theorem tailTrace_893700 : CollatzResearch.WordTrace tailWord_893700 prefixEnd_893700 407909031931785447413293 := by
  unfold tailWord_893700
  simp only [CollatzResearch.WordTrace]
  refine ⟨16297958431142503326735277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21730611241523337768980369 16297958431142503326735277)
  ·
    refine ⟨6111734411678438747525729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16297958431142503326735277 6111734411678438747525729)
    ·
      refine ⟨4583800808758829060644297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6111734411678438747525729 4583800808758829060644297)
      ·
        refine ⟨3437850606569121795483223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4583800808758829060644297 3437850606569121795483223)
        ·
          refine ⟨5156775909853682693224835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3437850606569121795483223 5156775909853682693224835)
          ·
            refine ⟨7735163864780524039837253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5156775909853682693224835 7735163864780524039837253)
            ·
              refine ⟨1450343224646348257469485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7735163864780524039837253 1450343224646348257469485)
              ·
                refine ⟨543878709242380596551057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1450343224646348257469485 543878709242380596551057)
                ·
                  refine ⟨407909031931785447413293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543878709242380596551057 407909031931785447413293)
                  ·
                    rfl

theorem cell20_893700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_893700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893700 prefixEnd_893700 := by exact prefixLift 893700
  have htrace : WordTrace (prefixWord ++ tailWord_893700) baseStart_893700 baseEnd_893700 := by
    simpa [prefixWord, tailWord_893700, baseEnd_893700] using wordTrace_append hprefix tailTrace_893700
  have hstable : (prefixWord ++ tailWord_893700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893700).length < 2 ^ (prefixWord ++ tailWord_893700).sum := by decide
  have hdescent : baseEnd_893700 < baseStart_893700 := by decide
  rcases family_descends (prefixWord ++ tailWord_893700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893741 : List Nat := [1, 5, 3, 2, 1, 2, 2, 4]
def baseStart_893741 : Nat := 118140960795 + 893741 * 2 ^ 59
def prefixEnd_893741 : Nat := 4983230072969 + 3 ^ 40 * 893741 * 2
def baseEnd_893741 : Nat := 135975915149657175682153

theorem tailTrace_893741 : CollatzResearch.WordTrace tailWord_893741 prefixEnd_893741 135975915149657175682153 := by
  unfold tailWord_893741
  simp only [CollatzResearch.WordTrace]
  refine ⟨32597412255136470655713077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21731608170090980437142051 32597412255136470655713077)
  ·
    refine ⟨3056007398919044123973101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32597412255136470655713077 3056007398919044123973101)
    ·
      refine ⟨1146002774594641546489913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3056007398919044123973101 1146002774594641546489913)
      ·
        refine ⟨859502080945981159867435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1146002774594641546489913 859502080945981159867435)
        ·
          refine ⟨1289253121418971739801153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859502080945981159867435 1289253121418971739801153)
          ·
            refine ⟨966939841064228804850865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1289253121418971739801153 966939841064228804850865)
            ·
              refine ⟨725204880798171603638149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 966939841064228804850865 725204880798171603638149)
              ·
                refine ⟨135975915149657175682153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 725204880798171603638149 135975915149657175682153)
                ·
                  rfl

theorem cell20_893741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 4].length) (baseStart_893741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893741 prefixEnd_893741 := by exact prefixLift 893741
  have htrace : WordTrace (prefixWord ++ tailWord_893741) baseStart_893741 baseEnd_893741 := by
    simpa [prefixWord, tailWord_893741, baseEnd_893741] using wordTrace_append hprefix tailTrace_893741
  have hstable : (prefixWord ++ tailWord_893741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893741).length < 2 ^ (prefixWord ++ tailWord_893741).sum := by decide
  have hdescent : baseEnd_893741 < baseStart_893741 := by decide
  rcases family_descends (prefixWord ++ tailWord_893741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893831 : List Nat := [1, 1, 4, 2, 3, 3, 2, 2, 2]
def baseStart_893831 : Nat := 118140960795 + 893831 * 2 ^ 59
def prefixEnd_893831 : Nat := 4983230072969 + 3 ^ 40 * 893831 * 2
def baseEnd_893831 : Nat := 407968823901331214046091

theorem tailTrace_893831 : CollatzResearch.WordTrace tailWord_893831 prefixEnd_893831 407968823901331214046091 := by
  unfold tailWord_893831
  simp only [CollatzResearch.WordTrace]
  refine ⟨32600694824810416026489347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21733796549873610684326231 32600694824810416026489347)
  ·
    refine ⟨48901042237215624039734021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32600694824810416026489347 48901042237215624039734021)
    ·
      refine ⟨9168945419477929507450129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48901042237215624039734021 9168945419477929507450129)
      ·
        refine ⟨6876709064608447130587597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9168945419477929507450129 6876709064608447130587597)
        ·
          refine ⟨2578765899228167673970349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6876709064608447130587597 2578765899228167673970349)
          ·
            refine ⟨967037212210562877738881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2578765899228167673970349 967037212210562877738881)
            ·
              refine ⟨725277909157922158304161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967037212210562877738881 725277909157922158304161)
              ·
                refine ⟨543958431868441618728121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725277909157922158304161 543958431868441618728121)
                ·
                  refine ⟨407968823901331214046091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543958431868441618728121 407968823901331214046091)
                  ·
                    rfl

theorem cell20_893831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 2].length) (baseStart_893831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893831 prefixEnd_893831 := by exact prefixLift 893831
  have htrace : WordTrace (prefixWord ++ tailWord_893831) baseStart_893831 baseEnd_893831 := by
    simpa [prefixWord, tailWord_893831, baseEnd_893831] using wordTrace_append hprefix tailTrace_893831
  have hstable : (prefixWord ++ tailWord_893831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893831).length < 2 ^ (prefixWord ++ tailWord_893831).sum := by decide
  have hdescent : baseEnd_893831 < baseStart_893831 := by decide
  rcases family_descends (prefixWord ++ tailWord_893831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893963 : List Nat := [1, 1, 1, 1, 6, 3, 1, 3, 3]
def baseStart_893963 : Nat := 118140960795 + 893963 * 2 ^ 59
def prefixEnd_893963 : Nat := 4983230072969 + 3 ^ 40 * 893963 * 2
def baseEnd_893963 : Nat := 408029072298125421645551

theorem tailTrace_893963 : CollatzResearch.WordTrace tailWord_893963 prefixEnd_893963 408029072298125421645551 := by
  unfold tailWord_893963
  simp only [CollatzResearch.WordTrace]
  refine ⟨32605509260332202570294543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21737006173554801713529695 32605509260332202570294543)
  ·
    refine ⟨48908263890498303855441815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32605509260332202570294543 48908263890498303855441815)
    ·
      refine ⟨73362395835747455783162723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48908263890498303855441815 73362395835747455783162723)
      ·
        refine ⟨110043593753621183674744085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73362395835747455783162723 110043593753621183674744085)
        ·
          refine ⟨5158293457200992984753629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 110043593753621183674744085 5158293457200992984753629)
          ·
            refine ⟨1934360046450372369282611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5158293457200992984753629 1934360046450372369282611)
            ·
              refine ⟨2901540069675558553923917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1934360046450372369282611 2901540069675558553923917)
              ·
                refine ⟨1088077526128334457721469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2901540069675558553923917 1088077526128334457721469)
                ·
                  refine ⟨408029072298125421645551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088077526128334457721469 408029072298125421645551)
                  ·
                    rfl

theorem cell20_893963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 3].length) (baseStart_893963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893963 prefixEnd_893963 := by exact prefixLift 893963
  have htrace : WordTrace (prefixWord ++ tailWord_893963) baseStart_893963 baseEnd_893963 := by
    simpa [prefixWord, tailWord_893963, baseEnd_893963] using wordTrace_append hprefix tailTrace_893963
  have hstable : (prefixWord ++ tailWord_893963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893963).length < 2 ^ (prefixWord ++ tailWord_893963).sum := by decide
  have hdescent : baseEnd_893963 < baseStart_893963 := by decide
  rcases family_descends (prefixWord ++ tailWord_893963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893994 : List Nat := [3, 1, 4, 1, 4, 7]
def baseStart_893994 : Nat := 118140960795 + 893994 * 2 ^ 59
def prefixEnd_893994 : Nat := 4983230072969 + 3 ^ 40 * 893994 * 2
def baseEnd_893994 : Nat := 15112711908993595985633

theorem tailTrace_893994 : CollatzResearch.WordTrace tailWord_893994 prefixEnd_893994 15112711908993595985633 := by
  unfold tailWord_893994
  simp only [CollatzResearch.WordTrace]
  refine ⟨8151659980804973716168259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21737759948813263243115357 8151659980804973716168259)
  ·
    refine ⟨12227489971207460574252389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8151659980804973716168259 12227489971207460574252389)
    ·
      refine ⟨2292654369601398857672323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12227489971207460574252389 2292654369601398857672323)
      ·
        refine ⟨3438981554402098286508485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2292654369601398857672323 3438981554402098286508485)
        ·
          refine ⟨644809041450393428720341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3438981554402098286508485 644809041450393428720341)
          ·
            refine ⟨15112711908993595985633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 644809041450393428720341 15112711908993595985633)
            ·
              rfl

theorem cell20_893994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 7].length) (baseStart_893994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_893994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_893994 prefixEnd_893994 := by exact prefixLift 893994
  have htrace : WordTrace (prefixWord ++ tailWord_893994) baseStart_893994 baseEnd_893994 := by
    simpa [prefixWord, tailWord_893994, baseEnd_893994] using wordTrace_append hprefix tailTrace_893994
  have hstable : (prefixWord ++ tailWord_893994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893994).length < 2 ^ (prefixWord ++ tailWord_893994).sum := by decide
  have hdescent : baseEnd_893994 < baseStart_893994 := by decide
  rcases family_descends (prefixWord ++ tailWord_893994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894001 : List Nat := [1, 2, 2, 3, 1, 2, 4, 2, 3]
def baseStart_894001 : Nat := 118140960795 + 894001 * 2 ^ 59
def prefixEnd_894001 : Nat := 4983230072969 + 3 ^ 40 * 894001 * 2
def baseEnd_894001 : Nat := 408046416533566178378729

theorem tailTrace_894001 : CollatzResearch.WordTrace tailWord_894001 prefixEnd_894001 408046416533566178378729 := by
  unfold tailWord_894001
  simp only [CollatzResearch.WordTrace]
  refine ⟨32606895234194535060177857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21737930156129690040118571 32606895234194535060177857)
  ·
    refine ⟨24455171425645901295133393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32606895234194535060177857 24455171425645901295133393)
    ·
      refine ⟨18341378569234425971350045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24455171425645901295133393 18341378569234425971350045)
      ·
        refine ⟨6878016963462909739256267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18341378569234425971350045 6878016963462909739256267)
        ·
          refine ⟨10317025445194364608884401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6878016963462909739256267 10317025445194364608884401)
          ·
            refine ⟨7737769083895773456663301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10317025445194364608884401 7737769083895773456663301)
            ·
              refine ⟨1450831703230457523124369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7737769083895773456663301 1450831703230457523124369)
              ·
                refine ⟨1088123777422843142343277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1450831703230457523124369 1088123777422843142343277)
                ·
                  refine ⟨408046416533566178378729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088123777422843142343277 408046416533566178378729)
                  ·
                    rfl

theorem cell20_894001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_894001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894001 prefixEnd_894001 := by exact prefixLift 894001
  have htrace : WordTrace (prefixWord ++ tailWord_894001) baseStart_894001 baseEnd_894001 := by
    simpa [prefixWord, tailWord_894001, baseEnd_894001] using wordTrace_append hprefix tailTrace_894001
  have hstable : (prefixWord ++ tailWord_894001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894001).length < 2 ^ (prefixWord ++ tailWord_894001).sum := by decide
  have hdescent : baseEnd_894001 < baseStart_894001 := by decide
  rcases family_descends (prefixWord ++ tailWord_894001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894038 : List Nat := [5, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_894038 : Nat := 118140960795 + 894038 * 2 ^ 59
def prefixEnd_894038 : Nat := 4983230072969 + 3 ^ 40 * 894038 * 2
def baseEnd_894038 : Nat := 408063304341758494145245

theorem tailTrace_894038 : CollatzResearch.WordTrace tailWord_894038 prefixEnd_894038 408063304341758494145245 := by
  unfold tailWord_894038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2038015295941280648704673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21738829823373660252849845 2038015295941280648704673)
  ·
    refine ⟨1528511471955960486528505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2038015295941280648704673 1528511471955960486528505)
    ·
      refine ⟨1146383603966970364896379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1528511471955960486528505 1146383603966970364896379)
      ·
        refine ⟨1719575405950455547344569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1146383603966970364896379 1719575405950455547344569)
        ·
          refine ⟨1289681554462841660508427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1719575405950455547344569 1289681554462841660508427)
          ·
            refine ⟨1934522331694262490762641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1289681554462841660508427 1934522331694262490762641)
            ·
              refine ⟨1450891748770696868071981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1934522331694262490762641 1450891748770696868071981)
              ·
                refine ⟨544084405789011325526993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1450891748770696868071981 544084405789011325526993)
                ·
                  refine ⟨408063304341758494145245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544084405789011325526993 408063304341758494145245)
                  ·
                    rfl

theorem cell20_894038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_894038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894038 prefixEnd_894038 := by exact prefixLift 894038
  have htrace : WordTrace (prefixWord ++ tailWord_894038) baseStart_894038 baseEnd_894038 := by
    simpa [prefixWord, tailWord_894038, baseEnd_894038] using wordTrace_append hprefix tailTrace_894038
  have hstable : (prefixWord ++ tailWord_894038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894038).length < 2 ^ (prefixWord ++ tailWord_894038).sum := by decide
  have hdescent : baseEnd_894038 < baseStart_894038 := by decide
  rcases family_descends (prefixWord ++ tailWord_894038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894056 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 5]
def baseStart_894056 : Nat := 118140960795 + 894056 * 2 ^ 59
def prefixEnd_894056 : Nat := 4983230072969 + 3 ^ 40 * 894056 * 2
def baseEnd_894056 : Nat := 408071520032230431545171

theorem tailTrace_894056 : CollatzResearch.WordTrace tailWord_894056 prefixEnd_894056 408071520032230431545171 := by
  unfold tailWord_894056
  simp only [CollatzResearch.WordTrace]
  refine ⟨16304450624497639726715011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21739267499330186302286681 16304450624497639726715011)
  ·
    refine ⟨24456675936746459590072517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16304450624497639726715011 24456675936746459590072517)
    ·
      refine ⟨4585626738139961173138597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24456675936746459590072517 4585626738139961173138597)
      ·
        refine ⟨859805013401242719963487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4585626738139961173138597 859805013401242719963487)
        ·
          refine ⟨1289707520101864079945231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859805013401242719963487 1289707520101864079945231)
          ·
            refine ⟨1934561280152796119917847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1289707520101864079945231 1934561280152796119917847)
            ·
              refine ⟨2901841920229194179876771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1934561280152796119917847 2901841920229194179876771)
              ·
                refine ⟨4352762880343791269815157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2901841920229194179876771 4352762880343791269815157)
                ·
                  refine ⟨408071520032230431545171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4352762880343791269815157 408071520032230431545171)
                  ·
                    rfl

theorem cell20_894056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_894056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894056 prefixEnd_894056 := by exact prefixLift 894056
  have htrace : WordTrace (prefixWord ++ tailWord_894056) baseStart_894056 baseEnd_894056 := by
    simpa [prefixWord, tailWord_894056, baseEnd_894056] using wordTrace_append hprefix tailTrace_894056
  have hstable : (prefixWord ++ tailWord_894056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894056).length < 2 ^ (prefixWord ++ tailWord_894056).sum := by decide
  have hdescent : baseEnd_894056 < baseStart_894056 := by decide
  rcases family_descends (prefixWord ++ tailWord_894056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894060 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 5]
def baseStart_894060 : Nat := 118140960795 + 894060 * 2 ^ 59
def prefixEnd_894060 : Nat := 4983230072969 + 3 ^ 40 * 894060 * 2
def baseEnd_894060 : Nat := 408073345741224195411821

theorem tailTrace_894060 : CollatzResearch.WordTrace tailWord_894060 prefixEnd_894060 408073345741224195411821 := by
  unfold tailWord_894060
  simp only [CollatzResearch.WordTrace]
  refine ⟨16304523570490394068287817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21739364760653858757717089 16304523570490394068287817)
  ·
    refine ⟨12228392677867795551215863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16304523570490394068287817 12228392677867795551215863)
    ·
      refine ⟨18342589016801693326823795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12228392677867795551215863 18342589016801693326823795)
      ·
        refine ⟨27513883525202539990235693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18342589016801693326823795 27513883525202539990235693)
        ·
          refine ⟨10317706321950952496338385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27513883525202539990235693 10317706321950952496338385)
          ·
            refine ⟨7738279741463214372253789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10317706321950952496338385 7738279741463214372253789)
            ·
              refine ⟨2901854903048705389595171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7738279741463214372253789 2901854903048705389595171)
              ·
                refine ⟨4352782354573058084392757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2901854903048705389595171 4352782354573058084392757)
                ·
                  refine ⟨408073345741224195411821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4352782354573058084392757 408073345741224195411821)
                  ·
                    rfl

theorem cell20_894060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_894060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894060 prefixEnd_894060 := by exact prefixLift 894060
  have htrace : WordTrace (prefixWord ++ tailWord_894060) baseStart_894060 baseEnd_894060 := by
    simpa [prefixWord, tailWord_894060, baseEnd_894060] using wordTrace_append hprefix tailTrace_894060
  have hstable : (prefixWord ++ tailWord_894060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894060).length < 2 ^ (prefixWord ++ tailWord_894060).sum := by decide
  have hdescent : baseEnd_894060 < baseStart_894060 := by decide
  rcases family_descends (prefixWord ++ tailWord_894060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894084 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 4]
def baseStart_894084 : Nat := 118140960795 + 894084 * 2 ^ 59
def prefixEnd_894084 : Nat := 4983230072969 + 3 ^ 40 * 894084 * 2
def baseEnd_894084 : Nat := 408084299995186778611723

theorem tailTrace_894084 : CollatzResearch.WordTrace tailWord_894084 prefixEnd_894084 408084299995186778611723 := by
  unfold tailWord_894084
  simp only [CollatzResearch.WordTrace]
  refine ⟨16304961246446920117724653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21739948328595893490299537 16304961246446920117724653)
  ·
    refine ⟨6114360467417595044146745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16304961246446920117724653 6114360467417595044146745)
    ·
      refine ⟨4585770350563196283110059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6114360467417595044146745 4585770350563196283110059)
      ·
        refine ⟨6878655525844794424665089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4585770350563196283110059 6878655525844794424665089)
        ·
          refine ⟨5158991644383595818498817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6878655525844794424665089 5158991644383595818498817)
          ·
            refine ⟨3869243733287696863874113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5158991644383595818498817 3869243733287696863874113)
            ·
              refine ⟨2901932799965772647905585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3869243733287696863874113 2901932799965772647905585)
              ·
                refine ⟨2176449599974329485929189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2901932799965772647905585 2176449599974329485929189)
                ·
                  refine ⟨408084299995186778611723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2176449599974329485929189 408084299995186778611723)
                  ·
                    rfl

theorem cell20_894084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_894084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894084 prefixEnd_894084 := by exact prefixLift 894084
  have htrace : WordTrace (prefixWord ++ tailWord_894084) baseStart_894084 baseEnd_894084 := by
    simpa [prefixWord, tailWord_894084, baseEnd_894084] using wordTrace_append hprefix tailTrace_894084
  have hstable : (prefixWord ++ tailWord_894084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894084).length < 2 ^ (prefixWord ++ tailWord_894084).sum := by decide
  have hdescent : baseEnd_894084 < baseStart_894084 := by decide
  rcases family_descends (prefixWord ++ tailWord_894084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894129 : List Nat := [1, 2, 2, 5, 1, 1, 1, 7]
def baseStart_894129 : Nat := 118140960795 + 894129 * 2 ^ 59
def prefixEnd_894129 : Nat := 4983230072969 + 3 ^ 40 * 894129 * 2
def baseEnd_894129 : Nat := 136034946407122207370513

theorem tailTrace_894129 : CollatzResearch.WordTrace tailWord_894129 prefixEnd_894129 136034946407122207370513 := by
  unfold tailWord_894129
  simp only [CollatzResearch.WordTrace]
  refine ⟨32611563777730812920837441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21741042518487208613891627 32611563777730812920837441)
  ·
    refine ⟨24458672833298109690628081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32611563777730812920837441 24458672833298109690628081)
    ·
      refine ⟨18344004624973582267971061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24458672833298109690628081 18344004624973582267971061)
      ·
        refine ⟨1719750433591273337622287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18344004624973582267971061 1719750433591273337622287)
        ·
          refine ⟨2579625650386910006433431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1719750433591273337622287 2579625650386910006433431)
          ·
            refine ⟨3869438475580365009650147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2579625650386910006433431 3869438475580365009650147)
            ·
              refine ⟨5804157713370547514475221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3869438475580365009650147 5804157713370547514475221)
              ·
                refine ⟨136034946407122207370513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5804157713370547514475221 136034946407122207370513)
                ·
                  rfl

theorem cell20_894129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 7].length) (baseStart_894129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894129 prefixEnd_894129 := by exact prefixLift 894129
  have htrace : WordTrace (prefixWord ++ tailWord_894129) baseStart_894129 baseEnd_894129 := by
    simpa [prefixWord, tailWord_894129, baseEnd_894129] using wordTrace_append hprefix tailTrace_894129
  have hstable : (prefixWord ++ tailWord_894129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894129).length < 2 ^ (prefixWord ++ tailWord_894129).sum := by decide
  have hdescent : baseEnd_894129 < baseStart_894129 := by decide
  rcases family_descends (prefixWord ++ tailWord_894129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894143 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 4]
def baseStart_894143 : Nat := 118140960795 + 894143 * 2 ^ 59
def prefixEnd_894143 : Nat := 4983230072969 + 3 ^ 40 * 894143 * 2
def baseEnd_894143 : Nat := 408111229202844795644815

theorem tailTrace_894143 : CollatzResearch.WordTrace tailWord_894143 prefixEnd_894143 408111229202844795644815 := by
  unfold tailWord_894143
  simp only [CollatzResearch.WordTrace]
  refine ⟨32612074399680093311847083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21741382933120062207898055 32612074399680093311847083)
  ·
    refine ⟨48918111599520139967770625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32612074399680093311847083 48918111599520139967770625)
    ·
      refine ⟨36688583699640104975827969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48918111599520139967770625 36688583699640104975827969)
      ·
        refine ⟨27516437774730078731870977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36688583699640104975827969 27516437774730078731870977)
        ·
          refine ⟨20637328331047559048903233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27516437774730078731870977 20637328331047559048903233)
          ·
            refine ⟨15477996248285669286677425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20637328331047559048903233 15477996248285669286677425)
            ·
              refine ⟨11608497186214251965008069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15477996248285669286677425 11608497186214251965008069)
              ·
                refine ⟨2176593222415172243439013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11608497186214251965008069 2176593222415172243439013)
                ·
                  refine ⟨408111229202844795644815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2176593222415172243439013 408111229202844795644815)
                  ·
                    rfl

theorem cell20_894143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_894143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894143 prefixEnd_894143 := by exact prefixLift 894143
  have htrace : WordTrace (prefixWord ++ tailWord_894143) baseStart_894143 baseEnd_894143 := by
    simpa [prefixWord, tailWord_894143, baseEnd_894143] using wordTrace_append hprefix tailTrace_894143
  have hstable : (prefixWord ++ tailWord_894143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894143).length < 2 ^ (prefixWord ++ tailWord_894143).sum := by decide
  have hdescent : baseEnd_894143 < baseStart_894143 := by decide
  rcases family_descends (prefixWord ++ tailWord_894143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894177 : List Nat := [1, 2, 3, 1, 3, 3, 1, 4, 2]
def baseStart_894177 : Nat := 118140960795 + 894177 * 2 ^ 59
def prefixEnd_894177 : Nat := 4983230072969 + 3 ^ 40 * 894177 * 2
def baseEnd_894177 : Nat := 408126747729291788511343

theorem tailTrace_894177 : CollatzResearch.WordTrace tailWord_894177 prefixEnd_894177 408126747729291788511343 := by
  unfold tailWord_894177
  simp only [CollatzResearch.WordTrace]
  refine ⟨32613314481556917118584785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21742209654371278079056523 32613314481556917118584785)
  ·
    refine ⟨24459985861167687838938589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32613314481556917118584785 24459985861167687838938589)
    ·
      refine ⟨9172494697937882939601971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24459985861167687838938589 9172494697937882939601971)
      ·
        refine ⟨13758742046906824409402957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9172494697937882939601971 13758742046906824409402957)
        ·
          refine ⟨5159528267590059153526109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13758742046906824409402957 5159528267590059153526109)
          ·
            refine ⟨1934823100346272182572291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5159528267590059153526109 1934823100346272182572291)
            ·
              refine ⟨2902234650519408273858437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1934823100346272182572291 2902234650519408273858437)
              ·
                refine ⟨544168996972389051348457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2902234650519408273858437 544168996972389051348457)
                ·
                  refine ⟨408126747729291788511343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544168996972389051348457 408126747729291788511343)
                  ·
                    rfl

theorem cell20_894177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 2].length) (baseStart_894177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894177 prefixEnd_894177 := by exact prefixLift 894177
  have htrace : WordTrace (prefixWord ++ tailWord_894177) baseStart_894177 baseEnd_894177 := by
    simpa [prefixWord, tailWord_894177, baseEnd_894177] using wordTrace_append hprefix tailTrace_894177
  have hstable : (prefixWord ++ tailWord_894177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894177).length < 2 ^ (prefixWord ++ tailWord_894177).sum := by decide
  have hdescent : baseEnd_894177 < baseStart_894177 := by decide
  rcases family_descends (prefixWord ++ tailWord_894177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894253 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 4]
def baseStart_894253 : Nat := 118140960795 + 894253 * 2 ^ 59
def prefixEnd_894253 : Nat := 4983230072969 + 3 ^ 40 * 894253 * 2
def baseEnd_894253 : Nat := 408161436200173301977699

theorem tailTrace_894253 : CollatzResearch.WordTrace tailWord_894253 prefixEnd_894253 408161436200173301977699 := by
  unfold tailWord_894253
  simp only [CollatzResearch.WordTrace]
  refine ⟨32616086429281582098351413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21744057619521054732234275 32616086429281582098351413)
  ·
    refine ⟨3057758102745148321720445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32616086429281582098351413 3057758102745148321720445)
    ·
      refine ⟨1146659288529430620645167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3057758102745148321720445 1146659288529430620645167)
      ·
        refine ⟨1719988932794145930967751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1146659288529430620645167 1719988932794145930967751)
        ·
          refine ⟨2579983399191218896451627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1719988932794145930967751 2579983399191218896451627)
          ·
            refine ⟨3869975098786828344677441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2579983399191218896451627 3869975098786828344677441)
            ·
              refine ⟨2902481324090121258508081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3869975098786828344677441 2902481324090121258508081)
              ·
                refine ⟨2176860993067590943881061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2902481324090121258508081 2176860993067590943881061)
                ·
                  refine ⟨408161436200173301977699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2176860993067590943881061 408161436200173301977699)
                  ·
                    rfl

theorem cell20_894253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_894253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894253 prefixEnd_894253 := by exact prefixLift 894253
  have htrace : WordTrace (prefixWord ++ tailWord_894253) baseStart_894253 baseEnd_894253 := by
    simpa [prefixWord, tailWord_894253, baseEnd_894253] using wordTrace_append hprefix tailTrace_894253
  have hstable : (prefixWord ++ tailWord_894253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894253).length < 2 ^ (prefixWord ++ tailWord_894253).sum := by decide
  have hdescent : baseEnd_894253 < baseStart_894253 := by decide
  rcases family_descends (prefixWord ++ tailWord_894253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894288 : List Nat := [2, 1, 1, 1, 1, 5, 2, 4, 3]
def baseStart_894288 : Nat := 118140960795 + 894288 * 2 ^ 59
def prefixEnd_894288 : Nat := 4983230072969 + 3 ^ 40 * 894288 * 2
def baseEnd_894288 : Nat := 408177411153868735810889

theorem tailTrace_894288 : CollatzResearch.WordTrace tailWord_894288 prefixEnd_894288 408177411153868735810889 := by
  unfold tailWord_894288
  simp only [CollatzResearch.WordTrace]
  refine ⟨16308681492077391537937759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21744908656103188717250345 16308681492077391537937759)
  ·
    refine ⟨24463022238116087306906639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16308681492077391537937759 24463022238116087306906639)
    ·
      refine ⟨36694533357174130960359959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24463022238116087306906639 36694533357174130960359959)
      ·
        refine ⟨55041800035761196440539939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36694533357174130960359959 55041800035761196440539939)
        ·
          refine ⟨82562700053641794660809909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55041800035761196440539939 82562700053641794660809909)
          ·
            refine ⟨7740253130028918249450929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82562700053641794660809909 7740253130028918249450929)
            ·
              refine ⟨5805189847521688687088197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7740253130028918249450929 5805189847521688687088197)
              ·
                refine ⟨1088473096410316628829037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5805189847521688687088197 1088473096410316628829037)
                ·
                  refine ⟨408177411153868735810889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088473096410316628829037 408177411153868735810889)
                  ·
                    rfl

theorem cell20_894288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_894288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894288 prefixEnd_894288 := by exact prefixLift 894288
  have htrace : WordTrace (prefixWord ++ tailWord_894288) baseStart_894288 baseEnd_894288 := by
    simpa [prefixWord, tailWord_894288, baseEnd_894288] using wordTrace_append hprefix tailTrace_894288
  have hstable : (prefixWord ++ tailWord_894288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894288).length < 2 ^ (prefixWord ++ tailWord_894288).sum := by decide
  have hdescent : baseEnd_894288 < baseStart_894288 := by decide
  rcases family_descends (prefixWord ++ tailWord_894288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894291 : List Nat := [1, 1, 1, 2, 1, 1, 9, 2, 2]
def baseStart_894291 : Nat := 118140960795 + 894291 * 2 ^ 59
def prefixEnd_894291 : Nat := 4983230072969 + 3 ^ 40 * 894291 * 2
def baseEnd_894291 : Nat := 408178780435614058710877

theorem tailTrace_894291 : CollatzResearch.WordTrace tailWord_894291 prefixEnd_894291 408178780435614058710877 := by
  unfold tailWord_894291
  simp only [CollatzResearch.WordTrace]
  refine ⟨32617472403143914588234727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21744981602095943058823151 32617472403143914588234727)
  ·
    refine ⟨48926208604715871882352091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32617472403143914588234727 48926208604715871882352091)
    ·
      refine ⟨73389312907073807823528137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48926208604715871882352091 73389312907073807823528137)
      ·
        refine ⟨55041984680305355867646103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73389312907073807823528137 55041984680305355867646103)
        ·
          refine ⟨82562977020458033801469155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55041984680305355867646103 82562977020458033801469155)
          ·
            refine ⟨123844465530687050702203733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82562977020458033801469155 123844465530687050702203733)
            ·
              refine ⟨725651165218869437708225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 123844465530687050702203733 725651165218869437708225)
              ·
                refine ⟨544238373914152078281169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725651165218869437708225 544238373914152078281169)
                ·
                  refine ⟨408178780435614058710877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544238373914152078281169 408178780435614058710877)
                  ·
                    rfl

theorem cell20_894291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 2].length) (baseStart_894291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894291 prefixEnd_894291 := by exact prefixLift 894291
  have htrace : WordTrace (prefixWord ++ tailWord_894291) baseStart_894291 baseEnd_894291 := by
    simpa [prefixWord, tailWord_894291, baseEnd_894291] using wordTrace_append hprefix tailTrace_894291
  have hstable : (prefixWord ++ tailWord_894291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894291).length < 2 ^ (prefixWord ++ tailWord_894291).sum := by decide
  have hdescent : baseEnd_894291 < baseStart_894291 := by decide
  rcases family_descends (prefixWord ++ tailWord_894291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894340 : List Nat := [2, 3, 2, 1, 1, 11]
def baseStart_894340 : Nat := 118140960795 + 894340 * 2 ^ 59
def prefixEnd_894340 : Nat := 4983230072969 + 3 ^ 40 * 894340 * 2
def baseEnd_894340 : Nat := 15118560939658802447309

theorem tailTrace_894340 : CollatzResearch.WordTrace tailWord_894340 prefixEnd_894340 15118560939658802447309 := by
  unfold tailWord_894340
  simp only [CollatzResearch.WordTrace]
  refine ⟨16309629789983197978384237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21746173053310930637845649 16309629789983197978384237)
  ·
    refine ⟨6116111171243699241894089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16309629789983197978384237 6116111171243699241894089)
    ·
      refine ⟨4587083378432774431420567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6116111171243699241894089 4587083378432774431420567)
      ·
        refine ⟨6880625067649161647130851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4587083378432774431420567 6880625067649161647130851)
        ·
          refine ⟨10320937601473742470696277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6880625067649161647130851 10320937601473742470696277)
          ·
            refine ⟨15118560939658802447309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10320937601473742470696277 15118560939658802447309)
            ·
              rfl

theorem cell20_894340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 11].length) (baseStart_894340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894340 prefixEnd_894340 := by exact prefixLift 894340
  have htrace : WordTrace (prefixWord ++ tailWord_894340) baseStart_894340 baseEnd_894340 := by
    simpa [prefixWord, tailWord_894340, baseEnd_894340] using wordTrace_append hprefix tailTrace_894340
  have hstable : (prefixWord ++ tailWord_894340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894340).length < 2 ^ (prefixWord ++ tailWord_894340).sum := by decide
  have hdescent : baseEnd_894340 < baseStart_894340 := by decide
  rcases family_descends (prefixWord ++ tailWord_894340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894343 : List Nat := [1, 1, 4, 2, 2, 3, 2, 2, 3]
def baseStart_894343 : Nat := 118140960795 + 894343 * 2 ^ 59
def prefixEnd_894343 : Nat := 4983230072969 + 3 ^ 40 * 894343 * 2
def baseEnd_894343 : Nat := 408202514652532988977331

theorem tailTrace_894343 : CollatzResearch.WordTrace tailWord_894343 prefixEnd_894343 408202514652532988977331 := by
  unfold tailWord_894343
  simp only [CollatzResearch.WordTrace]
  refine ⟨32619368998955527469127683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21746245999303684979418455 32619368998955527469127683)
  ·
    refine ⟨48929053498433291203691525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32619368998955527469127683 48929053498433291203691525)
    ·
      refine ⟨9174197530956242100692161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48929053498433291203691525 9174197530956242100692161)
      ·
        refine ⟨6880648148217181575519121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9174197530956242100692161 6880648148217181575519121)
        ·
          refine ⟨5160486111162886181639341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6880648148217181575519121 5160486111162886181639341)
          ·
            refine ⟨1935182291686082318114753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5160486111162886181639341 1935182291686082318114753)
            ·
              refine ⟨1451386718764561738586065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1935182291686082318114753 1451386718764561738586065)
              ·
                refine ⟨1088540039073421303939549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1451386718764561738586065 1088540039073421303939549)
                ·
                  refine ⟨408202514652532988977331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088540039073421303939549 408202514652532988977331)
                  ·
                    rfl

theorem cell20_894343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 3].length) (baseStart_894343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894343 prefixEnd_894343 := by exact prefixLift 894343
  have htrace : WordTrace (prefixWord ++ tailWord_894343) baseStart_894343 baseEnd_894343 := by
    simpa [prefixWord, tailWord_894343, baseEnd_894343] using wordTrace_append hprefix tailTrace_894343
  have hstable : (prefixWord ++ tailWord_894343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894343).length < 2 ^ (prefixWord ++ tailWord_894343).sum := by decide
  have hdescent : baseEnd_894343 < baseStart_894343 := by decide
  rcases family_descends (prefixWord ++ tailWord_894343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894371 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 4]
def baseStart_894371 : Nat := 118140960795 + 894371 * 2 ^ 59
def prefixEnd_894371 : Nat := 4983230072969 + 3 ^ 40 * 894371 * 2
def baseEnd_894371 : Nat := 408215294615489336043883

theorem tailTrace_894371 : CollatzResearch.WordTrace tailWord_894371 prefixEnd_894371 408215294615489336043883 := by
  unfold tailWord_894371
  simp only [CollatzResearch.WordTrace]
  refine ⟨32620390242854088251146967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21746926828569392167431311 32620390242854088251146967)
  ·
    refine ⟨48930585364281132376720451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32620390242854088251146967 48930585364281132376720451)
    ·
      refine ⟨73395878046421698565080677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48930585364281132376720451 73395878046421698565080677)
      ·
        refine ⟨13761727133704068480952627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73395878046421698565080677 13761727133704068480952627)
        ·
          refine ⟨20642590700556102721428941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13761727133704068480952627 20642590700556102721428941)
          ·
            refine ⟨7740971512708538520535853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20642590700556102721428941 7740971512708538520535853)
            ·
              refine ⟨2902864317265701945200945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7740971512708538520535853 2902864317265701945200945)
              ·
                refine ⟨2177148237949276458900709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2902864317265701945200945 2177148237949276458900709)
                ·
                  refine ⟨408215294615489336043883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2177148237949276458900709 408215294615489336043883)
                  ·
                    rfl

theorem cell20_894371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_894371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894371 prefixEnd_894371 := by exact prefixLift 894371
  have htrace : WordTrace (prefixWord ++ tailWord_894371) baseStart_894371 baseEnd_894371 := by
    simpa [prefixWord, tailWord_894371, baseEnd_894371] using wordTrace_append hprefix tailTrace_894371
  have hstable : (prefixWord ++ tailWord_894371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894371).length < 2 ^ (prefixWord ++ tailWord_894371).sum := by decide
  have hdescent : baseEnd_894371 < baseStart_894371 := by decide
  rcases family_descends (prefixWord ++ tailWord_894371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894433 : List Nat := [1, 2, 3, 1, 2, 3, 4, 4]
def baseStart_894433 : Nat := 118140960795 + 894433 * 2 ^ 59
def prefixEnd_894433 : Nat := 4983230072969 + 3 ^ 40 * 894433 * 2
def baseEnd_894433 : Nat := 136081197701630891992321

theorem tailTrace_894433 : CollatzResearch.WordTrace tailWord_894433 prefixEnd_894433 136081197701630891992321 := by
  unfold tailWord_894433
  simp only [CollatzResearch.WordTrace]
  refine ⟨32622651568629472839903953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21748434379086315226602635 32622651568629472839903953)
  ·
    refine ⟨24466988676472104629927965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32622651568629472839903953 24466988676472104629927965)
    ·
      refine ⟨9175120753677039236222987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24466988676472104629927965 9175120753677039236222987)
      ·
        refine ⟨13762681130515558854334481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9175120753677039236222987 13762681130515558854334481)
        ·
          refine ⟨10322010847886669140750861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13762681130515558854334481 10322010847886669140750861)
          ·
            refine ⟨3870754067957500927781573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10322010847886669140750861 3870754067957500927781573)
            ·
              refine ⟨725766387742031423959045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3870754067957500927781573 725766387742031423959045)
              ·
                refine ⟨136081197701630891992321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 725766387742031423959045 136081197701630891992321)
                ·
                  rfl

theorem cell20_894433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 4].length) (baseStart_894433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894433 prefixEnd_894433 := by exact prefixLift 894433
  have htrace : WordTrace (prefixWord ++ tailWord_894433) baseStart_894433 baseEnd_894433 := by
    simpa [prefixWord, tailWord_894433, baseEnd_894433] using wordTrace_append hprefix tailTrace_894433
  have hstable : (prefixWord ++ tailWord_894433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894433).length < 2 ^ (prefixWord ++ tailWord_894433).sum := by decide
  have hdescent : baseEnd_894433 < baseStart_894433 := by decide
  rcases family_descends (prefixWord ++ tailWord_894433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894470 : List Nat := [6, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_894470 : Nat := 118140960795 + 894470 * 2 ^ 59
def prefixEnd_894470 : Nat := 4983230072969 + 3 ^ 40 * 894470 * 2
def baseEnd_894470 : Nat := 408260480913084991743479

theorem tailTrace_894470 : CollatzResearch.WordTrace tailWord_894470 prefixEnd_894470 408260480913084991743479 := by
  unfold tailWord_894470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1019500033421732129968777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21749334046330285439333909 1019500033421732129968777)
  ·
    refine ⟨764625025066299097476583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1019500033421732129968777 764625025066299097476583)
    ·
      refine ⟨1146937537599448646214875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 764625025066299097476583 1146937537599448646214875)
      ·
        refine ⟨1720406306399172969322313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1146937537599448646214875 1720406306399172969322313)
        ·
          refine ⟨1290304729799379726991735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1720406306399172969322313 1290304729799379726991735)
          ·
            refine ⟨1935457094699069590487603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290304729799379726991735 1935457094699069590487603)
            ·
              refine ⟨2903185642048604385731405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935457094699069590487603 2903185642048604385731405)
              ·
                refine ⟨1088694615768226644649277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2903185642048604385731405 1088694615768226644649277)
                ·
                  refine ⟨408260480913084991743479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088694615768226644649277 408260480913084991743479)
                  ·
                    rfl

theorem cell20_894470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_894470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894470 prefixEnd_894470 := by exact prefixLift 894470
  have htrace : WordTrace (prefixWord ++ tailWord_894470) baseStart_894470 baseEnd_894470 := by
    simpa [prefixWord, tailWord_894470, baseEnd_894470] using wordTrace_append hprefix tailTrace_894470
  have hstable : (prefixWord ++ tailWord_894470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894470).length < 2 ^ (prefixWord ++ tailWord_894470).sum := by decide
  have hdescent : baseEnd_894470 < baseStart_894470 := by decide
  rcases family_descends (prefixWord ++ tailWord_894470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894471 : List Nat := [1, 1, 4, 3, 2, 2, 2, 5]
def baseStart_894471 : Nat := 118140960795 + 894471 * 2 ^ 59
def prefixEnd_894471 : Nat := 4983230072969 + 3 ^ 40 * 894471 * 2
def baseEnd_894471 : Nat := 136086979113444477570047

theorem tailTrace_894471 : CollatzResearch.WordTrace tailWord_894471 prefixEnd_894471 136086979113444477570047 := by
  unfold tailWord_894471
  simp only [CollatzResearch.WordTrace]
  refine ⟨32624037542491805329787267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21749358361661203553191511 32624037542491805329787267)
  ·
    refine ⟨48936056313737707994680901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32624037542491805329787267 48936056313737707994680901)
    ·
      refine ⟨9175510558825820249002669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48936056313737707994680901 9175510558825820249002669)
      ·
        refine ⟨3440816459559682593376001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9175510558825820249002669 3440816459559682593376001)
        ·
          refine ⟨2580612344669761945032001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3440816459559682593376001 2580612344669761945032001)
          ·
            refine ⟨1935459258502321458774001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2580612344669761945032001 1935459258502321458774001)
            ·
              refine ⟨1451594443876741094080501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1935459258502321458774001 1451594443876741094080501)
              ·
                refine ⟨136086979113444477570047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1451594443876741094080501 136086979113444477570047)
                ·
                  rfl

theorem cell20_894471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 5].length) (baseStart_894471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894471 prefixEnd_894471 := by exact prefixLift 894471
  have htrace : WordTrace (prefixWord ++ tailWord_894471) baseStart_894471 baseEnd_894471 := by
    simpa [prefixWord, tailWord_894471, baseEnd_894471] using wordTrace_append hprefix tailTrace_894471
  have hstable : (prefixWord ++ tailWord_894471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894471).length < 2 ^ (prefixWord ++ tailWord_894471).sum := by decide
  have hdescent : baseEnd_894471 < baseStart_894471 := by decide
  rcases family_descends (prefixWord ++ tailWord_894471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894474 : List Nat := [3, 1, 2, 2, 2, 4, 2, 1, 3]
def baseStart_894474 : Nat := 118140960795 + 894474 * 2 ^ 59
def prefixEnd_894474 : Nat := 4983230072969 + 3 ^ 40 * 894474 * 2
def baseEnd_894474 : Nat := 408262306622078755610129

theorem tailTrace_894474 : CollatzResearch.WordTrace tailWord_894474 prefixEnd_894474 408262306622078755610129 := by
  unfold tailWord_894474
  simp only [CollatzResearch.WordTrace]
  refine ⟨8156036740370234210536619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21749431307653957894764317 8156036740370234210536619)
  ·
    refine ⟨12234055110555351315804929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8156036740370234210536619 12234055110555351315804929)
    ·
      refine ⟨9175541332916513486853697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12234055110555351315804929 9175541332916513486853697)
      ·
        refine ⟨6881655999687385115140273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9175541332916513486853697 6881655999687385115140273)
        ·
          refine ⟨5161241999765538836355205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6881655999687385115140273 5161241999765538836355205)
          ·
            refine ⟨967732874956038531816601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5161241999765538836355205 967732874956038531816601)
            ·
              refine ⟨725799656217028898862451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967732874956038531816601 725799656217028898862451)
              ·
                refine ⟨1088699484325543348293677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725799656217028898862451 1088699484325543348293677)
                ·
                  refine ⟨408262306622078755610129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088699484325543348293677 408262306622078755610129)
                  ·
                    rfl

theorem cell20_894474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_894474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894474 prefixEnd_894474 := by exact prefixLift 894474
  have htrace : WordTrace (prefixWord ++ tailWord_894474) baseStart_894474 baseEnd_894474 := by
    simpa [prefixWord, tailWord_894474, baseEnd_894474] using wordTrace_append hprefix tailTrace_894474
  have hstable : (prefixWord ++ tailWord_894474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894474).length < 2 ^ (prefixWord ++ tailWord_894474).sum := by decide
  have hdescent : baseEnd_894474 < baseStart_894474 := by decide
  rcases family_descends (prefixWord ++ tailWord_894474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894492 : List Nat := [2, 2, 3, 1, 2, 1, 1, 8]
def baseStart_894492 : Nat := 118140960795 + 894492 * 2 ^ 59
def prefixEnd_894492 : Nat := 4983230072969 + 3 ^ 40 * 894492 * 2
def baseEnd_894492 : Nat := 136090174104183564336685

theorem tailTrace_894492 : CollatzResearch.WordTrace tailWord_894492 prefixEnd_894492 136090174104183564336685 := by
  unfold tailWord_894492
  simp only [CollatzResearch.WordTrace]
  refine ⟨16312401737707862958150865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21749868983610483944201153 16312401737707862958150865)
  ·
    refine ⟨12234301303280897218613149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16312401737707862958150865 12234301303280897218613149)
    ·
      refine ⟨4587862988730336456979931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12234301303280897218613149 4587862988730336456979931)
      ·
        refine ⟨6881794483095504685469897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4587862988730336456979931 6881794483095504685469897)
        ·
          refine ⟨5161345862321628514102423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6881794483095504685469897 5161345862321628514102423)
          ·
            refine ⟨7742018793482442771153635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5161345862321628514102423 7742018793482442771153635)
            ·
              refine ⟨11613028190223664156730453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7742018793482442771153635 11613028190223664156730453)
              ·
                refine ⟨136090174104183564336685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11613028190223664156730453 136090174104183564336685)
                ·
                  rfl

theorem cell20_894492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_894492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894492 prefixEnd_894492 := by exact prefixLift 894492
  have htrace : WordTrace (prefixWord ++ tailWord_894492) baseStart_894492 baseEnd_894492 := by
    simpa [prefixWord, tailWord_894492, baseEnd_894492] using wordTrace_append hprefix tailTrace_894492
  have hstable : (prefixWord ++ tailWord_894492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894492).length < 2 ^ (prefixWord ++ tailWord_894492).sum := by decide
  have hdescent : baseEnd_894492 < baseStart_894492 := by decide
  rcases family_descends (prefixWord ++ tailWord_894492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894509 : List Nat := [1, 5, 4, 10]
def baseStart_894509 : Nat := 118140960795 + 894509 * 2 ^ 59
def prefixEnd_894509 : Nat := 4983230072969 + 3 ^ 40 * 894509 * 2
def baseEnd_894509 : Nat := 1680157537348864977133

theorem tailTrace_894509 : CollatzResearch.WordTrace tailWord_894509 prefixEnd_894509 1680157537348864977133 := by
  unfold tailWord_894509
  simp only [CollatzResearch.WordTrace]
  refine ⟨32625423516354137819670581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21750282344236091879780387 32625423516354137819670581)
  ·
    refine ⟨3058633454658200420594117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32625423516354137819670581 3058633454658200420594117)
    ·
      refine ⟨573493772748412578861397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3058633454658200420594117 573493772748412578861397)
      ·
        refine ⟨1680157537348864977133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 573493772748412578861397 1680157537348864977133)
        ·
          rfl

theorem cell20_894509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 10].length) (baseStart_894509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894509 prefixEnd_894509 := by exact prefixLift 894509
  have htrace : WordTrace (prefixWord ++ tailWord_894509) baseStart_894509 baseEnd_894509 := by
    simpa [prefixWord, tailWord_894509, baseEnd_894509] using wordTrace_append hprefix tailTrace_894509
  have hstable : (prefixWord ++ tailWord_894509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894509).length < 2 ^ (prefixWord ++ tailWord_894509).sum := by decide
  have hdescent : baseEnd_894509 < baseStart_894509 := by decide
  rcases family_descends (prefixWord ++ tailWord_894509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
