import V185TrunkScan20Chunk090

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_554492 : List Nat := [2, 2, 2, 1, 2, 1, 3, 7]
def baseStart_554492 : Nat := 118140960795 + 554492 * 2 ^ 59
def prefixEnd_554492 : Nat := 4983230072969 + 3 ^ 40 * 554492 * 2
def baseEnd_554492 : Nat := 84361752614207342577761

theorem tailTrace_554492 : CollatzResearch.WordTrace tailWord_554492 prefixEnd_554492 84361752614207342577761 := by
  unfold tailWord_554492
  simp only [CollatzResearch.WordTrace]
  refine ⟨10111992353588829269640865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13482656471451772359521153 10111992353588829269640865)
  ·
    refine ⟨7583994265191621952230649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10111992353588829269640865 7583994265191621952230649)
    ·
      refine ⟨5687995698893716464172987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7583994265191621952230649 5687995698893716464172987)
      ·
        refine ⟨8531993548340574696259481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5687995698893716464172987 8531993548340574696259481)
        ·
          refine ⟨6398995161255431022194611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8531993548340574696259481 6398995161255431022194611)
          ·
            refine ⟨9598492741883146533291917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6398995161255431022194611 9598492741883146533291917)
            ·
              refine ⟨3599434778206179949984469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9598492741883146533291917 3599434778206179949984469)
              ·
                refine ⟨84361752614207342577761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3599434778206179949984469 84361752614207342577761)
                ·
                  rfl

theorem cell20_554492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_554492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554492 prefixEnd_554492 := by exact prefixLift 554492
  have htrace : WordTrace (prefixWord ++ tailWord_554492) baseStart_554492 baseEnd_554492 := by
    simpa [prefixWord, tailWord_554492, baseEnd_554492] using wordTrace_append hprefix tailTrace_554492
  have hstable : (prefixWord ++ tailWord_554492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554492).length < 2 ^ (prefixWord ++ tailWord_554492).sum := by decide
  have hdescent : baseEnd_554492 < baseStart_554492 := by decide
  rcases family_descends (prefixWord ++ tailWord_554492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554499 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 7]
def baseStart_554499 : Nat := 118140960795 + 554499 * 2 ^ 59
def prefixEnd_554499 : Nat := 4983230072969 + 3 ^ 40 * 554499 * 2
def baseEnd_554499 : Nat := 253088452833361114499921

theorem tailTrace_554499 : CollatzResearch.WordTrace tailWord_554499 prefixEnd_554499 253088452833361114499921 := by
  unfold tailWord_554499
  simp only [CollatzResearch.WordTrace]
  refine ⟨20224240018152298734786551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13482826678768199156524367 20224240018152298734786551)
  ·
    refine ⟨30336360027228448102179827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20224240018152298734786551 30336360027228448102179827)
    ·
      refine ⟨45504540040842672153269741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30336360027228448102179827 45504540040842672153269741)
      ·
        refine ⟨17064202515316002057476153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45504540040842672153269741 17064202515316002057476153)
        ·
          refine ⟨12798151886487001543107115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17064202515316002057476153 12798151886487001543107115)
          ·
            refine ⟨19197227829730502314660673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12798151886487001543107115 19197227829730502314660673)
            ·
              refine ⟨14397920872297876735995505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19197227829730502314660673 14397920872297876735995505)
              ·
                refine ⟨10798440654223407551996629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14397920872297876735995505 10798440654223407551996629)
                ·
                  refine ⟨253088452833361114499921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10798440654223407551996629 253088452833361114499921)
                  ·
                    rfl

theorem cell20_554499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_554499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554499 prefixEnd_554499 := by exact prefixLift 554499
  have htrace : WordTrace (prefixWord ++ tailWord_554499) baseStart_554499 baseEnd_554499 := by
    simpa [prefixWord, tailWord_554499, baseEnd_554499] using wordTrace_append hprefix tailTrace_554499
  have hstable : (prefixWord ++ tailWord_554499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554499).length < 2 ^ (prefixWord ++ tailWord_554499).sum := by decide
  have hdescent : baseEnd_554499 < baseStart_554499 := by decide
  rcases family_descends (prefixWord ++ tailWord_554499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554536 : List Nat := [2, 1, 5, 2, 2, 1, 1, 4, 2]
def baseStart_554536 : Nat := 118140960795 + 554536 * 2 ^ 59
def prefixEnd_554536 : Nat := 4983230072969 + 3 ^ 40 * 554536 * 2
def baseEnd_554536 : Nat := 253105340641553430266437

theorem tailTrace_554536 : CollatzResearch.WordTrace tailWord_554536 prefixEnd_554536 253105340641553430266437 := by
  unfold tailWord_554536
  simp only [CollatzResearch.WordTrace]
  refine ⟨10112794759509127026941731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13483726346012169369255641 10112794759509127026941731)
  ·
    refine ⟨15169192139263690540412597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10112794759509127026941731 15169192139263690540412597)
    ·
      refine ⟨1422111763055970988163681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15169192139263690540412597 1422111763055970988163681)
      ·
        refine ⟨1066583822291978241122761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1422111763055970988163681 1066583822291978241122761)
        ·
          refine ⟨799937866718983680842071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1066583822291978241122761 799937866718983680842071)
          ·
            refine ⟨1199906800078475521263107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799937866718983680842071 1199906800078475521263107)
            ·
              refine ⟨1799860200117713281894661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1199906800078475521263107 1799860200117713281894661)
              ·
                refine ⟨337473787522071240355249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1799860200117713281894661 337473787522071240355249)
                ·
                  refine ⟨253105340641553430266437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337473787522071240355249 253105340641553430266437)
                  ·
                    rfl

theorem cell20_554536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 2].length) (baseStart_554536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554536 prefixEnd_554536 := by exact prefixLift 554536
  have htrace : WordTrace (prefixWord ++ tailWord_554536) baseStart_554536 baseEnd_554536 := by
    simpa [prefixWord, tailWord_554536, baseEnd_554536] using wordTrace_append hprefix tailTrace_554536
  have hstable : (prefixWord ++ tailWord_554536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554536).length < 2 ^ (prefixWord ++ tailWord_554536).sum := by decide
  have hdescent : baseEnd_554536 < baseStart_554536 := by decide
  rcases family_descends (prefixWord ++ tailWord_554536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554547 : List Nat := [1, 1, 1, 2, 4, 5, 1, 5]
def baseStart_554547 : Nat := 118140960795 + 554547 * 2 ^ 59
def prefixEnd_554547 : Nat := 4983230072969 + 3 ^ 40 * 554547 * 2
def baseEnd_554547 : Nat := 84370120447095426966575

theorem tailTrace_554547 : CollatzResearch.WordTrace tailWord_554547 prefixEnd_554547 84370120447095426966575 := by
  unfold tailWord_554547
  simp only [CollatzResearch.WordTrace]
  refine ⟨20225990721978402932533895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13483993814652268621689263 20225990721978402932533895)
  ·
    refine ⟨30338986082967604398800843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20225990721978402932533895 30338986082967604398800843)
    ·
      refine ⟨45508479124451406598201265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30338986082967604398800843 45508479124451406598201265)
      ·
        refine ⟨34131359343338554948650949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45508479124451406598201265 34131359343338554948650949)
        ·
          refine ⟨6399629876875979052872053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34131359343338554948650949 6399629876875979052872053)
          ·
            refine ⟨599965300957123036206755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6399629876875979052872053 599965300957123036206755)
            ·
              refine ⟨899947951435684554310133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599965300957123036206755 899947951435684554310133)
              ·
                refine ⟨84370120447095426966575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 899947951435684554310133 84370120447095426966575)
                ·
                  rfl

theorem cell20_554547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 5].length) (baseStart_554547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554547 prefixEnd_554547 := by exact prefixLift 554547
  have htrace : WordTrace (prefixWord ++ tailWord_554547) baseStart_554547 baseEnd_554547 := by
    simpa [prefixWord, tailWord_554547, baseEnd_554547] using wordTrace_append hprefix tailTrace_554547
  have hstable : (prefixWord ++ tailWord_554547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554547).length < 2 ^ (prefixWord ++ tailWord_554547).sum := by decide
  have hdescent : baseEnd_554547 < baseStart_554547 := by decide
  rcases family_descends (prefixWord ++ tailWord_554547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554554 : List Nat := [3, 1, 1, 1, 3, 2, 1, 5, 3]
def baseStart_554554 : Nat := 118140960795 + 554554 * 2 ^ 59
def prefixEnd_554554 : Nat := 4983230072969 + 3 ^ 40 * 554554 * 2
def baseEnd_554554 : Nat := 253113556332025367666363

theorem tailTrace_554554 : CollatzResearch.WordTrace tailWord_554554 prefixEnd_554554 253113556332025367666363 := by
  unfold tailWord_554554
  simp only [CollatzResearch.WordTrace]
  refine ⟨5056561508238260782009679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13484164021968695418692477 5056561508238260782009679)
  ·
    refine ⟨7584842262357391173014519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5056561508238260782009679 7584842262357391173014519)
    ·
      refine ⟨11377263393536086759521779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7584842262357391173014519 11377263393536086759521779)
      ·
        refine ⟨17065895090304130139282669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11377263393536086759521779 17065895090304130139282669)
        ·
          refine ⟨6399710658864048802231001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17065895090304130139282669 6399710658864048802231001)
          ·
            refine ⟨4799782994148036601673251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6399710658864048802231001 4799782994148036601673251)
            ·
              refine ⟨7199674491222054902509877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4799782994148036601673251 7199674491222054902509877)
              ·
                refine ⟨674969483552067647110301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7199674491222054902509877 674969483552067647110301)
                ·
                  refine ⟨253113556332025367666363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 674969483552067647110301 253113556332025367666363)
                  ·
                    rfl

theorem cell20_554554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_554554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554554 prefixEnd_554554 := by exact prefixLift 554554
  have htrace : WordTrace (prefixWord ++ tailWord_554554) baseStart_554554 baseEnd_554554 := by
    simpa [prefixWord, tailWord_554554, baseEnd_554554] using wordTrace_append hprefix tailTrace_554554
  have hstable : (prefixWord ++ tailWord_554554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554554).length < 2 ^ (prefixWord ++ tailWord_554554).sum := by decide
  have hdescent : baseEnd_554554 < baseStart_554554 := by decide
  rcases family_descends (prefixWord ++ tailWord_554554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554575 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 5]
def baseStart_554575 : Nat := 118140960795 + 554575 * 2 ^ 59
def prefixEnd_554575 : Nat := 4983230072969 + 3 ^ 40 * 554575 * 2
def baseEnd_554575 : Nat := 253123141304242627966277

theorem tailTrace_554575 : CollatzResearch.WordTrace tailWord_554575 prefixEnd_554575 253123141304242627966277 := by
  unfold tailWord_554575
  simp only [CollatzResearch.WordTrace]
  refine ⟨20227011965876963714553179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13484674643917975809702119 20227011965876963714553179)
  ·
    refine ⟨30340517948815445571829769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20227011965876963714553179 30340517948815445571829769)
    ·
      refine ⟨22755388461611584178872327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30340517948815445571829769 22755388461611584178872327)
      ·
        refine ⟨34133082692417376268308491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22755388461611584178872327 34133082692417376268308491)
        ·
          refine ⟨51199624038626064402462737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34133082692417376268308491 51199624038626064402462737)
          ·
            refine ⟨38399718028969548301847053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51199624038626064402462737 38399718028969548301847053)
            ·
              refine ⟨14399894260863580613192645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38399718028969548301847053 14399894260863580613192645)
              ·
                refine ⟨2699980173911921364973621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14399894260863580613192645 2699980173911921364973621)
                ·
                  refine ⟨253123141304242627966277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2699980173911921364973621 253123141304242627966277)
                  ·
                    rfl

theorem cell20_554575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_554575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554575 prefixEnd_554575 := by exact prefixLift 554575
  have htrace : WordTrace (prefixWord ++ tailWord_554575) baseStart_554575 baseEnd_554575 := by
    simpa [prefixWord, tailWord_554575, baseEnd_554575] using wordTrace_append hprefix tailTrace_554575
  have hstable : (prefixWord ++ tailWord_554575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554575).length < 2 ^ (prefixWord ++ tailWord_554575).sum := by decide
  have hdescent : baseEnd_554575 < baseStart_554575 := by decide
  rcases family_descends (prefixWord ++ tailWord_554575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554588 : List Nat := [2, 2, 4, 1, 2, 3, 1, 2, 3]
def baseStart_554588 : Nat := 118140960795 + 554588 * 2 ^ 59
def prefixEnd_554588 : Nat := 4983230072969 + 3 ^ 40 * 554588 * 2
def baseEnd_554588 : Nat := 253129074858472360532891

theorem tailTrace_554588 : CollatzResearch.WordTrace tailWord_554588 prefixEnd_554588 253129074858472360532891 := by
  unfold tailWord_554588
  simp only [CollatzResearch.WordTrace]
  refine ⟨10113743057414933467388209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13484990743219911289850945 10113743057414933467388209)
  ·
    refine ⟨7585307293061200100541157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10113743057414933467388209 7585307293061200100541157)
    ·
      refine ⟨1422245117448975018851467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7585307293061200100541157 1422245117448975018851467)
      ·
        refine ⟨2133367676173462528277201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1422245117448975018851467 2133367676173462528277201)
        ·
          refine ⟨1600025757130096896207901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2133367676173462528277201 1600025757130096896207901)
          ·
            refine ⟨600009658923786336077963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1600025757130096896207901 600009658923786336077963)
            ·
              refine ⟨900014488385679504116945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600009658923786336077963 900014488385679504116945)
              ·
                refine ⟨675010866289259628087709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 900014488385679504116945 675010866289259628087709)
                ·
                  refine ⟨253129074858472360532891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 675010866289259628087709 253129074858472360532891)
                  ·
                    rfl

theorem cell20_554588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_554588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554588 prefixEnd_554588 := by exact prefixLift 554588
  have htrace : WordTrace (prefixWord ++ tailWord_554588) baseStart_554588 baseEnd_554588 := by
    simpa [prefixWord, tailWord_554588, baseEnd_554588] using wordTrace_append hprefix tailTrace_554588
  have hstable : (prefixWord ++ tailWord_554588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554588).length < 2 ^ (prefixWord ++ tailWord_554588).sum := by decide
  have hdescent : baseEnd_554588 < baseStart_554588 := by decide
  rcases family_descends (prefixWord ++ tailWord_554588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554599 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 4]
def baseStart_554599 : Nat := 118140960795 + 554599 * 2 ^ 59
def prefixEnd_554599 : Nat := 4983230072969 + 3 ^ 40 * 554599 * 2
def baseEnd_554599 : Nat := 253134095558205211166179

theorem tailTrace_554599 : CollatzResearch.WordTrace tailWord_554599 prefixEnd_554599 253134095558205211166179 := by
  unfold tailWord_554599
  simp only [CollatzResearch.WordTrace]
  refine ⟨20227887317790015813426851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13485258211860010542284567 20227887317790015813426851)
  ·
    refine ⟨30341830976685023720140277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20227887317790015813426851 30341830976685023720140277)
    ·
      refine ⟨2844546654064220973763151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30341830976685023720140277 2844546654064220973763151)
      ·
        refine ⟨4266819981096331460644727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2844546654064220973763151 4266819981096331460644727)
        ·
          refine ⟨6400229971644497190967091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4266819981096331460644727 6400229971644497190967091)
          ·
            refine ⟨9600344957466745786450637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6400229971644497190967091 9600344957466745786450637)
            ·
              refine ⟨3600129359050029669918989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9600344957466745786450637 3600129359050029669918989)
              ·
                refine ⟨1350048509643761126219621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3600129359050029669918989 1350048509643761126219621)
                ·
                  refine ⟨253134095558205211166179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1350048509643761126219621 253134095558205211166179)
                  ·
                    rfl

theorem cell20_554599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_554599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554599 prefixEnd_554599 := by exact prefixLift 554599
  have htrace : WordTrace (prefixWord ++ tailWord_554599) baseStart_554599 baseEnd_554599 := by
    simpa [prefixWord, tailWord_554599, baseEnd_554599] using wordTrace_append hprefix tailTrace_554599
  have hstable : (prefixWord ++ tailWord_554599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554599).length < 2 ^ (prefixWord ++ tailWord_554599).sum := by decide
  have hdescent : baseEnd_554599 < baseStart_554599 := by decide
  rcases family_descends (prefixWord ++ tailWord_554599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554678 : List Nat := [5, 1, 3, 1, 1, 1, 2, 6]
def baseStart_554678 : Nat := 118140960795 + 554678 * 2 ^ 59
def prefixEnd_554678 : Nat := 4983230072969 + 3 ^ 40 * 554678 * 2
def baseEnd_554678 : Nat := 84390051103610682510841

theorem tailTrace_554678 : CollatzResearch.WordTrace tailWord_554678 prefixEnd_554678 84390051103610682510841 := by
  unfold tailWord_554678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1264423042781488269097043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13487179123002541537035125 1264423042781488269097043)
  ·
    refine ⟨1896634564172232403645565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1264423042781488269097043 1896634564172232403645565)
    ·
      refine ⟨711237961564587151367087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1896634564172232403645565 711237961564587151367087)
      ·
        refine ⟨1066856942346880727050631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711237961564587151367087 1066856942346880727050631)
        ·
          refine ⟨1600285413520321090575947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066856942346880727050631 1600285413520321090575947)
          ·
            refine ⟨2400428120280481635863921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1600285413520321090575947 2400428120280481635863921)
            ·
              refine ⟨1800321090210361226897941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2400428120280481635863921 1800321090210361226897941)
              ·
                refine ⟨84390051103610682510841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1800321090210361226897941 84390051103610682510841)
                ·
                  rfl

theorem cell20_554678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_554678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554678 prefixEnd_554678 := by exact prefixLift 554678
  have htrace : WordTrace (prefixWord ++ tailWord_554678) baseStart_554678 baseEnd_554678 := by
    simpa [prefixWord, tailWord_554678, baseEnd_554678] using wordTrace_append hprefix tailTrace_554678
  have hstable : (prefixWord ++ tailWord_554678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554678).length < 2 ^ (prefixWord ++ tailWord_554678).sum := by decide
  have hdescent : baseEnd_554678 < baseStart_554678 := by decide
  rcases family_descends (prefixWord ++ tailWord_554678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554682 : List Nat := [3, 1, 1, 1, 2, 4, 2, 6]
def baseStart_554682 : Nat := 118140960795 + 554682 * 2 ^ 59
def prefixEnd_554682 : Nat := 4983230072969 + 3 ^ 40 * 554682 * 2
def baseEnd_554682 : Nat := 84390659673275270466391

theorem tailTrace_554682 : CollatzResearch.WordTrace tailWord_554682 prefixEnd_554682 84390659673275270466391 := by
  unfold tailWord_554682
  simp only [CollatzResearch.WordTrace]
  refine ⟨5057728644122330247174575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13487276384326213992465533 5057728644122330247174575)
  ·
    refine ⟨7586592966183495370761863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5057728644122330247174575 7586592966183495370761863)
    ·
      refine ⟨11379889449275243056142795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7586592966183495370761863 11379889449275243056142795)
      ·
        refine ⟨17069834173912864584214193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11379889449275243056142795 17069834173912864584214193)
        ·
          refine ⟨12802375630434648438160645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17069834173912864584214193 12802375630434648438160645)
          ·
            refine ⟨2400445430706496582155121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12802375630434648438160645 2400445430706496582155121)
            ·
              refine ⟨1800334073029872436616341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2400445430706496582155121 1800334073029872436616341)
              ·
                refine ⟨84390659673275270466391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1800334073029872436616341 84390659673275270466391)
                ·
                  rfl

theorem cell20_554682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_554682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554682 prefixEnd_554682 := by exact prefixLift 554682
  have htrace : WordTrace (prefixWord ++ tailWord_554682) baseStart_554682 baseEnd_554682 := by
    simpa [prefixWord, tailWord_554682, baseEnd_554682] using wordTrace_append hprefix tailTrace_554682
  have hstable : (prefixWord ++ tailWord_554682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554682).length < 2 ^ (prefixWord ++ tailWord_554682).sum := by decide
  have hdescent : baseEnd_554682 < baseStart_554682 := by decide
  rcases family_descends (prefixWord ++ tailWord_554682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554720 : List Nat := [2, 1, 1, 3, 1, 2, 5, 5]
def baseStart_554720 : Nat := 118140960795 + 554720 * 2 ^ 59
def prefixEnd_554720 : Nat := 4983230072969 + 3 ^ 40 * 554720 * 2
def baseEnd_554720 : Nat := 84396441085088856044117

theorem tailTrace_554720 : CollatzResearch.WordTrace tailWord_554720 prefixEnd_554720 84396441085088856044117 := by
  unfold tailWord_554720
  simp only [CollatzResearch.WordTrace]
  refine ⟨10116150275175826739290807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13488200366901102319054409 10116150275175826739290807)
  ·
    refine ⟨15174225412763740108936211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10116150275175826739290807 15174225412763740108936211)
    ·
      refine ⟨22761338119145610163404317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15174225412763740108936211 22761338119145610163404317)
      ·
        refine ⟨8535501794679603811276619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22761338119145610163404317 8535501794679603811276619)
        ·
          refine ⟨12803252692019405716914929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8535501794679603811276619 12803252692019405716914929)
          ·
            refine ⟨9602439519014554287686197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12803252692019405716914929 9602439519014554287686197)
            ·
              refine ⟨900228704907614464470581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9602439519014554287686197 900228704907614464470581)
              ·
                refine ⟨84396441085088856044117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 900228704907614464470581 84396441085088856044117)
                ·
                  rfl

theorem cell20_554720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_554720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554720 prefixEnd_554720 := by exact prefixLift 554720
  have htrace : WordTrace (prefixWord ++ tailWord_554720) baseStart_554720 baseEnd_554720 := by
    simpa [prefixWord, tailWord_554720, baseEnd_554720] using wordTrace_append hprefix tailTrace_554720
  have hstable : (prefixWord ++ tailWord_554720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554720).length < 2 ^ (prefixWord ++ tailWord_554720).sum := by decide
  have hdescent : baseEnd_554720 < baseStart_554720 := by decide
  rcases family_descends (prefixWord ++ tailWord_554720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554737 : List Nat := [1, 2, 2, 2, 2, 4, 3, 4]
def baseStart_554737 : Nat := 118140960795 + 554737 * 2 ^ 59
def prefixEnd_554737 : Nat := 4983230072969 + 3 ^ 40 * 554737 * 2
def baseEnd_554737 : Nat := 84399027506163354855205

theorem tailTrace_554737 : CollatzResearch.WordTrace tailWord_554737 prefixEnd_554737 84399027506163354855205 := by
  unfold tailWord_554737
  simp only [CollatzResearch.WordTrace]
  refine ⟨20232920591290065381950465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13488613727526710254633643 20232920591290065381950465)
  ·
    refine ⟨15174690443467549036462849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20232920591290065381950465 15174690443467549036462849)
    ·
      refine ⟨11381017832600661777347137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15174690443467549036462849 11381017832600661777347137)
      ·
        refine ⟨8535763374450496333010353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11381017832600661777347137 8535763374450496333010353)
        ·
          refine ⟨6401822530837872249757765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8535763374450496333010353 6401822530837872249757765)
          ·
            refine ⟨1200341724532101046829581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6401822530837872249757765 1200341724532101046829581)
            ·
              refine ⟨450128146699537892561093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1200341724532101046829581 450128146699537892561093)
              ·
                refine ⟨84399027506163354855205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 450128146699537892561093 84399027506163354855205)
                ·
                  rfl

theorem cell20_554737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 4].length) (baseStart_554737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554737 prefixEnd_554737 := by exact prefixLift 554737
  have htrace : WordTrace (prefixWord ++ tailWord_554737) baseStart_554737 baseEnd_554737 := by
    simpa [prefixWord, tailWord_554737, baseEnd_554737] using wordTrace_append hprefix tailTrace_554737
  have hstable : (prefixWord ++ tailWord_554737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554737).length < 2 ^ (prefixWord ++ tailWord_554737).sum := by decide
  have hdescent : baseEnd_554737 < baseStart_554737 := by decide
  rcases family_descends (prefixWord ++ tailWord_554737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554789 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 4]
def baseStart_554789 : Nat := 118140960795 + 554789 * 2 ^ 59
def prefixEnd_554789 : Nat := 4983230072969 + 3 ^ 40 * 554789 * 2
def baseEnd_554789 : Nat := 253220816735408994832069

theorem tailTrace_554789 : CollatzResearch.WordTrace tailWord_554789 prefixEnd_554789 253220816735408994832069 := by
  unfold tailWord_554789
  simp only [CollatzResearch.WordTrace]
  refine ⟨20234817187101678262843421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13489878124734452175228947 20234817187101678262843421)
  ·
    refine ⟨7588056445163129348566283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20234817187101678262843421 7588056445163129348566283)
    ·
      refine ⟨11382084667744694022849425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7588056445163129348566283 11382084667744694022849425)
      ·
        refine ⟨8536563500808520517137069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11382084667744694022849425 8536563500808520517137069)
        ·
          refine ⟨3201211312803195193926401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8536563500808520517137069 3201211312803195193926401)
          ·
            refine ⟨2400908484602396395444801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3201211312803195193926401 2400908484602396395444801)
            ·
              refine ⟨1800681363451797296583601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2400908484602396395444801 1800681363451797296583601)
              ·
                refine ⟨1350511022588847972437701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1800681363451797296583601 1350511022588847972437701)
                ·
                  refine ⟨253220816735408994832069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1350511022588847972437701 253220816735408994832069)
                  ·
                    rfl

theorem cell20_554789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_554789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554789 prefixEnd_554789 := by exact prefixLift 554789
  have htrace : WordTrace (prefixWord ++ tailWord_554789) baseStart_554789 baseEnd_554789 := by
    simpa [prefixWord, tailWord_554789, baseEnd_554789] using wordTrace_append hprefix tailTrace_554789
  have hstable : (prefixWord ++ tailWord_554789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554789).length < 2 ^ (prefixWord ++ tailWord_554789).sum := by decide
  have hdescent : baseEnd_554789 < baseStart_554789 := by decide
  rcases family_descends (prefixWord ++ tailWord_554789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554792 : List Nat := [2, 1, 5, 1, 1, 4, 2, 4]
def baseStart_554792 : Nat := 118140960795 + 554792 * 2 ^ 59
def prefixEnd_554792 : Nat := 4983230072969 + 3 ^ 40 * 554792 * 2
def baseEnd_554792 : Nat := 84407395339051439244019

theorem tailTrace_554792 : CollatzResearch.WordTrace tailWord_554792 prefixEnd_554792 84407395339051439244019 := by
  unfold tailWord_554792
  simp only [CollatzResearch.WordTrace]
  refine ⟨10117463303045404887601315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13489951070727206516801753 10117463303045404887601315)
  ·
    refine ⟨15176194954568107331401973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10117463303045404887601315 15176194954568107331401973)
    ·
      refine ⟨1422768276990760062318935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15176194954568107331401973 1422768276990760062318935)
      ·
        refine ⟨2134152415486140093478403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1422768276990760062318935 2134152415486140093478403)
        ·
          refine ⟨3201228623229210140217605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2134152415486140093478403 3201228623229210140217605)
          ·
            refine ⟨600230366855476901290801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3201228623229210140217605 600230366855476901290801)
            ·
              refine ⟨450172775141607675968101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 600230366855476901290801 450172775141607675968101)
              ·
                refine ⟨84407395339051439244019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 450172775141607675968101 84407395339051439244019)
                ·
                  rfl

theorem cell20_554792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_554792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554792 prefixEnd_554792 := by exact prefixLift 554792
  have htrace : WordTrace (prefixWord ++ tailWord_554792) baseStart_554792 baseEnd_554792 := by
    simpa [prefixWord, tailWord_554792, baseEnd_554792] using wordTrace_append hprefix tailTrace_554792
  have hstable : (prefixWord ++ tailWord_554792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554792).length < 2 ^ (prefixWord ++ tailWord_554792).sum := by decide
  have hdescent : baseEnd_554792 < baseStart_554792 := by decide
  rcases family_descends (prefixWord ++ tailWord_554792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554796 : List Nat := [2, 2, 1, 1, 1, 6, 1, 6]
def baseStart_554796 : Nat := 118140960795 + 554796 * 2 ^ 59
def prefixEnd_554796 : Nat := 4983230072969 + 3 ^ 40 * 554796 * 2
def baseEnd_554796 : Nat := 84408003908716027199569

theorem tailTrace_554796 : CollatzResearch.WordTrace tailWord_554796 prefixEnd_554796 84408003908716027199569 := by
  unfold tailWord_554796
  simp only [CollatzResearch.WordTrace]
  refine ⟨10117536249038159229174121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13490048332050878972232161 10117536249038159229174121)
  ·
    refine ⟨7588152186778619421880591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10117536249038159229174121 7588152186778619421880591)
    ·
      refine ⟨11382228280167929132820887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7588152186778619421880591 11382228280167929132820887)
      ·
        refine ⟨17073342420251893699231331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11382228280167929132820887 17073342420251893699231331)
        ·
          refine ⟨25610013630377840548846997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17073342420251893699231331 25610013630377840548846997)
          ·
            refine ⟨1200469388923961275727203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25610013630377840548846997 1200469388923961275727203)
            ·
              refine ⟨1800704083385941913590805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1200469388923961275727203 1800704083385941913590805)
              ·
                refine ⟨84408003908716027199569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1800704083385941913590805 84408003908716027199569)
                ·
                  rfl

theorem cell20_554796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_554796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554796 prefixEnd_554796 := by exact prefixLift 554796
  have htrace : WordTrace (prefixWord ++ tailWord_554796) baseStart_554796 baseEnd_554796 := by
    simpa [prefixWord, tailWord_554796, baseEnd_554796] using wordTrace_append hprefix tailTrace_554796
  have hstable : (prefixWord ++ tailWord_554796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554796).length < 2 ^ (prefixWord ++ tailWord_554796).sum := by decide
  have hdescent : baseEnd_554796 < baseStart_554796 := by decide
  rcases family_descends (prefixWord ++ tailWord_554796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554813 : List Nat := [1, 4, 1, 4, 1, 3, 6]
def baseStart_554813 : Nat := 118140960795 + 554813 * 2 ^ 59
def prefixEnd_554813 : Nat := 4983230072969 + 3 ^ 40 * 554813 * 2
def baseEnd_554813 : Nat := 28136863443263508670219

theorem tailTrace_554813 : CollatzResearch.WordTrace tailWord_554813 prefixEnd_554813 28136863443263508670219 := by
  unfold tailWord_554813
  simp only [CollatzResearch.WordTrace]
  refine ⟨20235692539014730361717093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13490461692676486907811395 20235692539014730361717093)
  ·
    refine ⟨3794192351065261942821955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20235692539014730361717093 3794192351065261942821955)
    ·
      refine ⟨5691288526597892914232933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3794192351065261942821955 5691288526597892914232933)
      ·
        refine ⟨1067116598737104921418675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5691288526597892914232933 1067116598737104921418675)
        ·
          refine ⟨1600674898105657382128013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1067116598737104921418675 1600674898105657382128013)
          ·
            refine ⟨600253086789621518298005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1600674898105657382128013 600253086789621518298005)
            ·
              refine ⟨28136863443263508670219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 600253086789621518298005 28136863443263508670219)
              ·
                rfl

theorem cell20_554813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 6].length) (baseStart_554813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554813 prefixEnd_554813 := by exact prefixLift 554813
  have htrace : WordTrace (prefixWord ++ tailWord_554813) baseStart_554813 baseEnd_554813 := by
    simpa [prefixWord, tailWord_554813, baseEnd_554813] using wordTrace_append hprefix tailTrace_554813
  have hstable : (prefixWord ++ tailWord_554813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554813).length < 2 ^ (prefixWord ++ tailWord_554813).sum := by decide
  have hdescent : baseEnd_554813 < baseStart_554813 := by decide
  rcases family_descends (prefixWord ++ tailWord_554813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554834 : List Nat := [3, 2, 2, 1, 1, 3, 1, 7]
def baseStart_554834 : Nat := 118140960795 + 554834 * 2 ^ 59
def prefixEnd_554834 : Nat := 4983230072969 + 3 ^ 40 * 554834 * 2
def baseEnd_554834 : Nat := 84413785320529612777295

theorem tailTrace_554834 : CollatzResearch.WordTrace tailWord_554834 prefixEnd_554834 84413785320529612777295 := by
  unfold tailWord_554834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5059114617984662737057889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13490972314625767298821037 5059114617984662737057889)
  ·
    refine ⟨3794335963488497052793417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5059114617984662737057889 3794335963488497052793417)
    ·
      refine ⟨2845751972616372789595063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3794335963488497052793417 2845751972616372789595063)
      ·
        refine ⟨4268627958924559184392595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2845751972616372789595063 4268627958924559184392595)
        ·
          refine ⟨6402941938386838776588893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4268627958924559184392595 6402941938386838776588893)
          ·
            refine ⟨2401103226895064541220835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6402941938386838776588893 2401103226895064541220835)
            ·
              refine ⟨3601654840342596811831253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2401103226895064541220835 3601654840342596811831253)
              ·
                refine ⟨84413785320529612777295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3601654840342596811831253 84413785320529612777295)
                ·
                  rfl

theorem cell20_554834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_554834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554834 prefixEnd_554834 := by exact prefixLift 554834
  have htrace : WordTrace (prefixWord ++ tailWord_554834) baseStart_554834 baseEnd_554834 := by
    simpa [prefixWord, tailWord_554834, baseEnd_554834] using wordTrace_append hprefix tailTrace_554834
  have hstable : (prefixWord ++ tailWord_554834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554834).length < 2 ^ (prefixWord ++ tailWord_554834).sum := by decide
  have hdescent : baseEnd_554834 < baseStart_554834 := by decide
  rcases family_descends (prefixWord ++ tailWord_554834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554837 : List Nat := [1, 3, 2, 2, 2, 2, 4, 1, 3]
def baseStart_554837 : Nat := 118140960795 + 554837 * 2 ^ 59
def prefixEnd_554837 : Nat := 4983230072969 + 3 ^ 40 * 554837 * 2
def baseEnd_554837 : Nat := 253242725243334161231873

theorem tailTrace_554837 : CollatzResearch.WordTrace tailWord_554837 prefixEnd_554837 253242725243334161231873 := by
  unfold tailWord_554837
  simp only [CollatzResearch.WordTrace]
  refine ⟨20236567890927782460590765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13491045260618521640393843 20236567890927782460590765)
  ·
    refine ⟨7588712959097918422721537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20236567890927782460590765 7588712959097918422721537)
    ·
      refine ⟨5691534719323438817041153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7588712959097918422721537 5691534719323438817041153)
      ·
        refine ⟨4268651039492579112780865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5691534719323438817041153 4268651039492579112780865)
        ·
          refine ⟨3201488279619434334585649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4268651039492579112780865 3201488279619434334585649)
          ·
            refine ⟨2401116209714575750939237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3201488279619434334585649 2401116209714575750939237)
            ·
              refine ⟨450209289321482953301107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2401116209714575750939237 450209289321482953301107)
              ·
                refine ⟨675313933982224429951661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450209289321482953301107 675313933982224429951661)
                ·
                  refine ⟨253242725243334161231873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 675313933982224429951661 253242725243334161231873)
                  ·
                    rfl

theorem cell20_554837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_554837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554837 prefixEnd_554837 := by exact prefixLift 554837
  have htrace : WordTrace (prefixWord ++ tailWord_554837) baseStart_554837 baseEnd_554837 := by
    simpa [prefixWord, tailWord_554837, baseEnd_554837] using wordTrace_append hprefix tailTrace_554837
  have hstable : (prefixWord ++ tailWord_554837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554837).length < 2 ^ (prefixWord ++ tailWord_554837).sum := by decide
  have hdescent : baseEnd_554837 < baseStart_554837 := by decide
  rcases family_descends (prefixWord ++ tailWord_554837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554878 : List Nat := [4, 2, 3, 1, 1, 2, 1, 4, 2]
def baseStart_554878 : Nat := 118140960795 + 554878 * 2 ^ 59
def prefixEnd_554878 : Nat := 4983230072969 + 3 ^ 40 * 554878 * 2
def baseEnd_554878 : Nat := 253261438760520240865039

theorem tailTrace_554878 : CollatzResearch.WordTrace tailWord_554878 prefixEnd_554878 253261438760520240865039 := by
  unfold tailWord_554878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2529757910472405807854161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13492042189186164308555525 2529757910472405807854161)
  ·
    refine ⟨1897318432854304355890621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2529757910472405807854161 1897318432854304355890621)
    ·
      refine ⟨711494412320364133458983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1897318432854304355890621 711494412320364133458983)
      ·
        refine ⟨1067241618480546200188475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711494412320364133458983 1067241618480546200188475)
        ·
          refine ⟨1600862427720819300282713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1067241618480546200188475 1600862427720819300282713)
          ·
            refine ⟨1200646820790614475212035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1600862427720819300282713 1200646820790614475212035)
            ·
              refine ⟨1800970231185921712818053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1200646820790614475212035 1800970231185921712818053)
              ·
                refine ⟨337681918347360321153385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1800970231185921712818053 337681918347360321153385)
                ·
                  refine ⟨253261438760520240865039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337681918347360321153385 253261438760520240865039)
                  ·
                    rfl

theorem cell20_554878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_554878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554878 prefixEnd_554878 := by exact prefixLift 554878
  have htrace : WordTrace (prefixWord ++ tailWord_554878) baseStart_554878 baseEnd_554878 := by
    simpa [prefixWord, tailWord_554878, baseEnd_554878] using wordTrace_append hprefix tailTrace_554878
  have hstable : (prefixWord ++ tailWord_554878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554878).length < 2 ^ (prefixWord ++ tailWord_554878).sum := by decide
  have hdescent : baseEnd_554878 < baseStart_554878 := by decide
  rcases family_descends (prefixWord ++ tailWord_554878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554902 : List Nat := [5, 3, 1, 1, 2, 1, 3, 4]
def baseStart_554902 : Nat := 118140960795 + 554902 * 2 ^ 59
def prefixEnd_554902 : Nat := 4983230072969 + 3 ^ 40 * 554902 * 2
def baseEnd_554902 : Nat := 84424131004827608021647

theorem tailTrace_554902 : CollatzResearch.WordTrace tailWord_554902 prefixEnd_554902 84424131004827608021647 := by
  unfold tailWord_554902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1264933664730768660106685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13492625757128199041137973 1264933664730768660106685)
  ·
    refine ⟨474350124274038247540007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1264933664730768660106685 474350124274038247540007)
    ·
      refine ⟨711525186411057371310011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 474350124274038247540007 711525186411057371310011)
      ·
        refine ⟨1067287779616586056965017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711525186411057371310011 1067287779616586056965017)
        ·
          refine ⟨800465834712439542723763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1067287779616586056965017 800465834712439542723763)
          ·
            refine ⟨1200698752068659314085645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 800465834712439542723763 1200698752068659314085645)
            ·
              refine ⟨450262032025747242782117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1200698752068659314085645 450262032025747242782117)
              ·
                refine ⟨84424131004827608021647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 450262032025747242782117 84424131004827608021647)
                ·
                  rfl

theorem cell20_554902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_554902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554902 prefixEnd_554902 := by exact prefixLift 554902
  have htrace : WordTrace (prefixWord ++ tailWord_554902) baseStart_554902 baseEnd_554902 := by
    simpa [prefixWord, tailWord_554902, baseEnd_554902] using wordTrace_append hprefix tailTrace_554902
  have hstable : (prefixWord ++ tailWord_554902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554902).length < 2 ^ (prefixWord ++ tailWord_554902).sum := by decide
  have hdescent : baseEnd_554902 < baseStart_554902 := by decide
  rcases family_descends (prefixWord ++ tailWord_554902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554903 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 4]
def baseStart_554903 : Nat := 118140960795 + 554903 * 2 ^ 59
def prefixEnd_554903 : Nat := 4983230072969 + 3 ^ 40 * 554903 * 2
def baseEnd_554903 : Nat := 253272849441731265031603

theorem tailTrace_554903 : CollatzResearch.WordTrace tailWord_554903 prefixEnd_554903 253272849441731265031603 := by
  unfold tailWord_554903
  simp only [CollatzResearch.WordTrace]
  refine ⟨20238975108688675732493363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13492650072459117154995575 20238975108688675732493363)
  ·
    refine ⟨30358462663033013598740045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20238975108688675732493363 30358462663033013598740045)
    ·
      refine ⟨11384423498637380099527517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30358462663033013598740045 11384423498637380099527517)
      ·
        refine ⟨4269158811989017537322819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11384423498637380099527517 4269158811989017537322819)
        ·
          refine ⟨6403738217983526305984229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4269158811989017537322819 6403738217983526305984229)
          ·
            refine ⟨1200700915871911182372043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6403738217983526305984229 1200700915871911182372043)
            ·
              refine ⟨1801051373807866773558065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1200700915871911182372043 1801051373807866773558065)
              ·
                refine ⟨1350788530355900080168549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1801051373807866773558065 1350788530355900080168549)
                ·
                  refine ⟨253272849441731265031603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1350788530355900080168549 253272849441731265031603)
                  ·
                    rfl

theorem cell20_554903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_554903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554903 prefixEnd_554903 := by exact prefixLift 554903
  have htrace : WordTrace (prefixWord ++ tailWord_554903) baseStart_554903 baseEnd_554903 := by
    simpa [prefixWord, tailWord_554903, baseEnd_554903] using wordTrace_append hprefix tailTrace_554903
  have hstable : (prefixWord ++ tailWord_554903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554903).length < 2 ^ (prefixWord ++ tailWord_554903).sum := by decide
  have hdescent : baseEnd_554903 < baseStart_554903 := by decide
  rcases family_descends (prefixWord ++ tailWord_554903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554926 : List Nat := [4, 1, 5, 1, 1, 2, 1, 2, 3]
def baseStart_554926 : Nat := 118140960795 + 554926 * 2 ^ 59
def prefixEnd_554926 : Nat := 4983230072969 + 3 ^ 40 * 554926 * 2
def baseEnd_554926 : Nat := 253283347268445407264843

theorem tailTrace_554926 : CollatzResearch.WordTrace tailWord_554926 prefixEnd_554926 253283347268445407264843 := by
  unfold tailWord_554926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2529976748450668832572579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13493209325070233773720421 2529976748450668832572579)
  ·
    refine ⟨3794965122676003248858869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2529976748450668832572579 3794965122676003248858869)
    ·
      refine ⟨355777980250875304580519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3794965122676003248858869 355777980250875304580519)
      ·
        refine ⟨533666970376312956870779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355777980250875304580519 533666970376312956870779)
        ·
          refine ⟨800500455564469435306169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533666970376312956870779 800500455564469435306169)
          ·
            refine ⟨600375341673352076479627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 800500455564469435306169 600375341673352076479627)
            ·
              refine ⟨900563012510028114719441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600375341673352076479627 900563012510028114719441)
              ·
                refine ⟨675422259382521086039581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 900563012510028114719441 675422259382521086039581)
                ·
                  refine ⟨253283347268445407264843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 675422259382521086039581 253283347268445407264843)
                  ·
                    rfl

theorem cell20_554926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_554926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554926 prefixEnd_554926 := by exact prefixLift 554926
  have htrace : WordTrace (prefixWord ++ tailWord_554926) baseStart_554926 baseEnd_554926 := by
    simpa [prefixWord, tailWord_554926, baseEnd_554926] using wordTrace_append hprefix tailTrace_554926
  have hstable : (prefixWord ++ tailWord_554926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554926).length < 2 ^ (prefixWord ++ tailWord_554926).sum := by decide
  have hdescent : baseEnd_554926 < baseStart_554926 := by decide
  rcases family_descends (prefixWord ++ tailWord_554926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554931 : List Nat := [1, 1, 1, 2, 3, 1, 11]
def baseStart_554931 : Nat := 118140960795 + 554931 * 2 ^ 59
def prefixEnd_554931 : Nat := 4983230072969 + 3 ^ 40 * 554931 * 2
def baseEnd_554931 : Nat := 28142847711631956899795

theorem tailTrace_554931 : CollatzResearch.WordTrace tailWord_554931 prefixEnd_554931 28142847711631956899795 := by
  unfold tailWord_554931
  simp only [CollatzResearch.WordTrace]
  refine ⟨20239996352587236514512647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13493330901724824343008431 20239996352587236514512647)
  ·
    refine ⟨30359994528880854771768971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20239996352587236514512647 30359994528880854771768971)
    ·
      refine ⟨45539991793321282157653457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30359994528880854771768971 45539991793321282157653457)
      ·
        refine ⟨34154993844990961618240093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45539991793321282157653457 34154993844990961618240093)
        ·
          refine ⟨12808122691871610606840035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34154993844990961618240093 12808122691871610606840035)
          ·
            refine ⟨19212184037807415910260053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12808122691871610606840035 19212184037807415910260053)
            ·
              refine ⟨28142847711631956899795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19212184037807415910260053 28142847711631956899795)
              ·
                rfl

theorem cell20_554931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 11].length) (baseStart_554931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554931 prefixEnd_554931 := by exact prefixLift 554931
  have htrace : WordTrace (prefixWord ++ tailWord_554931) baseStart_554931 baseEnd_554931 := by
    simpa [prefixWord, tailWord_554931, baseEnd_554931] using wordTrace_append hprefix tailTrace_554931
  have hstable : (prefixWord ++ tailWord_554931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554931).length < 2 ^ (prefixWord ++ tailWord_554931).sum := by decide
  have hdescent : baseEnd_554931 < baseStart_554931 := by decide
  rcases family_descends (prefixWord ++ tailWord_554931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554941 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 4]
def baseStart_554941 : Nat := 118140960795 + 554941 * 2 ^ 59
def prefixEnd_554941 : Nat := 4983230072969 + 3 ^ 40 * 554941 * 2
def baseEnd_554941 : Nat := 253290193677172021764781

theorem tailTrace_554941 : CollatzResearch.WordTrace tailWord_554941 prefixEnd_554941 253290193677172021764781 := by
  unfold tailWord_554941
  simp only [CollatzResearch.WordTrace]
  refine ⟨20240361082551008222376677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13493574055034005481584451 20240361082551008222376677)
  ·
    refine ⟨3795067702978314041695627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20240361082551008222376677 3795067702978314041695627)
    ·
      refine ⟨5692601554467471062543441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3795067702978314041695627 5692601554467471062543441)
      ·
        refine ⟨4269451165850603296907581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5692601554467471062543441 4269451165850603296907581)
        ·
          refine ⟨1601044187193976236340343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4269451165850603296907581 1601044187193976236340343)
          ·
            refine ⟨2401566280790964354510515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1601044187193976236340343 2401566280790964354510515)
            ·
              refine ⟨3602349421186446531765773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2401566280790964354510515 3602349421186446531765773)
              ·
                refine ⟨1350881032944917449412165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3602349421186446531765773 1350881032944917449412165)
                ·
                  refine ⟨253290193677172021764781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1350881032944917449412165 253290193677172021764781)
                  ·
                    rfl

theorem cell20_554941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_554941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554941 prefixEnd_554941 := by exact prefixLift 554941
  have htrace : WordTrace (prefixWord ++ tailWord_554941) baseStart_554941 baseEnd_554941 := by
    simpa [prefixWord, tailWord_554941, baseEnd_554941] using wordTrace_append hprefix tailTrace_554941
  have hstable : (prefixWord ++ tailWord_554941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554941).length < 2 ^ (prefixWord ++ tailWord_554941).sum := by decide
  have hdescent : baseEnd_554941 < baseStart_554941 := by decide
  rcases family_descends (prefixWord ++ tailWord_554941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554965 : List Nat := [1, 3, 2, 3, 2, 1, 4, 4]
def baseStart_554965 : Nat := 118140960795 + 554965 * 2 ^ 59
def prefixEnd_554965 : Nat := 4983230072969 + 3 ^ 40 * 554965 * 2
def baseEnd_554965 : Nat := 84433715977044868321561

theorem tailTrace_554965 : CollatzResearch.WordTrace tailWord_554965 prefixEnd_554965 84433715977044868321561 := by
  unfold tailWord_554965
  simp only [CollatzResearch.WordTrace]
  refine ⟨20241236434464060321250349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13494157622976040214166899 20241236434464060321250349)
  ·
    refine ⟨7590463662924022620468881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20241236434464060321250349 7590463662924022620468881)
    ·
      refine ⟨5692847747193016965351661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7590463662924022620468881 5692847747193016965351661)
      ·
        refine ⟨2134817905197381362006873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5692847747193016965351661 2134817905197381362006873)
        ·
          refine ⟨1601113428898036021505155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2134817905197381362006873 1601113428898036021505155)
          ·
            refine ⟨2401670143347054032257733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1601113428898036021505155 2401670143347054032257733)
            ·
              refine ⟨450313151877572631048325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2401670143347054032257733 450313151877572631048325)
              ·
                refine ⟨84433715977044868321561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 450313151877572631048325 84433715977044868321561)
                ·
                  rfl

theorem cell20_554965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 4].length) (baseStart_554965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554965 prefixEnd_554965 := by exact prefixLift 554965
  have htrace : WordTrace (prefixWord ++ tailWord_554965) baseStart_554965 baseEnd_554965 := by
    simpa [prefixWord, tailWord_554965, baseEnd_554965] using wordTrace_append hprefix tailTrace_554965
  have hstable : (prefixWord ++ tailWord_554965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554965).length < 2 ^ (prefixWord ++ tailWord_554965).sum := by decide
  have hdescent : baseEnd_554965 < baseStart_554965 := by decide
  rcases family_descends (prefixWord ++ tailWord_554965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554975 : List Nat := [1, 1, 2, 3, 4, 3, 1, 3, 2]
def baseStart_554975 : Nat := 118140960795 + 554975 * 2 ^ 59
def prefixEnd_554975 : Nat := 4983230072969 + 3 ^ 40 * 554975 * 2
def baseEnd_554975 : Nat := 253305712203619014631309

theorem tailTrace_554975 : CollatzResearch.WordTrace tailWord_554975 prefixEnd_554975 253305712203619014631309 := by
  unfold tailWord_554975
  simp only [CollatzResearch.WordTrace]
  refine ⟨20241601164427832029114379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13494400776285221352742919 20241601164427832029114379)
  ·
    refine ⟨30362401746641748043671569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20241601164427832029114379 30362401746641748043671569)
    ·
      refine ⟨22771801309981311032753677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30362401746641748043671569 22771801309981311032753677)
      ·
        refine ⟨8539425491242991637282629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22771801309981311032753677 8539425491242991637282629)
        ·
          refine ⟨1601142279608060931990493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8539425491242991637282629 1601142279608060931990493)
          ·
            refine ⟨600428354853022849496435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1601142279608060931990493 600428354853022849496435)
            ·
              refine ⟨900642532279534274244653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600428354853022849496435 900642532279534274244653)
              ·
                refine ⟨337740949604825352841745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 900642532279534274244653 337740949604825352841745)
                ·
                  refine ⟨253305712203619014631309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337740949604825352841745 253305712203619014631309)
                  ·
                    rfl

theorem cell20_554975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 2].length) (baseStart_554975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554975 prefixEnd_554975 := by exact prefixLift 554975
  have htrace : WordTrace (prefixWord ++ tailWord_554975) baseStart_554975 baseEnd_554975 := by
    simpa [prefixWord, tailWord_554975, baseEnd_554975] using wordTrace_append hprefix tailTrace_554975
  have hstable : (prefixWord ++ tailWord_554975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554975).length < 2 ^ (prefixWord ++ tailWord_554975).sum := by decide
  have hdescent : baseEnd_554975 < baseStart_554975 := by decide
  rcases family_descends (prefixWord ++ tailWord_554975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555006 : List Nat := [4, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_555006 : Nat := 118140960795 + 555006 * 2 ^ 59
def prefixEnd_555006 : Nat := 4983230072969 + 3 ^ 40 * 555006 * 2
def baseEnd_555006 : Nat := 253319861448320684597849

theorem tailTrace_555006 : CollatzResearch.WordTrace tailWord_555006 prefixEnd_555006 253319861448320684597849 := by
  unfold tailWord_555006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2530341478414440540436609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13495154551543682882328581 2530341478414440540436609)
  ·
    refine ⟨1897756108810830405327457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2530341478414440540436609 1897756108810830405327457)
    ·
      refine ⟨1423317081608122803995593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1897756108810830405327457 1423317081608122803995593)
      ·
        refine ⟨1067487811206092102996695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1423317081608122803995593 1067487811206092102996695)
        ·
          refine ⟨1601231716809138154495043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1067487811206092102996695 1601231716809138154495043)
          ·
            refine ⟨2401847575213707231742565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1601231716809138154495043 2401847575213707231742565)
            ·
              refine ⟨450346420352570105951731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2401847575213707231742565 450346420352570105951731)
              ·
                refine ⟨675519630528855158927597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450346420352570105951731 675519630528855158927597)
                ·
                  refine ⟨253319861448320684597849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 675519630528855158927597 253319861448320684597849)
                  ·
                    rfl

theorem cell20_555006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_555006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555006 prefixEnd_555006 := by exact prefixLift 555006
  have htrace : WordTrace (prefixWord ++ tailWord_555006) baseStart_555006 baseEnd_555006 := by
    simpa [prefixWord, tailWord_555006, baseEnd_555006] using wordTrace_append hprefix tailTrace_555006
  have hstable : (prefixWord ++ tailWord_555006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555006).length < 2 ^ (prefixWord ++ tailWord_555006).sum := by decide
  have hdescent : baseEnd_555006 < baseStart_555006 := by decide
  rcases family_descends (prefixWord ++ tailWord_555006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555045 : List Nat := [1, 3, 1, 2, 2, 11]
def baseStart_555045 : Nat := 118140960795 + 555045 * 2 ^ 59
def prefixEnd_555045 : Nat := 4983230072969 + 3 ^ 40 * 555045 * 2
def baseEnd_555045 : Nat := 9382876374481847492507

theorem tailTrace_555045 : CollatzResearch.WordTrace tailWord_555045 prefixEnd_555045 9382876374481847492507 := by
  unfold tailWord_555045
  simp only [CollatzResearch.WordTrace]
  refine ⟨20244154274174233984162589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13496102849449489322775059 20244154274174233984162589)
  ·
    refine ⟨7591557852815337744060971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20244154274174233984162589 7591557852815337744060971)
    ·
      refine ⟨11387336779223006616091457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7591557852815337744060971 11387336779223006616091457)
      ·
        refine ⟨8540502584417254962068593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11387336779223006616091457 8540502584417254962068593)
        ·
          refine ⟨6405376938312941221551445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8540502584417254962068593 6405376938312941221551445)
          ·
            refine ⟨9382876374481847492507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6405376938312941221551445 9382876374481847492507)
            ·
              rfl

theorem cell20_555045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 11].length) (baseStart_555045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555045 prefixEnd_555045 := by exact prefixLift 555045
  have htrace : WordTrace (prefixWord ++ tailWord_555045) baseStart_555045 baseEnd_555045 := by
    simpa [prefixWord, tailWord_555045, baseEnd_555045] using wordTrace_append hprefix tailTrace_555045
  have hstable : (prefixWord ++ tailWord_555045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555045).length < 2 ^ (prefixWord ++ tailWord_555045).sum := by decide
  have hdescent : baseEnd_555045 < baseStart_555045 := by decide
  rcases family_descends (prefixWord ++ tailWord_555045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555047 : List Nat := [1, 1, 7, 1, 2, 2, 2, 2, 2]
def baseStart_555047 : Nat := 118140960795 + 555047 * 2 ^ 59
def prefixEnd_555047 : Nat := 4983230072969 + 3 ^ 40 * 555047 * 2
def baseEnd_555047 : Nat := 253338574965506764231015

theorem tailTrace_555047 : CollatzResearch.WordTrace tailWord_555047 prefixEnd_555047 253338574965506764231015 := by
  unfold tailWord_555047
  simp only [CollatzResearch.WordTrace]
  refine ⟨20244227220166988325735395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13496151480111325550490263 20244227220166988325735395)
  ·
    refine ⟨30366340830250482488603093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20244227220166988325735395 30366340830250482488603093)
    ·
      refine ⟨711711113208995683326635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 30366340830250482488603093 711711113208995683326635)
      ·
        refine ⟨1067566669813493524989953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711711113208995683326635 1067566669813493524989953)
        ·
          refine ⟨800675002360120143742465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1067566669813493524989953 800675002360120143742465)
          ·
            refine ⟨600506251770090107806849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 800675002360120143742465 600506251770090107806849)
            ·
              refine ⟨450379688827567580855137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 600506251770090107806849 450379688827567580855137)
              ·
                refine ⟨337784766620675685641353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450379688827567580855137 337784766620675685641353)
                ·
                  refine ⟨253338574965506764231015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337784766620675685641353 253338574965506764231015)
                  ·
                    rfl

theorem cell20_555047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 2].length) (baseStart_555047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555047 prefixEnd_555047 := by exact prefixLift 555047
  have htrace : WordTrace (prefixWord ++ tailWord_555047) baseStart_555047 baseEnd_555047 := by
    simpa [prefixWord, tailWord_555047, baseEnd_555047] using wordTrace_append hprefix tailTrace_555047
  have hstable : (prefixWord ++ tailWord_555047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555047).length < 2 ^ (prefixWord ++ tailWord_555047).sum := by decide
  have hdescent : baseEnd_555047 < baseStart_555047 := by decide
  rcases family_descends (prefixWord ++ tailWord_555047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555100 : List Nat := [2, 2, 4, 1, 1, 3, 7]
def baseStart_555100 : Nat := 118140960795 + 555100 * 2 ^ 59
def prefixEnd_555100 : Nat := 4983230072969 + 3 ^ 40 * 555100 * 2
def baseEnd_555100 : Nat := 28151418401074903940459

theorem tailTrace_555100 : CollatzResearch.WordTrace tailWord_555100 prefixEnd_555100 28151418401074903940459 := by
  unfold tailWord_555100
  simp only [CollatzResearch.WordTrace]
  refine ⟨10123080144487489188707377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13497440192649985584943169 10123080144487489188707377)
  ·
    refine ⟨7592310108365616891530533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10123080144487489188707377 7592310108365616891530533)
    ·
      refine ⟨1423558145318553167161975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7592310108365616891530533 1423558145318553167161975)
      ·
        refine ⟨2135337217977829750742963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1423558145318553167161975 2135337217977829750742963)
        ·
          refine ⟨3203005826966744626114445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2135337217977829750742963 3203005826966744626114445)
          ·
            refine ⟨1201127185112529234792917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3203005826966744626114445 1201127185112529234792917)
            ·
              refine ⟨28151418401074903940459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1201127185112529234792917 28151418401074903940459)
              ·
                rfl

theorem cell20_555100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 7].length) (baseStart_555100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555100 prefixEnd_555100 := by exact prefixLift 555100
  have htrace : WordTrace (prefixWord ++ tailWord_555100) baseStart_555100 baseEnd_555100 := by
    simpa [prefixWord, tailWord_555100, baseEnd_555100] using wordTrace_append hprefix tailTrace_555100
  have hstable : (prefixWord ++ tailWord_555100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555100).length < 2 ^ (prefixWord ++ tailWord_555100).sum := by decide
  have hdescent : baseEnd_555100 < baseStart_555100 := by decide
  rcases family_descends (prefixWord ++ tailWord_555100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555121 : List Nat := [1, 2, 2, 2, 1, 1, 4, 7]
def baseStart_555121 : Nat := 118140960795 + 555121 * 2 ^ 59
def prefixEnd_555121 : Nat := 4983230072969 + 3 ^ 40 * 555121 * 2
def baseEnd_555121 : Nat := 84457450193963798588015

theorem tailTrace_555121 : CollatzResearch.WordTrace tailWord_555121 prefixEnd_555121 84457450193963798588015 := by
  unfold tailWord_555121
  simp only [CollatzResearch.WordTrace]
  refine ⟨20246926221898898963929217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13497950814599265975952811 20246926221898898963929217)
  ·
    refine ⟨15185194666424174222946913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20246926221898898963929217 15185194666424174222946913)
    ·
      refine ⟨11388895999818130667210185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15185194666424174222946913 11388895999818130667210185)
      ·
        refine ⟨8541671999863598000407639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11388895999818130667210185 8541671999863598000407639)
        ·
          refine ⟨12812507999795397000611459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8541671999863598000407639 12812507999795397000611459)
          ·
            refine ⟨19218761999693095500917189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12812507999795397000611459 19218761999693095500917189)
            ·
              refine ⟨3603517874942455406421973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19218761999693095500917189 3603517874942455406421973)
              ·
                refine ⟨84457450193963798588015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3603517874942455406421973 84457450193963798588015)
                ·
                  rfl

theorem cell20_555121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 7].length) (baseStart_555121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555121 prefixEnd_555121 := by exact prefixLift 555121
  have htrace : WordTrace (prefixWord ++ tailWord_555121) baseStart_555121 baseEnd_555121 := by
    simpa [prefixWord, tailWord_555121, baseEnd_555121] using wordTrace_append hprefix tailTrace_555121
  have hstable : (prefixWord ++ tailWord_555121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555121).length < 2 ^ (prefixWord ++ tailWord_555121).sum := by decide
  have hdescent : baseEnd_555121 < baseStart_555121 := by decide
  rcases family_descends (prefixWord ++ tailWord_555121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555165 : List Nat := [1, 4, 2, 1, 1, 4, 3, 2, 2]
def baseStart_555165 : Nat := 118140960795 + 555165 * 2 ^ 59
def prefixEnd_555165 : Nat := 4983230072969 + 3 ^ 40 * 555165 * 2
def baseEnd_555165 : Nat := 253392433380822798297199

theorem tailTrace_555165 : CollatzResearch.WordTrace tailWord_555165 prefixEnd_555165 253392433380822798297199 := by
  unfold tailWord_555165
  simp only [CollatzResearch.WordTrace]
  refine ⟨20248531033739494478530949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13499020689159662985687299 20248531033739494478530949)
  ·
    refine ⟨3796599568826155214724553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20248531033739494478530949 3796599568826155214724553)
    ·
      refine ⟨2847449676619616411043415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3796599568826155214724553 2847449676619616411043415)
      ·
        refine ⟨4271174514929424616565123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2847449676619616411043415 4271174514929424616565123)
        ·
          refine ⟨6406761772394136924847685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4271174514929424616565123 6406761772394136924847685)
          ·
            refine ⟨1201267832323900673408941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6406761772394136924847685 1201267832323900673408941)
            ·
              refine ⟨450475437121462752528353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1201267832323900673408941 450475437121462752528353)
              ·
                refine ⟨337856577841097064396265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450475437121462752528353 337856577841097064396265)
                ·
                  refine ⟨253392433380822798297199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337856577841097064396265 253392433380822798297199)
                  ·
                    rfl

theorem cell20_555165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_555165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555165 prefixEnd_555165 := by exact prefixLift 555165
  have htrace : WordTrace (prefixWord ++ tailWord_555165) baseStart_555165 baseEnd_555165 := by
    simpa [prefixWord, tailWord_555165, baseEnd_555165] using wordTrace_append hprefix tailTrace_555165
  have hstable : (prefixWord ++ tailWord_555165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555165).length < 2 ^ (prefixWord ++ tailWord_555165).sum := by decide
  have hdescent : baseEnd_555165 < baseStart_555165 := by decide
  rcases family_descends (prefixWord ++ tailWord_555165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555169 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 4]
def baseStart_555169 : Nat := 118140960795 + 555169 * 2 ^ 59
def prefixEnd_555169 : Nat := 4983230072969 + 3 ^ 40 * 555169 * 2
def baseEnd_555169 : Nat := 253394259089816562163849

theorem tailTrace_555169 : CollatzResearch.WordTrace tailWord_555169 prefixEnd_555169 253394259089816562163849 := by
  unfold tailWord_555169
  simp only [CollatzResearch.WordTrace]
  refine ⟨20248676925725003161676561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13499117950483335441117707 20248676925725003161676561)
  ·
    refine ⟨15186507694293752371257421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20248676925725003161676561 15186507694293752371257421)
    ·
      refine ⟨5694940385360157139221533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15186507694293752371257421 5694940385360157139221533)
      ·
        refine ⟨2135602644510058927208075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5694940385360157139221533 2135602644510058927208075)
        ·
          refine ⟨3203403966765088390812113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2135602644510058927208075 3203403966765088390812113)
          ·
            refine ⟨2402552975073816293109085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3203403966765088390812113 2402552975073816293109085)
            ·
              refine ⟨900957365652681109915907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2402552975073816293109085 900957365652681109915907)
              ·
                refine ⟨1351436048479021664873861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 900957365652681109915907 1351436048479021664873861)
                ·
                  refine ⟨253394259089816562163849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1351436048479021664873861 253394259089816562163849)
                  ·
                    rfl

theorem cell20_555169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_555169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555169 prefixEnd_555169 := by exact prefixLift 555169
  have htrace : WordTrace (prefixWord ++ tailWord_555169) baseStart_555169 baseEnd_555169 := by
    simpa [prefixWord, tailWord_555169, baseEnd_555169] using wordTrace_append hprefix tailTrace_555169
  have hstable : (prefixWord ++ tailWord_555169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555169).length < 2 ^ (prefixWord ++ tailWord_555169).sum := by decide
  have hdescent : baseEnd_555169 < baseStart_555169 := by decide
  rcases family_descends (prefixWord ++ tailWord_555169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555175 : List Nat := [1, 1, 6, 2, 3, 1, 2, 1, 3]
def baseStart_555175 : Nat := 118140960795 + 555175 * 2 ^ 59
def prefixEnd_555175 : Nat := 4983230072969 + 3 ^ 40 * 555175 * 2
def baseEnd_555175 : Nat := 253396997653307207963825

theorem tailTrace_555175 : CollatzResearch.WordTrace tailWord_555175 prefixEnd_555175 253396997653307207963825 := by
  unfold tailWord_555175
  simp only [CollatzResearch.WordTrace]
  refine ⟨20248895763703266186394979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13499263842468844124263319 20248895763703266186394979)
  ·
    refine ⟨30373343645554899279592469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20248895763703266186394979 30373343645554899279592469)
    ·
      refine ⟨1423750483385385903730897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30373343645554899279592469 1423750483385385903730897)
      ·
        refine ⟨1067812862539039427798173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1423750483385385903730897 1067812862539039427798173)
        ·
          refine ⟨400429823452139785424315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1067812862539039427798173 400429823452139785424315)
          ·
            refine ⟨600644735178209678136473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400429823452139785424315 600644735178209678136473)
            ·
              refine ⟨450483551383657258602355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 600644735178209678136473 450483551383657258602355)
              ·
                refine ⟨675725327075485887903533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450483551383657258602355 675725327075485887903533)
                ·
                  refine ⟨253396997653307207963825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 675725327075485887903533 253396997653307207963825)
                  ·
                    rfl

theorem cell20_555175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 3].length) (baseStart_555175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555175 prefixEnd_555175 := by exact prefixLift 555175
  have htrace : WordTrace (prefixWord ++ tailWord_555175) baseStart_555175 baseEnd_555175 := by
    simpa [prefixWord, tailWord_555175, baseEnd_555175] using wordTrace_append hprefix tailTrace_555175
  have hstable : (prefixWord ++ tailWord_555175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555175).length < 2 ^ (prefixWord ++ tailWord_555175).sum := by decide
  have hdescent : baseEnd_555175 < baseStart_555175 := by decide
  rcases family_descends (prefixWord ++ tailWord_555175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555224 : List Nat := [2, 1, 2, 2, 4, 2, 1, 4, 2]
def baseStart_555224 : Nat := 118140960795 + 555224 * 2 ^ 59
def prefixEnd_555224 : Nat := 4983230072969 + 3 ^ 40 * 555224 * 2
def baseEnd_555224 : Nat := 253419362588480815330291

theorem tailTrace_555224 : CollatzResearch.WordTrace tailWord_555224 prefixEnd_555224 253419362588480815330291 := by
  unfold tailWord_555224
  simp only [CollatzResearch.WordTrace]
  refine ⟨10125341470262873777464363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13500455293683831703285817 10125341470262873777464363)
  ·
    refine ⟨15188012205394310666196545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10125341470262873777464363 15188012205394310666196545)
    ·
      refine ⟨11391009154045732999647409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15188012205394310666196545 11391009154045732999647409)
      ·
        refine ⟨8543256865534299749735557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11391009154045732999647409 8543256865534299749735557)
        ·
          refine ⟨1601860662287681203075417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8543256865534299749735557 1601860662287681203075417)
          ·
            refine ⟨1201395496715760902306563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1601860662287681203075417 1201395496715760902306563)
            ·
              refine ⟨1802093245073641353459845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201395496715760902306563 1802093245073641353459845)
              ·
                refine ⟨337892483451307753773721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1802093245073641353459845 337892483451307753773721)
                ·
                  refine ⟨253419362588480815330291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337892483451307753773721 253419362588480815330291)
                  ·
                    rfl

theorem cell20_555224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 2].length) (baseStart_555224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555224 prefixEnd_555224 := by exact prefixLift 555224
  have htrace : WordTrace (prefixWord ++ tailWord_555224) baseStart_555224 baseEnd_555224 := by
    simpa [prefixWord, tailWord_555224, baseEnd_555224] using wordTrace_append hprefix tailTrace_555224
  have hstable : (prefixWord ++ tailWord_555224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555224).length < 2 ^ (prefixWord ++ tailWord_555224).sum := by decide
  have hdescent : baseEnd_555224 < baseStart_555224 := by decide
  rcases family_descends (prefixWord ++ tailWord_555224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555273 : List Nat := [1, 2, 1, 1, 3, 5, 7]
def baseStart_555273 : Nat := 118140960795 + 555273 * 2 ^ 59
def prefixEnd_555273 : Nat := 4983230072969 + 3 ^ 40 * 555273 * 2
def baseEnd_555273 : Nat := 28160191947072713632973

theorem tailTrace_555273 : CollatzResearch.WordTrace tailWord_555273 prefixEnd_555273 28160191947072713632973 := by
  unfold tailWord_555273
  simp only [CollatzResearch.WordTrace]
  refine ⟨20252470117348228923462473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13501646744898819282308315 20252470117348228923462473)
  ·
    refine ⟨15189352588011171692596855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20252470117348228923462473 15189352588011171692596855)
    ·
      refine ⟨22784028882016757538895283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15189352588011171692596855 22784028882016757538895283)
      ·
        refine ⟨34176043323025136308342925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22784028882016757538895283 34176043323025136308342925)
        ·
          refine ⟨12816016246134426115628597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34176043323025136308342925 12816016246134426115628597)
          ·
            refine ⟨1201501523075102448340181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12816016246134426115628597 1201501523075102448340181)
            ·
              refine ⟨28160191947072713632973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1201501523075102448340181 28160191947072713632973)
              ·
                rfl

theorem cell20_555273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 7].length) (baseStart_555273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555273 prefixEnd_555273 := by exact prefixLift 555273
  have htrace : WordTrace (prefixWord ++ tailWord_555273) baseStart_555273 baseEnd_555273 := by
    simpa [prefixWord, tailWord_555273, baseEnd_555273] using wordTrace_append hprefix tailTrace_555273
  have hstable : (prefixWord ++ tailWord_555273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555273).length < 2 ^ (prefixWord ++ tailWord_555273).sum := by decide
  have hdescent : baseEnd_555273 < baseStart_555273 := by decide
  rcases family_descends (prefixWord ++ tailWord_555273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555297 : List Nat := [1, 2, 3, 2, 1, 1, 2, 5, 3]
def baseStart_555297 : Nat := 118140960795 + 555297 * 2 ^ 59
def prefixEnd_555297 : Nat := 4983230072969 + 3 ^ 40 * 555297 * 2
def baseEnd_555297 : Nat := 253452681777617005896659

theorem tailTrace_555297 : CollatzResearch.WordTrace tailWord_555297 prefixEnd_555297 253452681777617005896659 := by
  unfold tailWord_555297
  simp only [CollatzResearch.WordTrace]
  refine ⟨20253345469261281022336145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13502230312840854014890763 20253345469261281022336145)
  ·
    refine ⟨15190009101945960766752109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20253345469261281022336145 15190009101945960766752109)
    ·
      refine ⟨5696253413229735287532041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15190009101945960766752109 5696253413229735287532041)
      ·
        refine ⟨4272190059922301465649031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5696253413229735287532041 4272190059922301465649031)
        ·
          refine ⟨6408285089883452198473547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4272190059922301465649031 6408285089883452198473547)
          ·
            refine ⟨9612427634825178297710321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6408285089883452198473547 9612427634825178297710321)
            ·
              refine ⟨7209320726118883723282741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9612427634825178297710321 7209320726118883723282741)
              ·
                refine ⟨675873818073645349057757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7209320726118883723282741 675873818073645349057757)
                ·
                  refine ⟨253452681777617005896659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 675873818073645349057757 253452681777617005896659)
                  ·
                    rfl

theorem cell20_555297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_555297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555297 prefixEnd_555297 := by exact prefixLift 555297
  have htrace : WordTrace (prefixWord ++ tailWord_555297) baseStart_555297 baseEnd_555297 := by
    simpa [prefixWord, tailWord_555297, baseEnd_555297] using wordTrace_append hprefix tailTrace_555297
  have hstable : (prefixWord ++ tailWord_555297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555297).length < 2 ^ (prefixWord ++ tailWord_555297).sum := by decide
  have hdescent : baseEnd_555297 < baseStart_555297 := by decide
  rcases family_descends (prefixWord ++ tailWord_555297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555335 : List Nat := [1, 1, 4, 1, 2, 2, 2, 4, 3]
def baseStart_555335 : Nat := 118140960795 + 555335 * 2 ^ 59
def prefixEnd_555335 : Nat := 4983230072969 + 3 ^ 40 * 555335 * 2
def baseEnd_555335 : Nat := 253470026013057762629837

theorem tailTrace_555335 : CollatzResearch.WordTrace tailWord_555335 prefixEnd_555335 253470026013057762629837 := by
  unfold tailWord_555335
  simp only [CollatzResearch.WordTrace]
  refine ⟨20254731443123613512219459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13503154295415742341479639 20254731443123613512219459)
  ·
    refine ⟨30382097164685420268329189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20254731443123613512219459 30382097164685420268329189)
    ·
      refine ⟨5696643218378516300311723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30382097164685420268329189 5696643218378516300311723)
      ·
        refine ⟨8544964827567774450467585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5696643218378516300311723 8544964827567774450467585)
        ·
          refine ⟨6408723620675830837850689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8544964827567774450467585 6408723620675830837850689)
          ·
            refine ⟨4806542715506873128388017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6408723620675830837850689 4806542715506873128388017)
            ·
              refine ⟨3604907036630154846291013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4806542715506873128388017 3604907036630154846291013)
              ·
                refine ⟨675920069368154033679565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3604907036630154846291013 675920069368154033679565)
                ·
                  refine ⟨253470026013057762629837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 675920069368154033679565 253470026013057762629837)
                  ·
                    rfl

theorem cell20_555335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 3].length) (baseStart_555335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555335 prefixEnd_555335 := by exact prefixLift 555335
  have htrace : WordTrace (prefixWord ++ tailWord_555335) baseStart_555335 baseEnd_555335 := by
    simpa [prefixWord, tailWord_555335, baseEnd_555335] using wordTrace_append hprefix tailTrace_555335
  have hstable : (prefixWord ++ tailWord_555335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555335).length < 2 ^ (prefixWord ++ tailWord_555335).sum := by decide
  have hdescent : baseEnd_555335 < baseStart_555335 := by decide
  rcases family_descends (prefixWord ++ tailWord_555335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555342 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_555342 : Nat := 118140960795 + 555342 * 2 ^ 59
def prefixEnd_555342 : Nat := 4983230072969 + 3 ^ 40 * 555342 * 2
def baseEnd_555342 : Nat := 253473221003796849396475

theorem tailTrace_555342 : CollatzResearch.WordTrace tailWord_555342 prefixEnd_555342 253473221003796849396475 := by
  unfold tailWord_555342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2531873344262281713465535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13503324502732169138482853 2531873344262281713465535)
  ·
    refine ⟨3797810016393422570198303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2531873344262281713465535 3797810016393422570198303)
    ·
      refine ⟨5696715024590133855297455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3797810016393422570198303 5696715024590133855297455)
      ·
        refine ⟨8545072536885200782946183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5696715024590133855297455 8545072536885200782946183)
        ·
          refine ⟨12817608805327801174419275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8545072536885200782946183 12817608805327801174419275)
          ·
            refine ⟨19226413207991701761628913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12817608805327801174419275 19226413207991701761628913)
            ·
              refine ⟨14419809905993776321221685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19226413207991701761628913 14419809905993776321221685)
              ·
                refine ⟨1351857178686916530114533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14419809905993776321221685 1351857178686916530114533)
                ·
                  refine ⟨253473221003796849396475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1351857178686916530114533 253473221003796849396475)
                  ·
                    rfl

theorem cell20_555342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_555342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555342 prefixEnd_555342 := by exact prefixLift 555342
  have htrace : WordTrace (prefixWord ++ tailWord_555342) baseStart_555342 baseEnd_555342 := by
    simpa [prefixWord, tailWord_555342, baseEnd_555342] using wordTrace_append hprefix tailTrace_555342
  have hstable : (prefixWord ++ tailWord_555342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555342).length < 2 ^ (prefixWord ++ tailWord_555342).sum := by decide
  have hdescent : baseEnd_555342 < baseStart_555342 := by decide
  rcases family_descends (prefixWord ++ tailWord_555342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555393 : List Nat := [1, 2, 4, 3, 1, 1, 4, 2, 2]
def baseStart_555393 : Nat := 118140960795 + 555393 * 2 ^ 59
def prefixEnd_555393 : Nat := 4983230072969 + 3 ^ 40 * 555393 * 2
def baseEnd_555393 : Nat := 253496498793467338696267

theorem tailTrace_555393 : CollatzResearch.WordTrace tailWord_555393 prefixEnd_555393 253496498793467338696267 := by
  unfold tailWord_555393
  simp only [CollatzResearch.WordTrace]
  refine ⟨20256846876913489417830833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13504564584608992945220555 20256846876913489417830833)
  ·
    refine ⟨15192635157685117063373125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20256846876913489417830833 15192635157685117063373125)
    ·
      refine ⟨2848619092065959449382461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15192635157685117063373125 2848619092065959449382461)
      ·
        refine ⟨1068232159524734793518423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2848619092065959449382461 1068232159524734793518423)
        ·
          refine ⟨1602348239287102190277635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1068232159524734793518423 1602348239287102190277635)
          ·
            refine ⟨2403522358930653285416453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1602348239287102190277635 2403522358930653285416453)
            ·
              refine ⟨450660442299497491015585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2403522358930653285416453 450660442299497491015585)
              ·
                refine ⟨337995331724623118261689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450660442299497491015585 337995331724623118261689)
                ·
                  refine ⟨253496498793467338696267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337995331724623118261689 253496498793467338696267)
                  ·
                    rfl

theorem cell20_555393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 2].length) (baseStart_555393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555393 prefixEnd_555393 := by exact prefixLift 555393
  have htrace : WordTrace (prefixWord ++ tailWord_555393) baseStart_555393 baseEnd_555393 := by
    simpa [prefixWord, tailWord_555393, baseEnd_555393] using wordTrace_append hprefix tailTrace_555393
  have hstable : (prefixWord ++ tailWord_555393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555393).length < 2 ^ (prefixWord ++ tailWord_555393).sum := by decide
  have hdescent : baseEnd_555393 < baseStart_555393 := by decide
  rcases family_descends (prefixWord ++ tailWord_555393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555404 : List Nat := [2, 2, 1, 2, 1, 6, 1, 5]
def baseStart_555404 : Nat := 118140960795 + 555404 * 2 ^ 59
def prefixEnd_555404 : Nat := 4983230072969 + 3 ^ 40 * 555404 * 2
def baseEnd_555404 : Nat := 84500506497733396443185

theorem tailTrace_555404 : CollatzResearch.WordTrace tailWord_555404 prefixEnd_555404 84500506497733396443185 := by
  unfold tailWord_555404
  simp only [CollatzResearch.WordTrace]
  refine ⟨10128624039936819148240633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13504832053249092197654177 10128624039936819148240633)
  ·
    refine ⟨7596468029952614361180475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10128624039936819148240633 7596468029952614361180475)
    ·
      refine ⟨11394702044928921541770713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7596468029952614361180475 11394702044928921541770713)
      ·
        refine ⟨8546026533696691156328035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11394702044928921541770713 8546026533696691156328035)
        ·
          refine ⟨12819039800545036734492053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8546026533696691156328035 12819039800545036734492053)
          ·
            refine ⟨600892490650548596929315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12819039800545036734492053 600892490650548596929315)
            ·
              refine ⟨901338735975822895393973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600892490650548596929315 901338735975822895393973)
              ·
                refine ⟨84500506497733396443185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 901338735975822895393973 84500506497733396443185)
                ·
                  rfl

theorem cell20_555404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_555404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555404 prefixEnd_555404 := by exact prefixLift 555404
  have htrace : WordTrace (prefixWord ++ tailWord_555404) baseStart_555404 baseEnd_555404 := by
    simpa [prefixWord, tailWord_555404, baseEnd_555404] using wordTrace_append hprefix tailTrace_555404
  have hstable : (prefixWord ++ tailWord_555404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555404).length < 2 ^ (prefixWord ++ tailWord_555404).sum := by decide
  have hdescent : baseEnd_555404 < baseStart_555404 := by decide
  rcases family_descends (prefixWord ++ tailWord_555404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555418 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_555418 : Nat := 118140960795 + 555418 * 2 ^ 59
def prefixEnd_555418 : Nat := 4983230072969 + 3 ^ 40 * 555418 * 2
def baseEnd_555418 : Nat := 253507909474678362862831

theorem tailTrace_555418 : CollatzResearch.WordTrace tailWord_555418 prefixEnd_555418 253507909474678362862831 := by
  unfold tailWord_555418
  simp only [CollatzResearch.WordTrace]
  refine ⟨5064439675455729671872727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13505172467881945791660605 5064439675455729671872727)
  ·
    refine ⟨7596659513183594507809091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5064439675455729671872727 7596659513183594507809091)
    ·
      refine ⟨11394989269775391761713637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7596659513183594507809091 11394989269775391761713637)
      ·
        refine ⟨2136560488082885955321307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11394989269775391761713637 2136560488082885955321307)
        ·
          refine ⟨3204840732124328932981961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2136560488082885955321307 3204840732124328932981961)
          ·
            refine ⟨2403630549093246699736471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3204840732124328932981961 2403630549093246699736471)
            ·
              refine ⟨3605445823639870049604707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2403630549093246699736471 3605445823639870049604707)
              ·
                refine ⟨5408168735459805074407061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3605445823639870049604707 5408168735459805074407061)
                ·
                  refine ⟨253507909474678362862831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5408168735459805074407061 253507909474678362862831)
                  ·
                    rfl

theorem cell20_555418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_555418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555418 prefixEnd_555418 := by exact prefixLift 555418
  have htrace : WordTrace (prefixWord ++ tailWord_555418) baseStart_555418 baseEnd_555418 := by
    simpa [prefixWord, tailWord_555418, baseEnd_555418] using wordTrace_append hprefix tailTrace_555418
  have hstable : (prefixWord ++ tailWord_555418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555418).length < 2 ^ (prefixWord ++ tailWord_555418).sum := by decide
  have hdescent : baseEnd_555418 < baseStart_555418 := by decide
  rcases family_descends (prefixWord ++ tailWord_555418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555421 : List Nat := [1, 4, 2, 1, 4, 1, 3, 4]
def baseStart_555421 : Nat := 118140960795 + 555421 * 2 ^ 59
def prefixEnd_555421 : Nat := 4983230072969 + 3 ^ 40 * 555421 * 2
def baseEnd_555421 : Nat := 84503092918807895254273

theorem tailTrace_555421 : CollatzResearch.WordTrace tailWord_555421 prefixEnd_555421 84503092918807895254273 := by
  unfold tailWord_555421
  simp only [CollatzResearch.WordTrace]
  refine ⟨20257868120812050199850117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13505245413874700133233411 20257868120812050199850117)
  ·
    refine ⟨3798350272652259412471897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20257868120812050199850117 3798350272652259412471897)
    ·
      refine ⟨2848762704489194559353923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3798350272652259412471897 2848762704489194559353923)
      ·
        refine ⟨4273144056733791839030885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2848762704489194559353923 4273144056733791839030885)
        ·
          refine ⟨801214510637585969818291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4273144056733791839030885 801214510637585969818291)
          ·
            refine ⟨1201821765956378954727437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801214510637585969818291 1201821765956378954727437)
            ·
              refine ⟨450683162233642108022789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1201821765956378954727437 450683162233642108022789)
              ·
                refine ⟨84503092918807895254273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 450683162233642108022789 84503092918807895254273)
                ·
                  rfl

theorem cell20_555421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 4].length) (baseStart_555421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555421 prefixEnd_555421 := by exact prefixLift 555421
  have htrace : WordTrace (prefixWord ++ tailWord_555421) baseStart_555421 baseEnd_555421 := by
    simpa [prefixWord, tailWord_555421, baseEnd_555421] using wordTrace_append hprefix tailTrace_555421
  have hstable : (prefixWord ++ tailWord_555421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555421).length < 2 ^ (prefixWord ++ tailWord_555421).sum := by decide
  have hdescent : baseEnd_555421 < baseStart_555421 := by decide
  rcases family_descends (prefixWord ++ tailWord_555421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555445 : List Nat := [1, 3, 3, 2, 3, 2, 1, 2, 3]
def baseStart_555445 : Nat := 118140960795 + 555445 * 2 ^ 59
def prefixEnd_555445 : Nat := 4983230072969 + 3 ^ 40 * 555445 * 2
def baseEnd_555445 : Nat := 253520233010386268962721

theorem tailTrace_555445 : CollatzResearch.WordTrace tailWord_555445 prefixEnd_555445 253520233010386268962721 := by
  unfold tailWord_555445
  simp only [CollatzResearch.WordTrace]
  refine ⟨20258743472725102298723789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13505828981816734865815859 20258743472725102298723789)
  ·
    refine ⟨7597028802271913362021421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20258743472725102298723789 7597028802271913362021421)
    ·
      refine ⟨2848885800851967510758033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7597028802271913362021421 2848885800851967510758033)
      ·
        refine ⟨2136664350638975633068525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2848885800851967510758033 2136664350638975633068525)
        ·
          refine ⟨801249131489615862400697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2136664350638975633068525 801249131489615862400697)
          ·
            refine ⟨600936848617211896800523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 801249131489615862400697 600936848617211896800523)
            ·
              refine ⟨901405272925817845200785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600936848617211896800523 901405272925817845200785)
              ·
                refine ⟨676053954694363383900589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 901405272925817845200785 676053954694363383900589)
                ·
                  refine ⟨253520233010386268962721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676053954694363383900589 253520233010386268962721)
                  ·
                    rfl

theorem cell20_555445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_555445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555445 prefixEnd_555445 := by exact prefixLift 555445
  have htrace : WordTrace (prefixWord ++ tailWord_555445) baseStart_555445 baseEnd_555445 := by
    simpa [prefixWord, tailWord_555445, baseEnd_555445] using wordTrace_append hprefix tailTrace_555445
  have hstable : (prefixWord ++ tailWord_555445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555445).length < 2 ^ (prefixWord ++ tailWord_555445).sum := by decide
  have hdescent : baseEnd_555445 < baseStart_555445 := by decide
  rcases family_descends (prefixWord ++ tailWord_555445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555449 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 5]
def baseStart_555449 : Nat := 118140960795 + 555449 * 2 ^ 59
def prefixEnd_555449 : Nat := 4983230072969 + 3 ^ 40 * 555449 * 2
def baseEnd_555449 : Nat := 253522058719380032829371

theorem tailTrace_555449 : CollatzResearch.WordTrace tailWord_555449 prefixEnd_555449 253522058719380032829371 := by
  unfold tailWord_555449
  simp only [CollatzResearch.WordTrace]
  refine ⟨20258889364710610981869401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13505926243140407321246267 20258889364710610981869401)
  ·
    refine ⟨15194167023532958236402051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20258889364710610981869401 15194167023532958236402051)
    ·
      refine ⟨22791250535299437354603077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15194167023532958236402051 22791250535299437354603077)
      ·
        refine ⟨4273359475368644503988077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22791250535299437354603077 4273359475368644503988077)
        ·
          refine ⟨1602509803263241688995529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4273359475368644503988077 1602509803263241688995529)
          ·
            refine ⟨1201882352447431266746647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1602509803263241688995529 1201882352447431266746647)
            ·
              refine ⟨1802823528671146900119971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201882352447431266746647 1802823528671146900119971)
              ·
                refine ⟨2704235293006720350179957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802823528671146900119971 2704235293006720350179957)
                ·
                  refine ⟨253522058719380032829371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2704235293006720350179957 253522058719380032829371)
                  ·
                    rfl

theorem cell20_555449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_555449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555449 prefixEnd_555449 := by exact prefixLift 555449
  have htrace : WordTrace (prefixWord ++ tailWord_555449) baseStart_555449 baseEnd_555449 := by
    simpa [prefixWord, tailWord_555449, baseEnd_555449] using wordTrace_append hprefix tailTrace_555449
  have hstable : (prefixWord ++ tailWord_555449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555449).length < 2 ^ (prefixWord ++ tailWord_555449).sum := by decide
  have hdescent : baseEnd_555449 < baseStart_555449 := by decide
  rcases family_descends (prefixWord ++ tailWord_555449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555452 : List Nat := [2, 2, 2, 4, 1, 1, 2, 4, 2]
def baseStart_555452 : Nat := 118140960795 + 555452 * 2 ^ 59
def prefixEnd_555452 : Nat := 4983230072969 + 3 ^ 40 * 555452 * 2
def baseEnd_555452 : Nat := 253523428001125355729359

theorem tailTrace_555452 : CollatzResearch.WordTrace tailWord_555452 prefixEnd_555452 253523428001125355729359 := by
  unfold tailWord_555452
  simp only [CollatzResearch.WordTrace]
  refine ⟨10129499391849871247114305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13505999189133161662819073 10129499391849871247114305)
  ·
    refine ⟨7597124543887403435335729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10129499391849871247114305 7597124543887403435335729)
    ·
      refine ⟨5697843407915552576501797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7597124543887403435335729 5697843407915552576501797)
      ·
        refine ⟨1068345638984166108094087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5697843407915552576501797 1068345638984166108094087)
        ·
          refine ⟨1602518458476249162141131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1068345638984166108094087 1602518458476249162141131)
          ·
            refine ⟨2403777687714373743211697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1602518458476249162141131 2403777687714373743211697)
            ·
              refine ⟨1802833265785780307408773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2403777687714373743211697 1802833265785780307408773)
              ·
                refine ⟨338031237334833807639145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1802833265785780307408773 338031237334833807639145)
                ·
                  refine ⟨253523428001125355729359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338031237334833807639145 253523428001125355729359)
                  ·
                    rfl

theorem cell20_555452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_555452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555452 prefixEnd_555452 := by exact prefixLift 555452
  have htrace : WordTrace (prefixWord ++ tailWord_555452) baseStart_555452 baseEnd_555452 := by
    simpa [prefixWord, tailWord_555452, baseEnd_555452] using wordTrace_append hprefix tailTrace_555452
  have hstable : (prefixWord ++ tailWord_555452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555452).length < 2 ^ (prefixWord ++ tailWord_555452).sum := by decide
  have hdescent : baseEnd_555452 < baseStart_555452 := by decide
  rcases family_descends (prefixWord ++ tailWord_555452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555466 : List Nat := [3, 1, 2, 1, 2, 2, 5, 1, 3]
def baseStart_555466 : Nat := 118140960795 + 555466 * 2 ^ 59
def prefixEnd_555466 : Nat := 4983230072969 + 3 ^ 40 * 555466 * 2
def baseEnd_555466 : Nat := 253529817982603529262635

theorem tailTrace_555466 : CollatzResearch.WordTrace tailWord_555466 prefixEnd_555466 253529817982603529262635 := by
  unfold tailWord_555466
  simp only [CollatzResearch.WordTrace]
  refine ⟨5064877351412255721309563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13506339603766015256825501 5064877351412255721309563)
  ·
    refine ⟨7597316027118383581964345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5064877351412255721309563 7597316027118383581964345)
    ·
      refine ⟨5697987020338787686473259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7597316027118383581964345 5697987020338787686473259)
      ·
        refine ⟨8546980530508181529709889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5697987020338787686473259 8546980530508181529709889)
        ·
          refine ⟨6410235397881136147282417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8546980530508181529709889 6410235397881136147282417)
          ·
            refine ⟨4807676548410852110461813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6410235397881136147282417 4807676548410852110461813)
            ·
              refine ⟨450719676413517385355795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4807676548410852110461813 450719676413517385355795)
              ·
                refine ⟨676079514620276078033693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450719676413517385355795 676079514620276078033693)
                ·
                  refine ⟨253529817982603529262635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676079514620276078033693 253529817982603529262635)
                  ·
                    rfl

theorem cell20_555466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_555466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555466 prefixEnd_555466 := by exact prefixLift 555466
  have htrace : WordTrace (prefixWord ++ tailWord_555466) baseStart_555466 baseEnd_555466 := by
    simpa [prefixWord, tailWord_555466, baseEnd_555466] using wordTrace_append hprefix tailTrace_555466
  have hstable : (prefixWord ++ tailWord_555466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555466).length < 2 ^ (prefixWord ++ tailWord_555466).sum := by decide
  have hdescent : baseEnd_555466 < baseStart_555466 := by decide
  rcases family_descends (prefixWord ++ tailWord_555466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555521 : List Nat := [1, 2, 4, 1, 3, 3, 2, 1, 3]
def baseStart_555521 : Nat := 118140960795 + 555521 * 2 ^ 59
def prefixEnd_555521 : Nat := 4983230072969 + 3 ^ 40 * 555521 * 2
def baseEnd_555521 : Nat := 253554921481267782429077

theorem tailTrace_555521 : CollatzResearch.WordTrace tailWord_555521 prefixEnd_555521 253554921481267782429077 := by
  unfold tailWord_555521
  simp only [CollatzResearch.WordTrace]
  refine ⟨20261515420449767278490417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13507676946966511518993611 20261515420449767278490417)
  ·
    refine ⟨15196136565337325458867813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20261515420449767278490417 15196136565337325458867813)
    ·
      refine ⟨2849275606000748523537715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15196136565337325458867813 2849275606000748523537715)
      ·
        refine ⟨4273913409001122785306573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2849275606000748523537715 4273913409001122785306573)
        ·
          refine ⟨1602717528375421044489965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4273913409001122785306573 1602717528375421044489965)
          ·
            refine ⟨601019073140782891683737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1602717528375421044489965 601019073140782891683737)
            ·
              refine ⟨450764304855587168762803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601019073140782891683737 450764304855587168762803)
              ·
                refine ⟨676146457283380753144205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450764304855587168762803 676146457283380753144205)
                ·
                  refine ⟨253554921481267782429077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676146457283380753144205 253554921481267782429077)
                  ·
                    rfl

theorem cell20_555521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_555521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555521 prefixEnd_555521 := by exact prefixLift 555521
  have htrace : WordTrace (prefixWord ++ tailWord_555521) baseStart_555521 baseEnd_555521 := by
    simpa [prefixWord, tailWord_555521, baseEnd_555521] using wordTrace_append hprefix tailTrace_555521
  have hstable : (prefixWord ++ tailWord_555521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555521).length < 2 ^ (prefixWord ++ tailWord_555521).sum := by decide
  have hdescent : baseEnd_555521 < baseStart_555521 := by decide
  rcases family_descends (prefixWord ++ tailWord_555521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555546 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_555546 : Nat := 118140960795 + 555546 * 2 ^ 59
def prefixEnd_555546 : Nat := 4983230072969 + 3 ^ 40 * 555546 * 2
def baseEnd_555546 : Nat := 253566332162478806595641

theorem tailTrace_555546 : CollatzResearch.WordTrace tailWord_555546 prefixEnd_555546 253566332162478806595641 := by
  unfold tailWord_555546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5065606811339799137037623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13508284830239464365433661 5065606811339799137037623)
  ·
    refine ⟨7598410217009698705556435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5065606811339799137037623 7598410217009698705556435)
    ·
      refine ⟨11397615325514548058334653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7598410217009698705556435 11397615325514548058334653)
      ·
        refine ⟨4274105747067955521875495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11397615325514548058334653 4274105747067955521875495)
        ·
          refine ⟨6411158620601933282813243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4274105747067955521875495 6411158620601933282813243)
          ·
            refine ⟨9616737930902899924219865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6411158620601933282813243 9616737930902899924219865)
            ·
              refine ⟨7212553448177174943164899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9616737930902899924219865 7212553448177174943164899)
              ·
                refine ⟨10818830172265762414747349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7212553448177174943164899 10818830172265762414747349)
                ·
                  refine ⟨253566332162478806595641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10818830172265762414747349 253566332162478806595641)
                  ·
                    rfl

theorem cell20_555546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_555546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555546 prefixEnd_555546 := by exact prefixLift 555546
  have htrace : WordTrace (prefixWord ++ tailWord_555546) baseStart_555546 baseEnd_555546 := by
    simpa [prefixWord, tailWord_555546, baseEnd_555546] using wordTrace_append hprefix tailTrace_555546
  have hstable : (prefixWord ++ tailWord_555546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555546).length < 2 ^ (prefixWord ++ tailWord_555546).sum := by decide
  have hdescent : baseEnd_555546 < baseStart_555546 := by decide
  rcases family_descends (prefixWord ++ tailWord_555546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555556 : List Nat := [2, 3, 1, 5, 1, 8]
def baseStart_555556 : Nat := 118140960795 + 555556 * 2 ^ 59
def prefixEnd_555556 : Nat := 4983230072969 + 3 ^ 40 * 555556 * 2
def baseEnd_555556 : Nat := 9391514682776415417121

theorem tailTrace_555556 : CollatzResearch.WordTrace tailWord_555556 prefixEnd_555556 9391514682776415417121 := by
  unfold tailWord_555556
  simp only [CollatzResearch.WordTrace]
  refine ⟨10131395987661484128007261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13508527983548645504009681 10131395987661484128007261)
  ·
    refine ⟨3799273495373056548002723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10131395987661484128007261 3799273495373056548002723)
    ·
      refine ⟨5698910243059584822004085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3799273495373056548002723 5698910243059584822004085)
      ·
        refine ⟨534272835286836077062883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5698910243059584822004085 534272835286836077062883)
        ·
          refine ⟨801409252930254115594325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534272835286836077062883 801409252930254115594325)
          ·
            refine ⟨9391514682776415417121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 801409252930254115594325 9391514682776415417121)
            ·
              rfl

theorem cell20_555556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 8].length) (baseStart_555556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555556 prefixEnd_555556 := by exact prefixLift 555556
  have htrace : WordTrace (prefixWord ++ tailWord_555556) baseStart_555556 baseEnd_555556 := by
    simpa [prefixWord, tailWord_555556, baseEnd_555556] using wordTrace_append hprefix tailTrace_555556
  have hstable : (prefixWord ++ tailWord_555556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555556).length < 2 ^ (prefixWord ++ tailWord_555556).sum := by decide
  have hdescent : baseEnd_555556 < baseStart_555556 := by decide
  rcases family_descends (prefixWord ++ tailWord_555556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555590 : List Nat := [6, 1, 1, 1, 2, 2, 3, 4]
def baseStart_555590 : Nat := 118140960795 + 555590 * 2 ^ 59
def prefixEnd_555590 : Nat := 4983230072969 + 3 ^ 40 * 555590 * 2
def baseEnd_555590 : Nat := 84528804987136736376265

theorem tailTrace_555590 : CollatzResearch.WordTrace tailWord_555590 prefixEnd_555590 84528804987136736376265 := by
  unfold tailWord_555590
  simp only [CollatzResearch.WordTrace]
  refine ⟨633251001787493501961007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13509354704799861375168149 633251001787493501961007)
  ·
    refine ⟨949876502681240252941511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 633251001787493501961007 949876502681240252941511)
    ·
      refine ⟨1424814754021860379412267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 949876502681240252941511 1424814754021860379412267)
      ·
        refine ⟨2137222131032790569118401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1424814754021860379412267 2137222131032790569118401)
        ·
          refine ⟨1602916598274592926838801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2137222131032790569118401 1602916598274592926838801)
          ·
            refine ⟨1202187448705944695129101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1602916598274592926838801 1202187448705944695129101)
            ·
              refine ⟨450820293264729260673413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1202187448705944695129101 450820293264729260673413)
              ·
                refine ⟨84528804987136736376265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 450820293264729260673413 84528804987136736376265)
                ·
                  rfl

theorem cell20_555590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_555590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555590 prefixEnd_555590 := by exact prefixLift 555590
  have htrace : WordTrace (prefixWord ++ tailWord_555590) baseStart_555590 baseEnd_555590 := by
    simpa [prefixWord, tailWord_555590, baseEnd_555590] using wordTrace_append hprefix tailTrace_555590
  have hstable : (prefixWord ++ tailWord_555590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555590).length < 2 ^ (prefixWord ++ tailWord_555590).sum := by decide
  have hdescent : baseEnd_555590 < baseStart_555590 := by decide
  rcases family_descends (prefixWord ++ tailWord_555590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555594 : List Nat := [3, 1, 2, 1, 1, 5, 3, 4]
def baseStart_555594 : Nat := 118140960795 + 555594 * 2 ^ 59
def prefixEnd_555594 : Nat := 4983230072969 + 3 ^ 40 * 555594 * 2
def baseEnd_555594 : Nat := 84529413556801324331815

theorem tailTrace_555594 : CollatzResearch.WordTrace tailWord_555594 prefixEnd_555594 84529413556801324331815 := by
  unfold tailWord_555594
  simp only [CollatzResearch.WordTrace]
  refine ⟨5066044487296325186474459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13509451966123533830598557 5066044487296325186474459)
  ·
    refine ⟨7599066730944487779711689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5066044487296325186474459 7599066730944487779711689)
    ·
      refine ⟨5699300048208365834783767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7599066730944487779711689 5699300048208365834783767)
      ·
        refine ⟨8548950072312548752175651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5699300048208365834783767 8548950072312548752175651)
        ·
          refine ⟨12823425108468823128263477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8548950072312548752175651 12823425108468823128263477)
          ·
            refine ⟨1202196103918952168274701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12823425108468823128263477 1202196103918952168274701)
            ·
              refine ⟨450823538969607063103013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1202196103918952168274701 450823538969607063103013)
              ·
                refine ⟨84529413556801324331815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 450823538969607063103013 84529413556801324331815)
                ·
                  rfl

theorem cell20_555594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_555594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555594 prefixEnd_555594 := by exact prefixLift 555594
  have htrace : WordTrace (prefixWord ++ tailWord_555594) baseStart_555594 baseEnd_555594 := by
    simpa [prefixWord, tailWord_555594, baseEnd_555594] using wordTrace_append hprefix tailTrace_555594
  have hstable : (prefixWord ++ tailWord_555594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555594).length < 2 ^ (prefixWord ++ tailWord_555594).sum := by decide
  have hdescent : baseEnd_555594 < baseStart_555594 := by decide
  rcases family_descends (prefixWord ++ tailWord_555594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555604 : List Nat := [2, 4, 1, 1, 1, 4, 2, 3, 2]
def baseStart_555604 : Nat := 118140960795 + 555604 * 2 ^ 59
def prefixEnd_555604 : Nat := 4983230072969 + 3 ^ 40 * 555604 * 2
def baseEnd_555604 : Nat := 253592804942888382662071

theorem tailTrace_555604 : CollatzResearch.WordTrace tailWord_555604 prefixEnd_555604 253592804942888382662071 := by
  unfold tailWord_555604
  simp only [CollatzResearch.WordTrace]
  refine ⟨10132271339574536226880933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13509695119432714969174577 10132271339574536226880933)
  ·
    refine ⟨1899800876170225542540175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10132271339574536226880933 1899800876170225542540175)
    ·
      refine ⟨2849701314255338313810263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1899800876170225542540175 2849701314255338313810263)
      ·
        refine ⟨4274551971383007470715395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2849701314255338313810263 4274551971383007470715395)
        ·
          refine ⟨6411827957074511206073093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4274551971383007470715395 6411827957074511206073093)
          ·
            refine ⟨1202217741951470851138705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6411827957074511206073093 1202217741951470851138705)
            ·
              refine ⟨901663306463603138354029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1202217741951470851138705 901663306463603138354029)
              ·
                refine ⟨338123739923851176882761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 901663306463603138354029 338123739923851176882761)
                ·
                  refine ⟨253592804942888382662071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338123739923851176882761 253592804942888382662071)
                  ·
                    rfl

theorem cell20_555604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_555604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555604 prefixEnd_555604 := by exact prefixLift 555604
  have htrace : WordTrace (prefixWord ++ tailWord_555604) baseStart_555604 baseEnd_555604 := by
    simpa [prefixWord, tailWord_555604, baseEnd_555604] using wordTrace_append hprefix tailTrace_555604
  have hstable : (prefixWord ++ tailWord_555604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555604).length < 2 ^ (prefixWord ++ tailWord_555604).sum := by decide
  have hdescent : baseEnd_555604 < baseStart_555604 := by decide
  rcases family_descends (prefixWord ++ tailWord_555604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555614 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_555614 : Nat := 118140960795 + 555614 * 2 ^ 59
def prefixEnd_555614 : Nat := 4983230072969 + 3 ^ 40 * 555614 * 2
def baseEnd_555614 : Nat := 253597369215372792328697

theorem tailTrace_555614 : CollatzResearch.WordTrace tailWord_555614 prefixEnd_555614 253597369215372792328697 := by
  unfold tailWord_555614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2533113426139105520203237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13509938272741896107750597 2533113426139105520203237)
  ·
    refine ⟨474958767401082285038107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2533113426139105520203237 474958767401082285038107)
    ·
      refine ⟨712438151101623427557161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 474958767401082285038107 712438151101623427557161)
      ·
        refine ⟨534328613326217570667871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 712438151101623427557161 534328613326217570667871)
        ·
          refine ⟨801492919989326356001807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534328613326217570667871 801492919989326356001807)
          ·
            refine ⟨1202239379983989534002711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801492919989326356001807 1202239379983989534002711)
            ·
              refine ⟨1803359069975984301004067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202239379983989534002711 1803359069975984301004067)
              ·
                refine ⟨2705038604963976451506101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803359069975984301004067 2705038604963976451506101)
                ·
                  refine ⟨253597369215372792328697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2705038604963976451506101 253597369215372792328697)
                  ·
                    rfl

theorem cell20_555614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_555614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555614 prefixEnd_555614 := by exact prefixLift 555614
  have htrace : WordTrace (prefixWord ++ tailWord_555614) baseStart_555614 baseEnd_555614 := by
    simpa [prefixWord, tailWord_555614, baseEnd_555614] using wordTrace_append hprefix tailTrace_555614
  have hstable : (prefixWord ++ tailWord_555614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555614).length < 2 ^ (prefixWord ++ tailWord_555614).sum := by decide
  have hdescent : baseEnd_555614 < baseStart_555614 := by decide
  rcases family_descends (prefixWord ++ tailWord_555614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555653 : List Nat := [1, 3, 1, 1, 4, 3, 1, 6]
def baseStart_555653 : Nat := 118140960795 + 555653 * 2 ^ 59
def prefixEnd_555653 : Nat := 4983230072969 + 3 ^ 40 * 555653 * 2
def baseEnd_555653 : Nat := 84538389959353996676179

theorem tailTrace_555653 : CollatzResearch.WordTrace tailWord_555653 prefixEnd_555653 84538389959353996676179 := by
  unfold tailWord_555653
  simp only [CollatzResearch.WordTrace]
  refine ⟨20266329855971553822295613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13510886570647702548197075 20266329855971553822295613)
  ·
    refine ⟨7599873695989332683360855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20266329855971553822295613 7599873695989332683360855)
    ·
      refine ⟨11399810543983999025041283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7599873695989332683360855 11399810543983999025041283)
      ·
        refine ⟨17099715815975998537561925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11399810543983999025041283 17099715815975998537561925)
        ·
          refine ⟨3206196715495499725792861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17099715815975998537561925 3206196715495499725792861)
          ·
            refine ⟨1202323768310812397172323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3206196715495499725792861 1202323768310812397172323)
            ·
              refine ⟨1803485652466218595758485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202323768310812397172323 1803485652466218595758485)
              ·
                refine ⟨84538389959353996676179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1803485652466218595758485 84538389959353996676179)
                ·
                  rfl

theorem cell20_555653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 6].length) (baseStart_555653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555653 prefixEnd_555653 := by exact prefixLift 555653
  have htrace : WordTrace (prefixWord ++ tailWord_555653) baseStart_555653 baseEnd_555653 := by
    simpa [prefixWord, tailWord_555653, baseEnd_555653] using wordTrace_append hprefix tailTrace_555653
  have hstable : (prefixWord ++ tailWord_555653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555653).length < 2 ^ (prefixWord ++ tailWord_555653).sum := by decide
  have hdescent : baseEnd_555653 < baseStart_555653 := by decide
  rcases family_descends (prefixWord ++ tailWord_555653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555680 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 4]
def baseStart_555680 : Nat := 118140960795 + 555680 * 2 ^ 59
def prefixEnd_555680 : Nat := 4983230072969 + 3 ^ 40 * 555680 * 2
def baseEnd_555680 : Nat := 253627493413769896128427

theorem tailTrace_555680 : CollatzResearch.WordTrace tailWord_555680 prefixEnd_555680 253627493413769896128427 := by
  unfold tailWord_555680
  simp only [CollatzResearch.WordTrace]
  refine ⟨10133657313436868716764247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13511543084582491622352329 10133657313436868716764247)
  ·
    refine ⟨15200485970155303075146371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10133657313436868716764247 15200485970155303075146371)
    ·
      refine ⟨22800728955232954612719557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15200485970155303075146371 22800728955232954612719557)
      ·
        refine ⟨4275136679106178989884917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22800728955232954612719557 4275136679106178989884917)
        ·
          refine ⟨400794063666204280301711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4275136679106178989884917 400794063666204280301711)
          ·
            refine ⟨601191095499306420452567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400794063666204280301711 601191095499306420452567)
            ·
              refine ⟨901786643248959630678851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601191095499306420452567 901786643248959630678851)
              ·
                refine ⟨1352679964873439446018277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 901786643248959630678851 1352679964873439446018277)
                ·
                  refine ⟨253627493413769896128427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1352679964873439446018277 253627493413769896128427)
                  ·
                    rfl

theorem cell20_555680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 4].length) (baseStart_555680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555680 prefixEnd_555680 := by exact prefixLift 555680
  have htrace : WordTrace (prefixWord ++ tailWord_555680) baseStart_555680 baseEnd_555680 := by
    simpa [prefixWord, tailWord_555680, baseEnd_555680] using wordTrace_append hprefix tailTrace_555680
  have hstable : (prefixWord ++ tailWord_555680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555680).length < 2 ^ (prefixWord ++ tailWord_555680).sum := by decide
  have hdescent : baseEnd_555680 < baseStart_555680 := by decide
  rcases family_descends (prefixWord ++ tailWord_555680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555687 : List Nat := [1, 1, 6, 3, 1, 1, 2, 5]
def baseStart_555687 : Nat := 118140960795 + 555687 * 2 ^ 59
def prefixEnd_555687 : Nat := 4983230072969 + 3 ^ 40 * 555687 * 2
def baseEnd_555687 : Nat := 84543562801502994298355

theorem tailTrace_555687 : CollatzResearch.WordTrace tailWord_555687 prefixEnd_555687 84543562801502994298355 := by
  unfold tailWord_555687
  simp only [CollatzResearch.WordTrace]
  refine ⟨20267569937848377629033315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13511713291898918419355543 20267569937848377629033315)
  ·
    refine ⟨30401354906772566443549973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20267569937848377629033315 30401354906772566443549973)
    ·
      refine ⟨1425063511254964052041405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30401354906772566443549973 1425063511254964052041405)
      ·
        refine ⟨534398816720611519515527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1425063511254964052041405 534398816720611519515527)
        ·
          refine ⟨801598225080917279273291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534398816720611519515527 801598225080917279273291)
          ·
            refine ⟨1202397337621375918909937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801598225080917279273291 1202397337621375918909937)
            ·
              refine ⟨901798003216031939182453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1202397337621375918909937 901798003216031939182453)
              ·
                refine ⟨84543562801502994298355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 901798003216031939182453 84543562801502994298355)
                ·
                  rfl

theorem cell20_555687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 5].length) (baseStart_555687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555687 prefixEnd_555687 := by exact prefixLift 555687
  have htrace : WordTrace (prefixWord ++ tailWord_555687) baseStart_555687 baseEnd_555687 := by
    simpa [prefixWord, tailWord_555687, baseEnd_555687] using wordTrace_append hprefix tailTrace_555687
  have hstable : (prefixWord ++ tailWord_555687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555687).length < 2 ^ (prefixWord ++ tailWord_555687).sum := by decide
  have hdescent : baseEnd_555687 < baseStart_555687 := by decide
  rcases family_descends (prefixWord ++ tailWord_555687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555705 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 6]
def baseStart_555705 : Nat := 118140960795 + 555705 * 2 ^ 59
def prefixEnd_555705 : Nat := 4983230072969 + 3 ^ 40 * 555705 * 2
def baseEnd_555705 : Nat := 253638904094980920294991

theorem tailTrace_555705 : CollatzResearch.WordTrace tailWord_555705 prefixEnd_555705 253638904094980920294991 := by
  unfold tailWord_555705
  simp only [CollatzResearch.WordTrace]
  refine ⟨20268226451783166703188569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13512150967855444468792379 20268226451783166703188569)
  ·
    refine ⟨15201169838837375027391427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20268226451783166703188569 15201169838837375027391427)
    ·
      refine ⟨22801754758256062541087141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15201169838837375027391427 22801754758256062541087141)
      ·
        refine ⟨4275329017173011726453839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22801754758256062541087141 4275329017173011726453839)
        ·
          refine ⟨6412993525759517589680759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4275329017173011726453839 6412993525759517589680759)
          ·
            refine ⟨9619490288639276384521139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6412993525759517589680759 9619490288639276384521139)
            ·
              refine ⟨14429235432958914576781709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9619490288639276384521139 14429235432958914576781709)
              ·
                refine ⟨5410963287359592966293141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14429235432958914576781709 5410963287359592966293141)
                ·
                  refine ⟨253638904094980920294991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5410963287359592966293141 253638904094980920294991)
                  ·
                    rfl

theorem cell20_555705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_555705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555705 prefixEnd_555705 := by exact prefixLift 555705
  have htrace : WordTrace (prefixWord ++ tailWord_555705) baseStart_555705 baseEnd_555705 := by
    simpa [prefixWord, tailWord_555705, baseEnd_555705] using wordTrace_append hprefix tailTrace_555705
  have hstable : (prefixWord ++ tailWord_555705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555705).length < 2 ^ (prefixWord ++ tailWord_555705).sum := by decide
  have hdescent : baseEnd_555705 < baseStart_555705 := by decide
  rcases family_descends (prefixWord ++ tailWord_555705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555725 : List Nat := [1, 6, 2, 1, 3, 7]
def baseStart_555725 : Nat := 118140960795 + 555725 * 2 ^ 59
def prefixEnd_555725 : Nat := 4983230072969 + 3 ^ 40 * 555725 * 2
def baseEnd_555725 : Nat := 9394371579257397764009

theorem tailTrace_555725 : CollatzResearch.WordTrace tailWord_555725 prefixEnd_555725 9394371579257397764009 := by
  unfold tailWord_555725
  simp only [CollatzResearch.WordTrace]
  refine ⟨20268955911710710118916629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13512637274473806745944419 20268955911710710118916629)
  ·
    refine ⟨950107308361439536824217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20268955911710710118916629 950107308361439536824217)
    ·
      refine ⟨712580481271079652618163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 950107308361439536824217 712580481271079652618163)
      ·
        refine ⟨1068870721906619478927245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712580481271079652618163 1068870721906619478927245)
        ·
          refine ⟨400826520714982304597717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1068870721906619478927245 400826520714982304597717)
          ·
            refine ⟨9394371579257397764009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 400826520714982304597717 9394371579257397764009)
            ·
              rfl

theorem cell20_555725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 7].length) (baseStart_555725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555725 prefixEnd_555725 := by exact prefixLift 555725
  have htrace : WordTrace (prefixWord ++ tailWord_555725) baseStart_555725 baseEnd_555725 := by
    simpa [prefixWord, tailWord_555725, baseEnd_555725] using wordTrace_append hprefix tailTrace_555725
  have hstable : (prefixWord ++ tailWord_555725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555725).length < 2 ^ (prefixWord ++ tailWord_555725).sum := by decide
  have hdescent : baseEnd_555725 < baseStart_555725 := by decide
  rcases family_descends (prefixWord ++ tailWord_555725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555794 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 4]
def baseStart_555794 : Nat := 118140960795 + 555794 * 2 ^ 59
def prefixEnd_555794 : Nat := 4983230072969 + 3 ^ 40 * 555794 * 2
def baseEnd_555794 : Nat := 253679526120092166327961

theorem tailTrace_555794 : CollatzResearch.WordTrace tailWord_555794 prefixEnd_555794 253679526120092166327961 := by
  unfold tailWord_555794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5067868137115183725794609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13514315032307156602118957 5067868137115183725794609)
  ·
    refine ⟨3800901102836387794345957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5067868137115183725794609 3800901102836387794345957)
    ·
      refine ⟨712668956781822711439867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3800901102836387794345957 712668956781822711439867)
      ·
        refine ⟨1069003435172734067159801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712668956781822711439867 1069003435172734067159801)
        ·
          refine ⟨801752576379550550369851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1069003435172734067159801 801752576379550550369851)
          ·
            refine ⟨1202628864569325825554777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801752576379550550369851 1202628864569325825554777)
            ·
              refine ⟨901971648426994369166083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1202628864569325825554777 901971648426994369166083)
              ·
                refine ⟨1352957472640491553749125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 901971648426994369166083 1352957472640491553749125)
                ·
                  refine ⟨253679526120092166327961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1352957472640491553749125 253679526120092166327961)
                  ·
                    rfl

theorem cell20_555794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_555794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555794 prefixEnd_555794 := by exact prefixLift 555794
  have htrace : WordTrace (prefixWord ++ tailWord_555794) baseStart_555794 baseEnd_555794 := by
    simpa [prefixWord, tailWord_555794, baseEnd_555794] using wordTrace_append hprefix tailTrace_555794
  have hstable : (prefixWord ++ tailWord_555794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555794).length < 2 ^ (prefixWord ++ tailWord_555794).sum := by decide
  have hdescent : baseEnd_555794 < baseStart_555794 := by decide
  rcases family_descends (prefixWord ++ tailWord_555794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555808 : List Nat := [2, 1, 1, 5, 1, 3, 3, 1, 3]
def baseStart_555808 : Nat := 118140960795 + 555808 * 2 ^ 59
def prefixEnd_555808 : Nat := 4983230072969 + 3 ^ 40 * 555808 * 2
def baseEnd_555808 : Nat := 253685916101570339861237

theorem tailTrace_555808 : CollatzResearch.WordTrace tailWord_555808 prefixEnd_555808 253685916101570339861237 := by
  unfold tailWord_555808
  simp only [CollatzResearch.WordTrace]
  refine ⟨10135991585205007647094039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13514655446940010196125385 10135991585205007647094039)
  ·
    refine ⟨15203987377807511470641059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10135991585205007647094039 15203987377807511470641059)
    ·
      refine ⟨22805981066711267205961589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15203987377807511470641059 22805981066711267205961589)
      ·
        refine ⟨2138060725004181300558899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22805981066711267205961589 2138060725004181300558899)
        ·
          refine ⟨3207091087506271950838349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2138060725004181300558899 3207091087506271950838349)
          ·
            refine ⟨1202659157814851981564381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3207091087506271950838349 1202659157814851981564381)
            ·
              refine ⟨450997184180569493086643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1202659157814851981564381 450997184180569493086643)
              ·
                refine ⟨676495776270854239629965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450997184180569493086643 676495776270854239629965)
                ·
                  refine ⟨253685916101570339861237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676495776270854239629965 253685916101570339861237)
                  ·
                    rfl

theorem cell20_555808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_555808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555808 prefixEnd_555808 := by exact prefixLift 555808
  have htrace : WordTrace (prefixWord ++ tailWord_555808) baseStart_555808 baseEnd_555808 := by
    simpa [prefixWord, tailWord_555808, baseEnd_555808] using wordTrace_append hprefix tailTrace_555808
  have hstable : (prefixWord ++ tailWord_555808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555808).length < 2 ^ (prefixWord ++ tailWord_555808).sum := by decide
  have hdescent : baseEnd_555808 < baseStart_555808 := by decide
  rcases family_descends (prefixWord ++ tailWord_555808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555818 : List Nat := [3, 1, 4, 3, 1, 2, 2, 4]
def baseStart_555818 : Nat := 118140960795 + 555818 * 2 ^ 59
def prefixEnd_555818 : Nat := 4983230072969 + 3 ^ 40 * 555818 * 2
def baseEnd_555818 : Nat := 84563493458018249842621

theorem tailTrace_555818 : CollatzResearch.WordTrace tailWord_555818 prefixEnd_555818 84563493458018249842621 := by
  unfold tailWord_555818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5068086975093446750513027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13514898600249191334701405 5068086975093446750513027)
  ·
    refine ⟨7602130462640170125769541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5068086975093446750513027 7602130462640170125769541)
    ·
      refine ⟨1425399461745031898581789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7602130462640170125769541 1425399461745031898581789)
      ·
        refine ⟨534524798154386961968171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1425399461745031898581789 534524798154386961968171)
        ·
          refine ⟨801787197231580442952257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534524798154386961968171 801787197231580442952257)
          ·
            refine ⟨601340397923685332214193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 801787197231580442952257 601340397923685332214193)
            ·
              refine ⟨451005298442763999160645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601340397923685332214193 451005298442763999160645)
              ·
                refine ⟨84563493458018249842621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 451005298442763999160645 84563493458018249842621)
                ·
                  rfl

theorem cell20_555818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_555818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555818 prefixEnd_555818 := by exact prefixLift 555818
  have htrace : WordTrace (prefixWord ++ tailWord_555818) baseStart_555818 baseEnd_555818 := by
    simpa [prefixWord, tailWord_555818, baseEnd_555818] using wordTrace_append hprefix tailTrace_555818
  have hstable : (prefixWord ++ tailWord_555818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555818).length < 2 ^ (prefixWord ++ tailWord_555818).sum := by decide
  have hdescent : baseEnd_555818 < baseStart_555818 := by decide
  rcases family_descends (prefixWord ++ tailWord_555818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555822 : List Nat := [4, 1, 3, 2, 1, 2, 1, 6]
def baseStart_555822 : Nat := 118140960795 + 555822 * 2 ^ 59
def prefixEnd_555822 : Nat := 4983230072969 + 3 ^ 40 * 555822 * 2
def baseEnd_555822 : Nat := 84564102027682837798171

theorem tailTrace_555822 : CollatzResearch.WordTrace tailWord_555822 prefixEnd_555822 84564102027682837798171 := by
  unfold tailWord_555822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2534061724044911960649715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13514995861572863790131813 2534061724044911960649715)
  ·
    refine ⟨3801092586067367940974573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2534061724044911960649715 3801092586067367940974573)
    ·
      refine ⟨1425409719775262977865465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3801092586067367940974573 1425409719775262977865465)
      ·
        refine ⟨1069057289831447233399099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1425409719775262977865465 1069057289831447233399099)
        ·
          refine ⟨1603585934747170850098649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1069057289831447233399099 1603585934747170850098649)
          ·
            refine ⟨1202689451060378137573987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1603585934747170850098649 1202689451060378137573987)
            ·
              refine ⟨1804034176590567206360981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202689451060378137573987 1804034176590567206360981)
              ·
                refine ⟨84564102027682837798171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1804034176590567206360981 84564102027682837798171)
                ·
                  rfl

theorem cell20_555822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_555822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555822 prefixEnd_555822 := by exact prefixLift 555822
  have htrace : WordTrace (prefixWord ++ tailWord_555822) baseStart_555822 baseEnd_555822 := by
    simpa [prefixWord, tailWord_555822, baseEnd_555822] using wordTrace_append hprefix tailTrace_555822
  have hstable : (prefixWord ++ tailWord_555822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555822).length < 2 ^ (prefixWord ++ tailWord_555822).sum := by decide
  have hdescent : baseEnd_555822 < baseStart_555822 := by decide
  rcases family_descends (prefixWord ++ tailWord_555822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555828 : List Nat := [2, 5, 1, 1, 4, 1, 1, 3, 2]
def baseStart_555828 : Nat := 118140960795 + 555828 * 2 ^ 59
def prefixEnd_555828 : Nat := 4983230072969 + 3 ^ 40 * 555828 * 2
def baseEnd_555828 : Nat := 253695044646539159194489

theorem tailTrace_555828 : CollatzResearch.WordTrace tailWord_555828 prefixEnd_555828 253695044646539159194489 := by
  unfold tailWord_555828
  simp only [CollatzResearch.WordTrace]
  refine ⟨10136356315168779354958069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13515141753558372473277425 10136356315168779354958069)
  ·
    refine ⟨950283404547073064527319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10136356315168779354958069 950283404547073064527319)
    ·
      refine ⟨1425425106820609596790979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 950283404547073064527319 1425425106820609596790979)
      ·
        refine ⟨2138137660230914395186469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1425425106820609596790979 2138137660230914395186469)
        ·
          refine ⟨400900811293296449097463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2138137660230914395186469 400900811293296449097463)
          ·
            refine ⟨601351216939944673646195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400900811293296449097463 601351216939944673646195)
            ·
              refine ⟨902026825409917010469293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601351216939944673646195 902026825409917010469293)
              ·
                refine ⟨338260059528718878925985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 902026825409917010469293 338260059528718878925985)
                ·
                  refine ⟨253695044646539159194489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338260059528718878925985 253695044646539159194489)
                  ·
                    rfl

theorem cell20_555828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_555828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555828 prefixEnd_555828 := by exact prefixLift 555828
  have htrace : WordTrace (prefixWord ++ tailWord_555828) baseStart_555828 baseEnd_555828 := by
    simpa [prefixWord, tailWord_555828, baseEnd_555828] using wordTrace_append hprefix tailTrace_555828
  have hstable : (prefixWord ++ tailWord_555828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555828).length < 2 ^ (prefixWord ++ tailWord_555828).sum := by decide
  have hdescent : baseEnd_555828 < baseStart_555828 := by decide
  rcases family_descends (prefixWord ++ tailWord_555828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555860 : List Nat := [2, 4, 1, 1, 4, 1, 2, 5]
def baseStart_555860 : Nat := 118140960795 + 555860 * 2 ^ 59
def prefixEnd_555860 : Nat := 4983230072969 + 3 ^ 40 * 555860 * 2
def baseEnd_555860 : Nat := 84569883439496423375897

theorem tailTrace_555860 : CollatzResearch.WordTrace tailWord_555860 prefixEnd_555860 84569883439496423375897 := by
  unfold tailWord_555860
  simp only [CollatzResearch.WordTrace]
  refine ⟨10136939883110814087540517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13515919844147752116720689 10136939883110814087540517)
  ·
    refine ⟨1900676228083277641413847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10136939883110814087540517 1900676228083277641413847)
    ·
      refine ⟨2851014342124916462120771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1900676228083277641413847 2851014342124916462120771)
      ·
        refine ⟨4276521513187374693181157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2851014342124916462120771 4276521513187374693181157)
        ·
          refine ⟨801847783722632754971467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4276521513187374693181157 801847783722632754971467)
          ·
            refine ⟨1202771675583949132457201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801847783722632754971467 1202771675583949132457201)
            ·
              refine ⟨902078756687961849342901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1202771675583949132457201 902078756687961849342901)
              ·
                refine ⟨84569883439496423375897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 902078756687961849342901 84569883439496423375897)
                ·
                  rfl

theorem cell20_555860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_555860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555860 prefixEnd_555860 := by exact prefixLift 555860
  have htrace : WordTrace (prefixWord ++ tailWord_555860) baseStart_555860 baseEnd_555860 := by
    simpa [prefixWord, tailWord_555860, baseEnd_555860] using wordTrace_append hprefix tailTrace_555860
  have hstable : (prefixWord ++ tailWord_555860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555860).length < 2 ^ (prefixWord ++ tailWord_555860).sum := by decide
  have hdescent : baseEnd_555860 < baseStart_555860 := by decide
  rcases family_descends (prefixWord ++ tailWord_555860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555947 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 7]
def baseStart_555947 : Nat := 118140960795 + 555947 * 2 ^ 59
def prefixEnd_555947 : Nat := 4983230072969 + 3 ^ 40 * 555947 * 2
def baseEnd_555947 : Nat := 253749359489103634227335

theorem tailTrace_555947 : CollatzResearch.WordTrace tailWord_555947 prefixEnd_555947 253749359489103634227335 := by
  unfold tailWord_555947
  simp only [CollatzResearch.WordTrace]
  refine ⟨20277052916906442033498095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13518035277937628022332063 20277052916906442033498095)
  ·
    refine ⟨30415579375359663050247143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20277052916906442033498095 30415579375359663050247143)
    ·
      refine ⟨45623369063039494575370715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30415579375359663050247143 45623369063039494575370715)
      ·
        refine ⟨68435053594559241863056073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45623369063039494575370715 68435053594559241863056073)
        ·
          refine ⟨51326290195919431397292055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68435053594559241863056073 51326290195919431397292055)
          ·
            refine ⟨76989435293879147095938083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51326290195919431397292055 76989435293879147095938083)
            ·
              refine ⟨115484152940818720643907125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76989435293879147095938083 115484152940818720643907125)
              ·
                refine ⟨10826639338201755060366293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115484152940818720643907125 10826639338201755060366293)
                ·
                  refine ⟨253749359489103634227335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10826639338201755060366293 253749359489103634227335)
                  ·
                    rfl

theorem cell20_555947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_555947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555947 prefixEnd_555947 := by exact prefixLift 555947
  have htrace : WordTrace (prefixWord ++ tailWord_555947) baseStart_555947 baseEnd_555947 := by
    simpa [prefixWord, tailWord_555947, baseEnd_555947] using wordTrace_append hprefix tailTrace_555947
  have hstable : (prefixWord ++ tailWord_555947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555947).length < 2 ^ (prefixWord ++ tailWord_555947).sum := by decide
  have hdescent : baseEnd_555947 < baseStart_555947 := by decide
  rcases family_descends (prefixWord ++ tailWord_555947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555978 : List Nat := [3, 1, 2, 1, 2, 1, 1, 9]
def baseStart_555978 : Nat := 118140960795 + 555978 * 2 ^ 59
def prefixEnd_555978 : Nat := 4983230072969 + 3 ^ 40 * 555978 * 2
def baseEnd_555978 : Nat := 84587836244601768064625

theorem tailTrace_555978 : CollatzResearch.WordTrace tailWord_555978 prefixEnd_555978 84587836244601768064625 := by
  unfold tailWord_555978
  simp only [CollatzResearch.WordTrace]
  refine ⟨5069545894948533581969147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13518789053196089551917725 5069545894948533581969147)
  ·
    refine ⟨7604318842422800372953721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5069545894948533581969147 7604318842422800372953721)
    ·
      refine ⟨5703239131817100279715291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7604318842422800372953721 5703239131817100279715291)
      ·
        refine ⟨8554858697725650419572937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5703239131817100279715291 8554858697725650419572937)
        ·
          refine ⟨6416144023294237814679703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8554858697725650419572937 6416144023294237814679703)
          ·
            refine ⟨9624216034941356722019555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6416144023294237814679703 9624216034941356722019555)
            ·
              refine ⟨14436324052412035083029333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9624216034941356722019555 14436324052412035083029333)
              ·
                refine ⟨84587836244601768064625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14436324052412035083029333 84587836244601768064625)
                ·
                  rfl

theorem cell20_555978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_555978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555978 prefixEnd_555978 := by exact prefixLift 555978
  have htrace : WordTrace (prefixWord ++ tailWord_555978) baseStart_555978 baseEnd_555978 := by
    simpa [prefixWord, tailWord_555978, baseEnd_555978] using wordTrace_append hprefix tailTrace_555978
  have hstable : (prefixWord ++ tailWord_555978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555978).length < 2 ^ (prefixWord ++ tailWord_555978).sum := by decide
  have hdescent : baseEnd_555978 < baseStart_555978 := by decide
  rcases family_descends (prefixWord ++ tailWord_555978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555988 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 4]
def baseStart_555988 : Nat := 118140960795 + 555988 * 2 ^ 59
def prefixEnd_555988 : Nat := 4983230072969 + 3 ^ 40 * 555988 * 2
def baseEnd_555988 : Nat := 253768073006289713860501

theorem tailTrace_555988 : CollatzResearch.WordTrace tailWord_555988 prefixEnd_555988 253768073006289713860501 := by
  unfold tailWord_555988
  simp only [CollatzResearch.WordTrace]
  refine ⟨10139274154878953017870309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13519032206505270690493745 10139274154878953017870309)
  ·
    refine ⟨1901113904039803690850683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10139274154878953017870309 1901113904039803690850683)
    ·
      refine ⟨2851670856059705536276025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1901113904039803690850683 2851670856059705536276025)
      ·
        refine ⟨2138753142044779152207019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2851670856059705536276025 2138753142044779152207019)
        ·
          refine ⟨3208129713067168728310529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2138753142044779152207019 3208129713067168728310529)
          ·
            refine ⟨2406097284800376546232897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3208129713067168728310529 2406097284800376546232897)
            ·
              refine ⟨1804572963600282409674673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2406097284800376546232897 1804572963600282409674673)
              ·
                refine ⟨1353429722700211807256005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1804572963600282409674673 1353429722700211807256005)
                ·
                  refine ⟨253768073006289713860501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1353429722700211807256005 253768073006289713860501)
                  ·
                    rfl

theorem cell20_555988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_555988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_555988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_555988 prefixEnd_555988 := by exact prefixLift 555988
  have htrace : WordTrace (prefixWord ++ tailWord_555988) baseStart_555988 baseEnd_555988 := by
    simpa [prefixWord, tailWord_555988, baseEnd_555988] using wordTrace_append hprefix tailTrace_555988
  have hstable : (prefixWord ++ tailWord_555988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555988).length < 2 ^ (prefixWord ++ tailWord_555988).sum := by decide
  have hdescent : baseEnd_555988 < baseStart_555988 := by decide
  rcases family_descends (prefixWord ++ tailWord_555988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556026 : List Nat := [3, 1, 1, 1, 1, 2, 1, 8, 2]
def baseStart_556026 : Nat := 118140960795 + 556026 * 2 ^ 59
def prefixEnd_556026 : Nat := 4983230072969 + 3 ^ 40 * 556026 * 2
def baseEnd_556026 : Nat := 253785417241730470593679

theorem tailTrace_556026 : CollatzResearch.WordTrace tailWord_556026 prefixEnd_556026 253785417241730470593679 := by
  unfold tailWord_556026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5069983570905059631405983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13519956189080159017082621 5069983570905059631405983)
  ·
    refine ⟨7604975356357589447108975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5069983570905059631405983 7604975356357589447108975)
    ·
      refine ⟨11407463034536384170663463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7604975356357589447108975 11407463034536384170663463)
      ·
        refine ⟨17111194551804576255995195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11407463034536384170663463 17111194551804576255995195)
        ·
          refine ⟨25666791827706864383992793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17111194551804576255995195 25666791827706864383992793)
          ·
            refine ⟨19250093870780148287994595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25666791827706864383992793 19250093870780148287994595)
            ·
              refine ⟨28875140806170222431991893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19250093870780148287994595 28875140806170222431991893)
              ·
                refine ⟨338380556322307294124905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 28875140806170222431991893 338380556322307294124905)
                ·
                  refine ⟨253785417241730470593679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338380556322307294124905 253785417241730470593679)
                  ·
                    rfl

theorem cell20_556026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_556026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556026 prefixEnd_556026 := by exact prefixLift 556026
  have htrace : WordTrace (prefixWord ++ tailWord_556026) baseStart_556026 baseEnd_556026 := by
    simpa [prefixWord, tailWord_556026, baseEnd_556026] using wordTrace_append hprefix tailTrace_556026
  have hstable : (prefixWord ++ tailWord_556026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556026).length < 2 ^ (prefixWord ++ tailWord_556026).sum := by decide
  have hdescent : baseEnd_556026 < baseStart_556026 := by decide
  rcases family_descends (prefixWord ++ tailWord_556026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556033 : List Nat := [1, 2, 4, 1, 2, 3, 2, 5]
def baseStart_556033 : Nat := 118140960795 + 556033 * 2 ^ 59
def prefixEnd_556033 : Nat := 4983230072969 + 3 ^ 40 * 556033 * 2
def baseEnd_556033 : Nat := 84596204077489852453439

theorem tailTrace_556033 : CollatzResearch.WordTrace tailWord_556033 prefixEnd_556033 84596204077489852453439 := by
  unfold tailWord_556033
  simp only [CollatzResearch.WordTrace]
  refine ⟨20280189594594878721128753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13520126396396585814085835 20280189594594878721128753)
  ·
    refine ⟨15210142195946159040846565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20280189594594878721128753 15210142195946159040846565)
    ·
      refine ⟨2851901661739904820158731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15210142195946159040846565 2851901661739904820158731)
      ·
        refine ⟨4277852492609857230238097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2851901661739904820158731 4277852492609857230238097)
        ·
          refine ⟨3208389369457392922678573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4277852492609857230238097 3208389369457392922678573)
          ·
            refine ⟨1203146013546522346004465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3208389369457392922678573 1203146013546522346004465)
            ·
              refine ⟨902359510159891759503349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1203146013546522346004465 902359510159891759503349)
              ·
                refine ⟨84596204077489852453439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 902359510159891759503349 84596204077489852453439)
                ·
                  rfl

theorem cell20_556033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 5].length) (baseStart_556033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556033 prefixEnd_556033 := by exact prefixLift 556033
  have htrace : WordTrace (prefixWord ++ tailWord_556033) baseStart_556033 baseEnd_556033 := by
    simpa [prefixWord, tailWord_556033, baseEnd_556033] using wordTrace_append hprefix tailTrace_556033
  have hstable : (prefixWord ++ tailWord_556033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556033).length < 2 ^ (prefixWord ++ tailWord_556033).sum := by decide
  have hdescent : baseEnd_556033 < baseStart_556033 := by decide
  rcases family_descends (prefixWord ++ tailWord_556033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556071 : List Nat := [1, 1, 7, 1, 1, 9]
def baseStart_556071 : Nat := 118140960795 + 556071 * 2 ^ 59
def prefixEnd_556071 : Nat := 4983230072969 + 3 ^ 40 * 556071 * 2
def baseEnd_556071 : Nat := 9400220609922604225685

theorem tailTrace_556071 : CollatzResearch.WordTrace tailWord_556071 prefixEnd_556071 9400220609922604225685 := by
  unfold tailWord_556071
  simp only [CollatzResearch.WordTrace]
  refine ⟨20281575568457211211012067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13521050378971474140674711 20281575568457211211012067)
  ·
    refine ⟨30422363352685816816518101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20281575568457211211012067 30422363352685816816518101)
    ·
      refine ⟨713024141078573831637143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 30422363352685816816518101 713024141078573831637143)
      ·
        refine ⟨1069536211617860747455715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713024141078573831637143 1069536211617860747455715)
        ·
          refine ⟨1604304317426791121183573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1069536211617860747455715 1604304317426791121183573)
          ·
            refine ⟨9400220609922604225685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1604304317426791121183573 9400220609922604225685)
            ·
              rfl

theorem cell20_556071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 9].length) (baseStart_556071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556071 prefixEnd_556071 := by exact prefixLift 556071
  have htrace : WordTrace (prefixWord ++ tailWord_556071) baseStart_556071 baseEnd_556071 := by
    simpa [prefixWord, tailWord_556071, baseEnd_556071] using wordTrace_append hprefix tailTrace_556071
  have hstable : (prefixWord ++ tailWord_556071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556071).length < 2 ^ (prefixWord ++ tailWord_556071).sum := by decide
  have hdescent : baseEnd_556071 < baseStart_556071 := by decide
  rcases family_descends (prefixWord ++ tailWord_556071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556074 : List Nat := [3, 1, 4, 1, 3, 1, 2, 2, 3]
def baseStart_556074 : Nat := 118140960795 + 556074 * 2 ^ 59
def prefixEnd_556074 : Nat := 4983230072969 + 3 ^ 40 * 556074 * 2
def baseEnd_556074 : Nat := 253807325749655636993483

theorem tailTrace_556074 : CollatzResearch.WordTrace tailWord_556074 prefixEnd_556074 253807325749655636993483 := by
  unfold tailWord_556074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5070421246861585680842819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13521123324964228482247517 5070421246861585680842819)
  ·
    refine ⟨7605631870292378521264229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5070421246861585680842819 7605631870292378521264229)
    ·
      refine ⟨1426055975679820972737043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7605631870292378521264229 1426055975679820972737043)
      ·
        refine ⟨2139083963519731459105565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1426055975679820972737043 2139083963519731459105565)
        ·
          refine ⟨802156486319899297164587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2139083963519731459105565 802156486319899297164587)
          ·
            refine ⟨1203234729479848945746881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802156486319899297164587 1203234729479848945746881)
            ·
              refine ⟨902426047109886709310161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1203234729479848945746881 902426047109886709310161)
              ·
                refine ⟨676819535332415031982621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 902426047109886709310161 676819535332415031982621)
                ·
                  refine ⟨253807325749655636993483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676819535332415031982621 253807325749655636993483)
                  ·
                    rfl

theorem cell20_556074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_556074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556074 prefixEnd_556074 := by exact prefixLift 556074
  have htrace : WordTrace (prefixWord ++ tailWord_556074) baseStart_556074 baseEnd_556074 := by
    simpa [prefixWord, tailWord_556074, baseEnd_556074] using wordTrace_append hprefix tailTrace_556074
  have hstable : (prefixWord ++ tailWord_556074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556074).length < 2 ^ (prefixWord ++ tailWord_556074).sum := by decide
  have hdescent : baseEnd_556074 < baseStart_556074 := by decide
  rcases family_descends (prefixWord ++ tailWord_556074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556085 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 4]
def baseStart_556085 : Nat := 118140960795 + 556085 * 2 ^ 59
def prefixEnd_556085 : Nat := 4983230072969 + 3 ^ 40 * 556085 * 2
def baseEnd_556085 : Nat := 253812346449388487626771

theorem tailTrace_556085 : CollatzResearch.WordTrace tailWord_556085 prefixEnd_556085 253812346449388487626771 := by
  unfold tailWord_556085
  simp only [CollatzResearch.WordTrace]
  refine ⟨20282086190406491602021709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13521390793604327734681139 20282086190406491602021709)
  ·
    refine ⟨7605782321402434350758141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20282086190406491602021709 7605782321402434350758141)
    ·
      refine ⟨2852168370525912881534303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7605782321402434350758141 2852168370525912881534303)
      ·
        refine ⟨4278252555788869322301455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2852168370525912881534303 4278252555788869322301455)
        ·
          refine ⟨6417378833683303983452183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4278252555788869322301455 6417378833683303983452183)
          ·
            refine ⟨9626068250524955975178275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6417378833683303983452183 9626068250524955975178275)
            ·
              refine ⟨14439102375787433962767413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9626068250524955975178275 14439102375787433962767413)
              ·
                refine ⟨1353665847730071934009445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14439102375787433962767413 1353665847730071934009445)
                ·
                  refine ⟨253812346449388487626771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1353665847730071934009445 253812346449388487626771)
                  ·
                    rfl

theorem cell20_556085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_556085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556085 prefixEnd_556085 := by exact prefixLift 556085
  have htrace : WordTrace (prefixWord ++ tailWord_556085) baseStart_556085 baseEnd_556085 := by
    simpa [prefixWord, tailWord_556085, baseEnd_556085] using wordTrace_append hprefix tailTrace_556085
  have hstable : (prefixWord ++ tailWord_556085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556085).length < 2 ^ (prefixWord ++ tailWord_556085).sum := by decide
  have hdescent : baseEnd_556085 < baseStart_556085 := by decide
  rcases family_descends (prefixWord ++ tailWord_556085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556140 : List Nat := [2, 2, 1, 1, 3, 2, 1, 6, 2]
def baseStart_556140 : Nat := 118140960795 + 556140 * 2 ^ 59
def prefixEnd_556140 : Nat := 4983230072969 + 3 ^ 40 * 556140 * 2
def baseEnd_556140 : Nat := 253837449948052740793213

theorem tailTrace_556140 : CollatzResearch.WordTrace tailWord_556140 prefixEnd_556140 253837449948052740793213 := by
  unfold tailWord_556140
  simp only [CollatzResearch.WordTrace]
  refine ⟨10142046102603617997636937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13522728136804823996849249 10142046102603617997636937)
  ·
    refine ⟨7606534576952713498227703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10142046102603617997636937 7606534576952713498227703)
    ·
      refine ⟨11409801865429070247341555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7606534576952713498227703 11409801865429070247341555)
      ·
        refine ⟨17114702798143605371012333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11409801865429070247341555 17114702798143605371012333)
        ·
          refine ⟨6418013549303852014129625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17114702798143605371012333 6418013549303852014129625)
          ·
            refine ⟨4813510161977889010597219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6418013549303852014129625 4813510161977889010597219)
            ·
              refine ⟨7220265242966833515895829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4813510161977889010597219 7220265242966833515895829)
              ·
                refine ⟨338449933264070321057617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7220265242966833515895829 338449933264070321057617)
                ·
                  refine ⟨253837449948052740793213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338449933264070321057617 253837449948052740793213)
                  ·
                    rfl

theorem cell20_556140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_556140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556140 prefixEnd_556140 := by exact prefixLift 556140
  have htrace : WordTrace (prefixWord ++ tailWord_556140) baseStart_556140 baseEnd_556140 := by
    simpa [prefixWord, tailWord_556140, baseEnd_556140] using wordTrace_append hprefix tailTrace_556140
  have hstable : (prefixWord ++ tailWord_556140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556140).length < 2 ^ (prefixWord ++ tailWord_556140).sum := by decide
  have hdescent : baseEnd_556140 < baseStart_556140 := by decide
  rcases family_descends (prefixWord ++ tailWord_556140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556150 : List Nat := [5, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_556150 : Nat := 118140960795 + 556150 * 2 ^ 59
def prefixEnd_556150 : Nat := 4983230072969 + 3 ^ 40 * 556150 * 2
def baseEnd_556150 : Nat := 253842014220537150459839

theorem tailTrace_556150 : CollatzResearch.WordTrace tailWord_556150 prefixEnd_556150 253842014220537150459839 := by
  unfold tailWord_556150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1267778558448187981446119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13522971290114005135425269 1267778558448187981446119)
  ·
    refine ⟨1901667837672281972169179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1267778558448187981446119 1901667837672281972169179)
    ·
      refine ⟨2852501756508422958253769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1901667837672281972169179 2852501756508422958253769)
      ·
        refine ⟨2139376317381317218690327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2852501756508422958253769 2139376317381317218690327)
        ·
          refine ⟨3209064476071975828035491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2139376317381317218690327 3209064476071975828035491)
          ·
            refine ⟨4813596714107963742053237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3209064476071975828035491 4813596714107963742053237)
            ·
              refine ⟨451274691947621600817491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4813596714107963742053237 451274691947621600817491)
              ·
                refine ⟨676912037921432401226237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451274691947621600817491 676912037921432401226237)
                ·
                  refine ⟨253842014220537150459839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676912037921432401226237 253842014220537150459839)
                  ·
                    rfl

theorem cell20_556150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_556150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556150 prefixEnd_556150 := by exact prefixLift 556150
  have htrace : WordTrace (prefixWord ++ tailWord_556150) baseStart_556150 baseEnd_556150 := by
    simpa [prefixWord, tailWord_556150, baseEnd_556150] using wordTrace_append hprefix tailTrace_556150
  have hstable : (prefixWord ++ tailWord_556150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556150).length < 2 ^ (prefixWord ++ tailWord_556150).sum := by decide
  have hdescent : baseEnd_556150 < baseStart_556150 := by decide
  rcases family_descends (prefixWord ++ tailWord_556150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556164 : List Nat := [2, 3, 2, 1, 2, 4, 2, 4]
def baseStart_556164 : Nat := 118140960795 + 556164 * 2 ^ 59
def prefixEnd_556164 : Nat := 4983230072969 + 3 ^ 40 * 556164 * 2
def baseEnd_556164 : Nat := 84616134734005107997705

theorem tailTrace_556164 : CollatzResearch.WordTrace tailWord_556164 prefixEnd_556164 84616134734005107997705 := by
  unfold tailWord_556164
  simp only [CollatzResearch.WordTrace]
  refine ⟨10142483778560144047073773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13523311704746858729431697 10142483778560144047073773)
  ·
    refine ⟨3803431416960054017652665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10142483778560144047073773 3803431416960054017652665)
    ·
      refine ⟨2852573562720040513239499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3803431416960054017652665 2852573562720040513239499)
      ·
        refine ⟨4278860344080060769859249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2852573562720040513239499 4278860344080060769859249)
        ·
          refine ⟨3209145258060045577394437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4278860344080060769859249 3209145258060045577394437)
          ·
            refine ⟨601714735886258545761457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3209145258060045577394437 601714735886258545761457)
            ·
              refine ⟨451286051914693909321093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601714735886258545761457 451286051914693909321093)
              ·
                refine ⟨84616134734005107997705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 451286051914693909321093 84616134734005107997705)
                ·
                  rfl

theorem cell20_556164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_556164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556164 prefixEnd_556164 := by exact prefixLift 556164
  have htrace : WordTrace (prefixWord ++ tailWord_556164) baseStart_556164 baseEnd_556164 := by
    simpa [prefixWord, tailWord_556164, baseEnd_556164] using wordTrace_append hprefix tailTrace_556164
  have hstable : (prefixWord ++ tailWord_556164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556164).length < 2 ^ (prefixWord ++ tailWord_556164).sum := by decide
  have hdescent : baseEnd_556164 < baseStart_556164 := by decide
  rcases family_descends (prefixWord ++ tailWord_556164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556174 : List Nat := [4, 1, 1, 3, 2, 3, 1, 3, 2]
def baseStart_556174 : Nat := 118140960795 + 556174 * 2 ^ 59
def prefixEnd_556174 : Nat := 4983230072969 + 3 ^ 40 * 556174 * 2
def baseEnd_556174 : Nat := 253852968474499733659741

theorem tailTrace_556174 : CollatzResearch.WordTrace tailWord_556174 prefixEnd_556174 253852968474499733659741 := by
  unfold tailWord_556174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2535666535885507475251447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13523554858056039868007717 2535666535885507475251447)
  ·
    refine ⟨3803499803828261212877171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2535666535885507475251447 3803499803828261212877171)
    ·
      refine ⟨5705249705742391819315757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3803499803828261212877171 5705249705742391819315757)
      ·
        refine ⟨2139468639653396932243409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5705249705742391819315757 2139468639653396932243409)
        ·
          refine ⟨1604601479740047699182557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2139468639653396932243409 1604601479740047699182557)
          ·
            refine ⟨601725554902517887193459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1604601479740047699182557 601725554902517887193459)
            ·
              refine ⟨902588332353776830790189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601725554902517887193459 902588332353776830790189)
              ·
                refine ⟨338470624632666311546321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 902588332353776830790189 338470624632666311546321)
                ·
                  refine ⟨253852968474499733659741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338470624632666311546321 253852968474499733659741)
                  ·
                    rfl

theorem cell20_556174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_556174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556174 prefixEnd_556174 := by exact prefixLift 556174
  have htrace : WordTrace (prefixWord ++ tailWord_556174) baseStart_556174 baseEnd_556174 := by
    simpa [prefixWord, tailWord_556174, baseEnd_556174] using wordTrace_append hprefix tailTrace_556174
  have hstable : (prefixWord ++ tailWord_556174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556174).length < 2 ^ (prefixWord ++ tailWord_556174).sum := by decide
  have hdescent : baseEnd_556174 < baseStart_556174 := by decide
  rcases family_descends (prefixWord ++ tailWord_556174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556192 : List Nat := [2, 1, 1, 4, 2, 1, 2, 4, 3]
def baseStart_556192 : Nat := 118140960795 + 556192 * 2 ^ 59
def prefixEnd_556192 : Nat := 4983230072969 + 3 ^ 40 * 556192 * 2
def baseEnd_556192 : Nat := 253861184164971671059667

theorem tailTrace_556192 : CollatzResearch.WordTrace tailWord_556192 prefixEnd_556192 253861184164971671059667 := by
  unfold tailWord_556192
  simp only [CollatzResearch.WordTrace]
  refine ⟨10142994400509424438083415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13523992534012565917444553 10142994400509424438083415)
  ·
    refine ⟨15214491600764136657125123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10142994400509424438083415 15214491600764136657125123)
    ·
      refine ⟨22821737401146204985687685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15214491600764136657125123 22821737401146204985687685)
      ·
        refine ⟨4279075762714913434816441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22821737401146204985687685 4279075762714913434816441)
        ·
          refine ⟨3209306822036185076112331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4279075762714913434816441 3209306822036185076112331)
          ·
            refine ⟨4813960233054277614168497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3209306822036185076112331 4813960233054277614168497)
            ·
              refine ⟨3610470174790708210626373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4813960233054277614168497 3610470174790708210626373)
              ·
                refine ⟨676963157773257789492445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3610470174790708210626373 676963157773257789492445)
                ·
                  refine ⟨253861184164971671059667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676963157773257789492445 253861184164971671059667)
                  ·
                    rfl

theorem cell20_556192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_556192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556192 prefixEnd_556192 := by exact prefixLift 556192
  have htrace : WordTrace (prefixWord ++ tailWord_556192) baseStart_556192 baseEnd_556192 := by
    simpa [prefixWord, tailWord_556192, baseEnd_556192] using wordTrace_append hprefix tailTrace_556192
  have hstable : (prefixWord ++ tailWord_556192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556192).length < 2 ^ (prefixWord ++ tailWord_556192).sum := by decide
  have hdescent : baseEnd_556192 < baseStart_556192 := by decide
  rcases family_descends (prefixWord ++ tailWord_556192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556202 : List Nat := [3, 1, 5, 1, 1, 2, 2, 5]
def baseStart_556202 : Nat := 118140960795 + 556202 * 2 ^ 59
def prefixEnd_556202 : Nat := 4983230072969 + 3 ^ 40 * 556202 * 2
def baseEnd_556202 : Nat := 84621916145818693575431

theorem tailTrace_556202 : CollatzResearch.WordTrace tailWord_556202 prefixEnd_556202 84621916145818693575431 := by
  unfold tailWord_556202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5071588382745655146007715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13524235687321747056020573 5071588382745655146007715)
  ·
    refine ⟨7607382574118482719011573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5071588382745655146007715 7607382574118482719011573)
    ·
      refine ⟨713192116323607754907335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7607382574118482719011573 713192116323607754907335)
      ·
        refine ⟨1069788174485411632361003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713192116323607754907335 1069788174485411632361003)
        ·
          refine ⟨1604682261728117448541505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1069788174485411632361003 1604682261728117448541505)
          ·
            refine ⟨1203511696296088086406129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1604682261728117448541505 1203511696296088086406129)
            ·
              refine ⟨902633772222066064804597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1203511696296088086406129 902633772222066064804597)
              ·
                refine ⟨84621916145818693575431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 902633772222066064804597 84621916145818693575431)
                ·
                  rfl

theorem cell20_556202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_556202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556202 prefixEnd_556202 := by exact prefixLift 556202
  have htrace : WordTrace (prefixWord ++ tailWord_556202) baseStart_556202 baseEnd_556202 := by
    simpa [prefixWord, tailWord_556202, baseEnd_556202] using wordTrace_append hprefix tailTrace_556202
  have hstable : (prefixWord ++ tailWord_556202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556202).length < 2 ^ (prefixWord ++ tailWord_556202).sum := by decide
  have hdescent : baseEnd_556202 < baseStart_556202 := by decide
  rcases family_descends (prefixWord ++ tailWord_556202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556205 : List Nat := [1, 5, 2, 1, 3, 2, 2, 1, 3]
def baseStart_556205 : Nat := 118140960795 + 556205 * 2 ^ 59
def prefixEnd_556205 : Nat := 4983230072969 + 3 ^ 40 * 556205 * 2
def baseEnd_556205 : Nat := 253867117719201403626281

theorem tailTrace_556205 : CollatzResearch.WordTrace tailWord_556205 prefixEnd_556205 253867117719201403626281 := by
  unfold tailWord_556205
  simp only [CollatzResearch.WordTrace]
  refine ⟨20286462949971752096390069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13524308633314501397593379 20286462949971752096390069)
  ·
    refine ⟨1901855901559851759036569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20286462949971752096390069 1901855901559851759036569)
    ·
      refine ⟨1426391926169888819277427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1901855901559851759036569 1426391926169888819277427)
      ·
        refine ⟨2139587889254833228916141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1426391926169888819277427 2139587889254833228916141)
        ·
          refine ⟨802345458470562460843553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2139587889254833228916141 802345458470562460843553)
          ·
            refine ⟨601759093852921845632665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802345458470562460843553 601759093852921845632665)
            ·
              refine ⟨451319320389691384224499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601759093852921845632665 451319320389691384224499)
              ·
                refine ⟨676978980584537076336749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451319320389691384224499 676978980584537076336749)
                ·
                  refine ⟨253867117719201403626281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676978980584537076336749 253867117719201403626281)
                  ·
                    rfl

theorem cell20_556205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_556205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556205 prefixEnd_556205 := by exact prefixLift 556205
  have htrace : WordTrace (prefixWord ++ tailWord_556205) baseStart_556205 baseEnd_556205 := by
    simpa [prefixWord, tailWord_556205, baseEnd_556205] using wordTrace_append hprefix tailTrace_556205
  have hstable : (prefixWord ++ tailWord_556205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556205).length < 2 ^ (prefixWord ++ tailWord_556205).sum := by decide
  have hdescent : baseEnd_556205 < baseStart_556205 := by decide
  rcases family_descends (prefixWord ++ tailWord_556205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556209 : List Nat := [1, 2, 2, 5, 1, 2, 1, 3, 3]
def baseStart_556209 : Nat := 118140960795 + 556209 * 2 ^ 59
def prefixEnd_556209 : Nat := 4983230072969 + 3 ^ 40 * 556209 * 2
def baseEnd_556209 : Nat := 253868943428195167492931

theorem tailTrace_556209 : CollatzResearch.WordTrace tailWord_556209 prefixEnd_556209 253868943428195167492931 := by
  unfold tailWord_556209
  simp only [CollatzResearch.WordTrace]
  refine ⟨20286608841957260779535681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13524405894638173853023787 20286608841957260779535681)
  ·
    refine ⟨15214956631467945584651761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20286608841957260779535681 15214956631467945584651761)
    ·
      refine ⟨11411217473600959188488821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15214956631467945584651761 11411217473600959188488821)
      ·
        refine ⟨1069801638150089923920827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11411217473600959188488821 1069801638150089923920827)
        ·
          refine ⟨1604702457225134885881241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1069801638150089923920827 1604702457225134885881241)
          ·
            refine ⟨1203526842918851164410931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1604702457225134885881241 1203526842918851164410931)
            ·
              refine ⟨1805290264378276746616397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203526842918851164410931 1805290264378276746616397)
              ·
                refine ⟨676983849141853779981149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1805290264378276746616397 676983849141853779981149)
                ·
                  refine ⟨253868943428195167492931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676983849141853779981149 253868943428195167492931)
                  ·
                    rfl

theorem cell20_556209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_556209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556209 prefixEnd_556209 := by exact prefixLift 556209
  have htrace : WordTrace (prefixWord ++ tailWord_556209) baseStart_556209 baseEnd_556209 := by
    simpa [prefixWord, tailWord_556209, baseEnd_556209] using wordTrace_append hprefix tailTrace_556209
  have hstable : (prefixWord ++ tailWord_556209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556209).length < 2 ^ (prefixWord ++ tailWord_556209).sum := by decide
  have hdescent : baseEnd_556209 < baseStart_556209 := by decide
  rcases family_descends (prefixWord ++ tailWord_556209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556246 : List Nat := [5, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_556246 : Nat := 118140960795 + 556246 * 2 ^ 59
def prefixEnd_556246 : Nat := 4983230072969 + 3 ^ 40 * 556246 * 2
def baseEnd_556246 : Nat := 253885831236387483259447

theorem tailTrace_556246 : CollatzResearch.WordTrace tailWord_556246 prefixEnd_556246 253885831236387483259447 := by
  unfold tailWord_556246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1267997396426451006164537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13525305561882144065755061 1267997396426451006164537)
  ·
    refine ⟨950998047319838254623403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1267997396426451006164537 950998047319838254623403)
    ·
      refine ⟨1426497070979757381935105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 950998047319838254623403 1426497070979757381935105)
      ·
        refine ⟨1069872803234818036451329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1426497070979757381935105 1069872803234818036451329)
        ·
          refine ⟨802404602426113527338497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1069872803234818036451329 802404602426113527338497)
          ·
            refine ⟨601803451819585145503873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802404602426113527338497 601803451819585145503873)
            ·
              refine ⟨451352588864688859127905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601803451819585145503873 451352588864688859127905)
              ·
                refine ⟨338514441648516644345929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451352588864688859127905 338514441648516644345929)
                ·
                  refine ⟨253885831236387483259447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338514441648516644345929 253885831236387483259447)
                  ·
                    rfl

theorem cell20_556246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_556246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556246 prefixEnd_556246 := by exact prefixLift 556246
  have htrace : WordTrace (prefixWord ++ tailWord_556246) baseStart_556246 baseEnd_556246 := by
    simpa [prefixWord, tailWord_556246, baseEnd_556246] using wordTrace_append hprefix tailTrace_556246
  have hstable : (prefixWord ++ tailWord_556246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556246).length < 2 ^ (prefixWord ++ tailWord_556246).sum := by decide
  have hdescent : baseEnd_556246 < baseStart_556246 := by decide
  rcases family_descends (prefixWord ++ tailWord_556246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556268 : List Nat := [2, 2, 1, 1, 2, 4, 2, 3, 3]
def baseStart_556268 : Nat := 118140960795 + 556268 * 2 ^ 59
def prefixEnd_556268 : Nat := 4983230072969 + 3 ^ 40 * 556268 * 2
def baseEnd_556268 : Nat := 253895872635853184526023

theorem tailTrace_556268 : CollatzResearch.WordTrace tailWord_556268 prefixEnd_556268 253895872635853184526023 := by
  unfold tailWord_556268
  simp only [CollatzResearch.WordTrace]
  refine ⟨10144380374371756927966729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13525840499162342570622305 10144380374371756927966729)
  ·
    refine ⟨7608285280778817695975047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10144380374371756927966729 7608285280778817695975047)
    ·
      refine ⟨11412427921168226543962571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7608285280778817695975047 11412427921168226543962571)
      ·
        refine ⟨17118641881752339815943857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11412427921168226543962571 17118641881752339815943857)
        ·
          refine ⟨12838981411314254861957893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17118641881752339815943857 12838981411314254861957893)
          ·
            refine ⟨2407309014621422786617105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12838981411314254861957893 2407309014621422786617105)
            ·
              refine ⟨1805481760966067089962829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2407309014621422786617105 1805481760966067089962829)
              ·
                refine ⟨677055660362275158736061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1805481760966067089962829 677055660362275158736061)
                ·
                  refine ⟨253895872635853184526023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 677055660362275158736061 253895872635853184526023)
                  ·
                    rfl

theorem cell20_556268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_556268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556268 prefixEnd_556268 := by exact prefixLift 556268
  have htrace : WordTrace (prefixWord ++ tailWord_556268) baseStart_556268 baseEnd_556268 := by
    simpa [prefixWord, tailWord_556268, baseEnd_556268] using wordTrace_append hprefix tailTrace_556268
  have hstable : (prefixWord ++ tailWord_556268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556268).length < 2 ^ (prefixWord ++ tailWord_556268).sum := by decide
  have hdescent : baseEnd_556268 < baseStart_556268 := by decide
  rcases family_descends (prefixWord ++ tailWord_556268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556275 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 4]
def baseStart_556275 : Nat := 118140960795 + 556275 * 2 ^ 59
def prefixEnd_556275 : Nat := 4983230072969 + 3 ^ 40 * 556275 * 2
def baseEnd_556275 : Nat := 253899067626592271292661

theorem tailTrace_556275 : CollatzResearch.WordTrace tailWord_556275 prefixEnd_556275 253899067626592271292661 := by
  unfold tailWord_556275
  simp only [CollatzResearch.WordTrace]
  refine ⟨20289016059718154051438279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13526010706478769367625519 20289016059718154051438279)
  ·
    refine ⟨30433524089577231077157419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20289016059718154051438279 30433524089577231077157419)
    ·
      refine ⟨45650286134365846615736129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30433524089577231077157419 45650286134365846615736129)
      ·
        refine ⟨34237714600774384961802097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45650286134365846615736129 34237714600774384961802097)
        ·
          refine ⟨25678285950580788721351573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34237714600774384961802097 25678285950580788721351573)
          ·
            refine ⟨1203669653933474471313355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25678285950580788721351573 1203669653933474471313355)
            ·
              refine ⟨1805504480900211706970033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203669653933474471313355 1805504480900211706970033)
              ·
                refine ⟨1354128360675158780227525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1805504480900211706970033 1354128360675158780227525)
                ·
                  refine ⟨253899067626592271292661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1354128360675158780227525 253899067626592271292661)
                  ·
                    rfl

theorem cell20_556275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_556275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556275 prefixEnd_556275 := by exact prefixLift 556275
  have htrace : WordTrace (prefixWord ++ tailWord_556275) baseStart_556275 baseEnd_556275 := by
    simpa [prefixWord, tailWord_556275, baseEnd_556275] using wordTrace_append hprefix tailTrace_556275
  have hstable : (prefixWord ++ tailWord_556275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556275).length < 2 ^ (prefixWord ++ tailWord_556275).sum := by decide
  have hdescent : baseEnd_556275 < baseStart_556275 := by decide
  rcases family_descends (prefixWord ++ tailWord_556275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556323 : List Nat := [1, 1, 1, 4, 2, 4, 3, 1, 3]
def baseStart_556323 : Nat := 118140960795 + 556323 * 2 ^ 59
def prefixEnd_556323 : Nat := 4983230072969 + 3 ^ 40 * 556323 * 2
def baseEnd_556323 : Nat := 253920976134517437692465

theorem tailTrace_556323 : CollatzResearch.WordTrace tailWord_556323 prefixEnd_556323 253920976134517437692465 := by
  unfold tailWord_556323
  simp only [CollatzResearch.WordTrace]
  refine ⟨20290766763544258249185623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13527177842362838832790415 20290766763544258249185623)
  ·
    refine ⟨30436150145316387373778435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20290766763544258249185623 30436150145316387373778435)
    ·
      refine ⟨45654225217974581060667653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30436150145316387373778435 45654225217974581060667653)
      ·
        refine ⟨8560167228370233948875185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45654225217974581060667653 8560167228370233948875185)
        ·
          refine ⟨6420125421277675461656389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8560167228370233948875185 6420125421277675461656389)
          ·
            refine ⟨1203773516489564149060573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6420125421277675461656389 1203773516489564149060573)
            ·
              refine ⟨451415068683586555897715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1203773516489564149060573 451415068683586555897715)
              ·
                refine ⟨677122603025379833846573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451415068683586555897715 677122603025379833846573)
                ·
                  refine ⟨253920976134517437692465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 677122603025379833846573 253920976134517437692465)
                  ·
                    rfl

theorem cell20_556323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 3].length) (baseStart_556323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556323 prefixEnd_556323 := by exact prefixLift 556323
  have htrace : WordTrace (prefixWord ++ tailWord_556323) baseStart_556323 baseEnd_556323 := by
    simpa [prefixWord, tailWord_556323, baseEnd_556323] using wordTrace_append hprefix tailTrace_556323
  have hstable : (prefixWord ++ tailWord_556323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556323).length < 2 ^ (prefixWord ++ tailWord_556323).sum := by decide
  have hdescent : baseEnd_556323 < baseStart_556323 := by decide
  rcases family_descends (prefixWord ++ tailWord_556323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556330 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_556330 : Nat := 118140960795 + 556330 * 2 ^ 59
def prefixEnd_556330 : Nat := 4983230072969 + 3 ^ 40 * 556330 * 2
def baseEnd_556330 : Nat := 253924171125256524459103

theorem tailTrace_556330 : CollatzResearch.WordTrace tailWord_556330 prefixEnd_556330 253924171125256524459103 := by
  unfold tailWord_556330
  simp only [CollatzResearch.WordTrace]
  refine ⟨5072755518629724611172611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13527348049679265629793629 5072755518629724611172611)
  ·
    refine ⟨7609133277944586916758917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5072755518629724611172611 7609133277944586916758917)
    ·
      refine ⟨1426712489614610046892297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7609133277944586916758917 1426712489614610046892297)
      ·
        refine ⟨1070034367210957535169223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1426712489614610046892297 1070034367210957535169223)
        ·
          refine ⟨1605051550816436302753835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070034367210957535169223 1605051550816436302753835)
          ·
            refine ⟨2407577326224654454130753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605051550816436302753835 2407577326224654454130753)
            ·
              refine ⟨1805682994668490840598065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2407577326224654454130753 1805682994668490840598065)
              ·
                refine ⟨1354262246001368130448549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1805682994668490840598065 1354262246001368130448549)
                ·
                  refine ⟨253924171125256524459103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1354262246001368130448549 253924171125256524459103)
                  ·
                    rfl

theorem cell20_556330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_556330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556330 prefixEnd_556330 := by exact prefixLift 556330
  have htrace : WordTrace (prefixWord ++ tailWord_556330) baseStart_556330 baseEnd_556330 := by
    simpa [prefixWord, tailWord_556330, baseEnd_556330] using wordTrace_append hprefix tailTrace_556330
  have hstable : (prefixWord ++ tailWord_556330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556330).length < 2 ^ (prefixWord ++ tailWord_556330).sum := by decide
  have hdescent : baseEnd_556330 < baseStart_556330 := by decide
  rcases family_descends (prefixWord ++ tailWord_556330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556333 : List Nat := [1, 5, 3, 1, 1, 3, 2, 4]
def baseStart_556333 : Nat := 118140960795 + 556333 * 2 ^ 59
def prefixEnd_556333 : Nat := 4983230072969 + 3 ^ 40 * 556333 * 2
def baseEnd_556333 : Nat := 84641846802333949119697

theorem tailTrace_556333 : CollatzResearch.WordTrace tailWord_556333 prefixEnd_556333 84641846802333949119697 := by
  unfold tailWord_556333
  simp only [CollatzResearch.WordTrace]
  refine ⟨20291131493508029957049653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13527420995672019971366435 20291131493508029957049653)
  ·
    refine ⟨1902293577516377808473405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20291131493508029957049653 1902293577516377808473405)
    ·
      refine ⟨713360091568641678177527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1902293577516377808473405 713360091568641678177527)
      ·
        refine ⟨1070040137352962517266291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713360091568641678177527 1070040137352962517266291)
        ·
          refine ⟨1605060206029443775899437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070040137352962517266291 1605060206029443775899437)
          ·
            refine ⟨601897577261041415962289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1605060206029443775899437 601897577261041415962289)
            ·
              refine ⟨451423182945781061971717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601897577261041415962289 451423182945781061971717)
              ·
                refine ⟨84641846802333949119697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 451423182945781061971717 84641846802333949119697)
                ·
                  rfl

theorem cell20_556333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 4].length) (baseStart_556333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556333 prefixEnd_556333 := by exact prefixLift 556333
  have htrace : WordTrace (prefixWord ++ tailWord_556333) baseStart_556333 baseEnd_556333 := by
    simpa [prefixWord, tailWord_556333, baseEnd_556333] using wordTrace_append hprefix tailTrace_556333
  have hstable : (prefixWord ++ tailWord_556333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556333).length < 2 ^ (prefixWord ++ tailWord_556333).sum := by decide
  have hdescent : baseEnd_556333 < baseStart_556333 := by decide
  rcases family_descends (prefixWord ++ tailWord_556333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556337 : List Nat := [1, 2, 2, 3, 3, 1, 4, 4]
def baseStart_556337 : Nat := 118140960795 + 556337 * 2 ^ 59
def prefixEnd_556337 : Nat := 4983230072969 + 3 ^ 40 * 556337 * 2
def baseEnd_556337 : Nat := 84642455371998537075247

theorem tailTrace_556337 : CollatzResearch.WordTrace tailWord_556337 prefixEnd_556337 84642455371998537075247 := by
  unfold tailWord_556337
  simp only [CollatzResearch.WordTrace]
  refine ⟨20291277385493538640195265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13527518256995692426796843 20291277385493538640195265)
  ·
    refine ⟨15218458039120153980146449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20291277385493538640195265 15218458039120153980146449)
    ·
      refine ⟨11413843529340115485109837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15218458039120153980146449 11413843529340115485109837)
      ·
        refine ⟨4280191323502543306916189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11413843529340115485109837 4280191323502543306916189)
        ·
          refine ⟨1605071746313453740093571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4280191323502543306916189 1605071746313453740093571)
          ·
            refine ⟨2407607619470180610140357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605071746313453740093571 2407607619470180610140357)
            ·
              refine ⟨451426428650658864401317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2407607619470180610140357 451426428650658864401317)
              ·
                refine ⟨84642455371998537075247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 451426428650658864401317 84642455371998537075247)
                ·
                  rfl

theorem cell20_556337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 4].length) (baseStart_556337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556337 prefixEnd_556337 := by exact prefixLift 556337
  have htrace : WordTrace (prefixWord ++ tailWord_556337) baseStart_556337 baseEnd_556337 := by
    simpa [prefixWord, tailWord_556337, baseEnd_556337] using wordTrace_append hprefix tailTrace_556337
  have hstable : (prefixWord ++ tailWord_556337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556337).length < 2 ^ (prefixWord ++ tailWord_556337).sum := by decide
  have hdescent : baseEnd_556337 < baseStart_556337 := by decide
  rcases family_descends (prefixWord ++ tailWord_556337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556374 : List Nat := [5, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_556374 : Nat := 118140960795 + 556374 * 2 ^ 59
def prefixEnd_556374 : Nat := 4983230072969 + 3 ^ 40 * 556374 * 2
def baseEnd_556374 : Nat := 253944253924187926992257

theorem tailTrace_556374 : CollatzResearch.WordTrace tailWord_556374 prefixEnd_556374 253944253924187926992257 := by
  unfold tailWord_556374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1268289180397468372455761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13528417924239662639528117 1268289180397468372455761)
  ·
    refine ⟨951216885298101279341821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1268289180397468372455761 951216885298101279341821)
    ·
      refine ⟨356706331986787979753183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 951216885298101279341821 356706331986787979753183)
      ·
        refine ⟨535059497980181969629775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356706331986787979753183 535059497980181969629775)
        ·
          refine ⟨802589246970272954444663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535059497980181969629775 802589246970272954444663)
          ·
            refine ⟨1203883870455409431666995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802589246970272954444663 1203883870455409431666995)
            ·
              refine ⟨1805825805683114147500493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203883870455409431666995 1805825805683114147500493)
              ·
                refine ⟨677184677131167805312685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1805825805683114147500493 677184677131167805312685)
                ·
                  refine ⟨253944253924187926992257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 677184677131167805312685 253944253924187926992257)
                  ·
                    rfl

theorem cell20_556374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_556374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556374 prefixEnd_556374 := by exact prefixLift 556374
  have htrace : WordTrace (prefixWord ++ tailWord_556374) baseStart_556374 baseEnd_556374 := by
    simpa [prefixWord, tailWord_556374, baseEnd_556374] using wordTrace_append hprefix tailTrace_556374
  have hstable : (prefixWord ++ tailWord_556374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556374).length < 2 ^ (prefixWord ++ tailWord_556374).sum := by decide
  have hdescent : baseEnd_556374 < baseStart_556374 := by decide
  rcases family_descends (prefixWord ++ tailWord_556374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556396 : List Nat := [2, 2, 1, 1, 5, 1, 2, 6]
def baseStart_556396 : Nat := 118140960795 + 556396 * 2 ^ 59
def prefixEnd_556396 : Nat := 4983230072969 + 3 ^ 40 * 556396 * 2
def baseEnd_556396 : Nat := 84651431774551209419611

theorem tailTrace_556396 : CollatzResearch.WordTrace tailWord_556396 prefixEnd_556396 84651431774551209419611 := by
  unfold tailWord_556396
  simp only [CollatzResearch.WordTrace]
  refine ⟨10146714646139895858296521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13528952861519861144395361 10146714646139895858296521)
  ·
    refine ⟨7610035984604921893722391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10146714646139895858296521 7610035984604921893722391)
    ·
      refine ⟨11415053976907382840583587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7610035984604921893722391 11415053976907382840583587)
      ·
        refine ⟨17122580965361074260875381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11415053976907382840583587 17122580965361074260875381)
        ·
          refine ⟨1605241965502600711957067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17122580965361074260875381 1605241965502600711957067)
          ·
            refine ⟨2407862948253901067935601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605241965502600711957067 2407862948253901067935601)
            ·
              refine ⟨1805897211190425800951701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2407862948253901067935601 1805897211190425800951701)
              ·
                refine ⟨84651431774551209419611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1805897211190425800951701 84651431774551209419611)
                ·
                  rfl

theorem cell20_556396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_556396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556396 prefixEnd_556396 := by exact prefixLift 556396
  have htrace : WordTrace (prefixWord ++ tailWord_556396) baseStart_556396 baseEnd_556396 := by
    simpa [prefixWord, tailWord_556396, baseEnd_556396] using wordTrace_append hprefix tailTrace_556396
  have hstable : (prefixWord ++ tailWord_556396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556396).length < 2 ^ (prefixWord ++ tailWord_556396).sum := by decide
  have hdescent : baseEnd_556396 < baseStart_556396 := by decide
  rcases family_descends (prefixWord ++ tailWord_556396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556410 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_556410 : Nat := 118140960795 + 556410 * 2 ^ 59
def prefixEnd_556410 : Nat := 4983230072969 + 3 ^ 40 * 556410 * 2
def baseEnd_556410 : Nat := 253960685305131801792109

theorem tailTrace_556410 : CollatzResearch.WordTrace tailWord_556410 prefixEnd_556410 253960685305131801792109 := by
  unfold tailWord_556410
  simp only [CollatzResearch.WordTrace]
  refine ⟨5073484978557268026900671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13529293276152714738401789 5073484978557268026900671)
  ·
    refine ⟨7610227467835902040351007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5073484978557268026900671 7610227467835902040351007)
    ·
      refine ⟨11415341201753853060526511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7610227467835902040351007 11415341201753853060526511)
      ·
        refine ⟨17123011802630779590789767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11415341201753853060526511 17123011802630779590789767)
        ·
          refine ⟨25684517703946169386184651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17123011802630779590789767 25684517703946169386184651)
          ·
            refine ⟨38526776555919254079276977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25684517703946169386184651 38526776555919254079276977)
            ·
              refine ⟨28895082416939440559457733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38526776555919254079276977 28895082416939440559457733)
              ·
                refine ⟨5417827953176145104898325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28895082416939440559457733 5417827953176145104898325)
                ·
                  refine ⟨253960685305131801792109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5417827953176145104898325 253960685305131801792109)
                  ·
                    rfl

theorem cell20_556410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_556410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556410 prefixEnd_556410 := by exact prefixLift 556410
  have htrace : WordTrace (prefixWord ++ tailWord_556410) baseStart_556410 baseEnd_556410 := by
    simpa [prefixWord, tailWord_556410, baseEnd_556410] using wordTrace_append hprefix tailTrace_556410
  have hstable : (prefixWord ++ tailWord_556410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556410).length < 2 ^ (prefixWord ++ tailWord_556410).sum := by decide
  have hdescent : baseEnd_556410 < baseStart_556410 := by decide
  rcases family_descends (prefixWord ++ tailWord_556410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556420 : List Nat := [2, 3, 2, 1, 1, 3, 1, 4, 3]
def baseStart_556420 : Nat := 118140960795 + 556420 * 2 ^ 59
def prefixEnd_556420 : Nat := 4983230072969 + 3 ^ 40 * 556420 * 2
def baseEnd_556420 : Nat := 253965249577616211458735

theorem tailTrace_556420 : CollatzResearch.WordTrace tailWord_556420 prefixEnd_556420 253965249577616211458735 := by
  unfold tailWord_556420
  simp only [CollatzResearch.WordTrace]
  refine ⟨10147152322096421907733357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13529536429461895876977809 10147152322096421907733357)
  ·
    refine ⟨3805182120786158215400009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10147152322096421907733357 3805182120786158215400009)
    ·
      refine ⟨2853886590589618661550007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3805182120786158215400009 2853886590589618661550007)
      ·
        refine ⟨4280829885884427992325011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2853886590589618661550007 4280829885884427992325011)
        ·
          refine ⟨6421244828826641988487517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4280829885884427992325011 6421244828826641988487517)
          ·
            refine ⟨2407966810809990745682819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6421244828826641988487517 2407966810809990745682819)
            ·
              refine ⟨3611950216214986118524229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2407966810809990745682819 3611950216214986118524229)
              ·
                refine ⟨677240665540309897223293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3611950216214986118524229 677240665540309897223293)
                ·
                  refine ⟨253965249577616211458735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 677240665540309897223293 253965249577616211458735)
                  ·
                    rfl

theorem cell20_556420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_556420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556420 prefixEnd_556420 := by exact prefixLift 556420
  have htrace : WordTrace (prefixWord ++ tailWord_556420) baseStart_556420 baseEnd_556420 := by
    simpa [prefixWord, tailWord_556420, baseEnd_556420] using wordTrace_append hprefix tailTrace_556420
  have hstable : (prefixWord ++ tailWord_556420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556420).length < 2 ^ (prefixWord ++ tailWord_556420).sum := by decide
  have hdescent : baseEnd_556420 < baseStart_556420 := by decide
  rcases family_descends (prefixWord ++ tailWord_556420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556423 : List Nat := [1, 1, 4, 2, 2, 2, 4, 2, 2]
def baseStart_556423 : Nat := 118140960795 + 556423 * 2 ^ 59
def prefixEnd_556423 : Nat := 4983230072969 + 3 ^ 40 * 556423 * 2
def baseEnd_556423 : Nat := 253966618859361534358723

theorem tailTrace_556423 : CollatzResearch.WordTrace tailWord_556423 prefixEnd_556423 253966618859361534358723 := by
  unfold tailWord_556423
  simp only [CollatzResearch.WordTrace]
  refine ⟨20294414063181975327825923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13529609375454650218550615 20294414063181975327825923)
  ·
    refine ⟨30441621094772962991738885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20294414063181975327825923 30441621094772962991738885)
    ·
      refine ⟨5707803955269930560951041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30441621094772962991738885 5707803955269930560951041)
      ·
        refine ⟨4280852966452447920713281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5707803955269930560951041 4280852966452447920713281)
        ·
          refine ⟨3210639724839335940534961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4280852966452447920713281 3210639724839335940534961)
          ·
            refine ⟨2407979793629501955401221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3210639724839335940534961 2407979793629501955401221)
            ·
              refine ⟨451496211305531616637729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2407979793629501955401221 451496211305531616637729)
              ·
                refine ⟨338622158479148712478297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451496211305531616637729 338622158479148712478297)
                ·
                  refine ⟨253966618859361534358723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338622158479148712478297 253966618859361534358723)
                  ·
                    rfl

theorem cell20_556423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 2].length) (baseStart_556423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556423 prefixEnd_556423 := by exact prefixLift 556423
  have htrace : WordTrace (prefixWord ++ tailWord_556423) baseStart_556423 baseEnd_556423 := by
    simpa [prefixWord, tailWord_556423, baseEnd_556423] using wordTrace_append hprefix tailTrace_556423
  have hstable : (prefixWord ++ tailWord_556423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556423).length < 2 ^ (prefixWord ++ tailWord_556423).sum := by decide
  have hdescent : baseEnd_556423 < baseStart_556423 := by decide
  rcases family_descends (prefixWord ++ tailWord_556423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556430 : List Nat := [4, 1, 1, 4, 2, 2, 1, 5]
def baseStart_556430 : Nat := 118140960795 + 556430 * 2 ^ 59
def prefixEnd_556430 : Nat := 4983230072969 + 3 ^ 40 * 556430 * 2
def baseEnd_556430 : Nat := 84656604616700207041787

theorem tailTrace_556430 : CollatzResearch.WordTrace tailWord_556430 prefixEnd_556430 84656604616700207041787 := by
  unfold tailWord_556430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2536833671769576940416343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13529779582771077015553829 2536833671769576940416343)
  ·
    refine ⟨3805250507654365410624515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2536833671769576940416343 3805250507654365410624515)
    ·
      refine ⟨5707875761481548115936773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3805250507654365410624515 5707875761481548115936773)
      ·
        refine ⟨1070226705277790271738145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5707875761481548115936773 1070226705277790271738145)
        ·
          refine ⟨802670028958342703803609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1070226705277790271738145 802670028958342703803609)
          ·
            refine ⟨602002521718757027852707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802670028958342703803609 602002521718757027852707)
            ·
              refine ⟨903003782578135541779061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602002521718757027852707 903003782578135541779061)
              ·
                refine ⟨84656604616700207041787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 903003782578135541779061 84656604616700207041787)
                ·
                  rfl

theorem cell20_556430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_556430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556430 prefixEnd_556430 := by exact prefixLift 556430
  have htrace : WordTrace (prefixWord ++ tailWord_556430) baseStart_556430 baseEnd_556430 := by
    simpa [prefixWord, tailWord_556430, baseEnd_556430] using wordTrace_append hprefix tailTrace_556430
  have hstable : (prefixWord ++ tailWord_556430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556430).length < 2 ^ (prefixWord ++ tailWord_556430).sum := by decide
  have hdescent : baseEnd_556430 < baseStart_556430 := by decide
  rcases family_descends (prefixWord ++ tailWord_556430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556461 : List Nat := [1, 5, 2, 2, 1, 1, 1, 5, 2]
def baseStart_556461 : Nat := 118140960795 + 556461 * 2 ^ 59
def prefixEnd_556461 : Nat := 4983230072969 + 3 ^ 40 * 556461 * 2
def baseEnd_556461 : Nat := 253983963094802291091901

theorem tailTrace_556461 : CollatzResearch.WordTrace tailWord_556461 prefixEnd_556461 253983963094802291091901 := by
  unfold tailWord_556461
  simp only [CollatzResearch.WordTrace]
  refine ⟨20295800037044307817709237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13530533358029538545139491 20295800037044307817709237)
  ·
    refine ⟨1902731253472903857910241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20295800037044307817709237 1902731253472903857910241)
    ·
      refine ⟨1427048440104677893432681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1902731253472903857910241 1427048440104677893432681)
      ·
        refine ⟨1070286330078508420074511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1427048440104677893432681 1070286330078508420074511)
        ·
          refine ⟨1605429495117762630111767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070286330078508420074511 1605429495117762630111767)
          ·
            refine ⟨2408144242676643945167651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605429495117762630111767 2408144242676643945167651)
            ·
              refine ⟨3612216364014965917751477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408144242676643945167651 3612216364014965917751477)
              ·
                refine ⟨338645284126403054789201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3612216364014965917751477 338645284126403054789201)
                ·
                  refine ⟨253983963094802291091901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338645284126403054789201 253983963094802291091901)
                  ·
                    rfl

theorem cell20_556461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_556461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556461 prefixEnd_556461 := by exact prefixLift 556461
  have htrace : WordTrace (prefixWord ++ tailWord_556461) baseStart_556461 baseEnd_556461 := by
    simpa [prefixWord, tailWord_556461, baseEnd_556461] using wordTrace_append hprefix tailTrace_556461
  have hstable : (prefixWord ++ tailWord_556461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556461).length < 2 ^ (prefixWord ++ tailWord_556461).sum := by decide
  have hdescent : baseEnd_556461 < baseStart_556461 := by decide
  rcases family_descends (prefixWord ++ tailWord_556461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556534 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_556534 : Nat := 118140960795 + 556534 * 2 ^ 59
def prefixEnd_556534 : Nat := 4983230072969 + 3 ^ 40 * 556534 * 2
def baseEnd_556534 : Nat := 254017282283938481658269

theorem tailTrace_556534 : CollatzResearch.WordTrace tailWord_556534 prefixEnd_556534 254017282283938481658269 := by
  unfold tailWord_556534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1268653910361240080319791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13532308377186560856744437 1268653910361240080319791)
  ·
    refine ⟨1902980865541860120479687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1268653910361240080319791 1902980865541860120479687)
    ·
      refine ⟨2854471298312790180719531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1902980865541860120479687 2854471298312790180719531)
      ·
        refine ⟨4281706947469185271079297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2854471298312790180719531 4281706947469185271079297)
        ·
          refine ⟨3211280210601888953309473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4281706947469185271079297 3211280210601888953309473)
          ·
            refine ⟨2408460157951416714982105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3211280210601888953309473 2408460157951416714982105)
            ·
              refine ⟨1806345118463562536236579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2408460157951416714982105 1806345118463562536236579)
              ·
                refine ⟨2709517677695343804354869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1806345118463562536236579 2709517677695343804354869)
                ·
                  refine ⟨254017282283938481658269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2709517677695343804354869 254017282283938481658269)
                  ·
                    rfl

theorem cell20_556534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_556534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556534 prefixEnd_556534 := by exact prefixLift 556534
  have htrace : WordTrace (prefixWord ++ tailWord_556534) baseStart_556534 baseEnd_556534 := by
    simpa [prefixWord, tailWord_556534, baseEnd_556534] using wordTrace_append hprefix tailTrace_556534
  have hstable : (prefixWord ++ tailWord_556534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556534).length < 2 ^ (prefixWord ++ tailWord_556534).sum := by decide
  have hdescent : baseEnd_556534 < baseStart_556534 := by decide
  rcases family_descends (prefixWord ++ tailWord_556534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556541 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 4]
def baseStart_556541 : Nat := 118140960795 + 556541 * 2 ^ 59
def prefixEnd_556541 : Nat := 4983230072969 + 3 ^ 40 * 556541 * 2
def baseEnd_556541 : Nat := 254020477274677568424907

theorem tailTrace_556541 : CollatzResearch.WordTrace tailWord_556541 prefixEnd_556541 254020477274677568424907 := by
  unfold tailWord_556541
  simp only [CollatzResearch.WordTrace]
  refine ⟨20298717876754481480621477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13532478584502987653747651 20298717876754481480621477)
  ·
    refine ⟨3806009601891465277616527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20298717876754481480621477 3806009601891465277616527)
    ·
      refine ⟨5709014402837197916424791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3806009601891465277616527 5709014402837197916424791)
      ·
        refine ⟨8563521604255796874637187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5709014402837197916424791 8563521604255796874637187)
        ·
          refine ⟨12845282406383695311955781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8563521604255796874637187 12845282406383695311955781)
          ·
            refine ⟨2408490451196942870991709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12845282406383695311955781 2408490451196942870991709)
            ·
              refine ⟨903183919198853576621891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2408490451196942870991709 903183919198853576621891)
              ·
                refine ⟨1354775878798280364932837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 903183919198853576621891 1354775878798280364932837)
                ·
                  refine ⟨254020477274677568424907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1354775878798280364932837 254020477274677568424907)
                  ·
                    rfl

theorem cell20_556541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_556541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556541 prefixEnd_556541 := by exact prefixLift 556541
  have htrace : WordTrace (prefixWord ++ tailWord_556541) baseStart_556541 baseEnd_556541 := by
    simpa [prefixWord, tailWord_556541, baseEnd_556541] using wordTrace_append hprefix tailTrace_556541
  have hstable : (prefixWord ++ tailWord_556541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556541).length < 2 ^ (prefixWord ++ tailWord_556541).sum := by decide
  have hdescent : baseEnd_556541 < baseStart_556541 := by decide
  rcases family_descends (prefixWord ++ tailWord_556541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556551 : List Nat := [1, 1, 4, 3, 2, 1, 4, 1, 3]
def baseStart_556551 : Nat := 118140960795 + 556551 * 2 ^ 59
def prefixEnd_556551 : Nat := 4983230072969 + 3 ^ 40 * 556551 * 2
def baseEnd_556551 : Nat := 254025041547161978091533

theorem tailTrace_556551 : CollatzResearch.WordTrace tailWord_556551 prefixEnd_556551 254025041547161978091533 := by
  unfold tailWord_556551
  simp only [CollatzResearch.WordTrace]
  refine ⟨20299082606718253188485507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13532721737812168792323671 20299082606718253188485507)
  ·
    refine ⟨30448623910077379782728261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20299082606718253188485507 30448623910077379782728261)
    ·
      refine ⟨5709116983139508709261549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30448623910077379782728261 5709116983139508709261549)
      ·
        refine ⟨2140918868677315765973081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5709116983139508709261549 2140918868677315765973081)
        ·
          refine ⟨1605689151507986824479811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2140918868677315765973081 1605689151507986824479811)
          ·
            refine ⟨2408533727261980236719717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605689151507986824479811 2408533727261980236719717)
            ·
              refine ⟨451600073861621294384947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2408533727261980236719717 451600073861621294384947)
              ·
                refine ⟨677400110792431941577421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451600073861621294384947 677400110792431941577421)
                ·
                  refine ⟨254025041547161978091533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 677400110792431941577421 254025041547161978091533)
                  ·
                    rfl

theorem cell20_556551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 3].length) (baseStart_556551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556551 prefixEnd_556551 := by exact prefixLift 556551
  have htrace : WordTrace (prefixWord ++ tailWord_556551) baseStart_556551 baseEnd_556551 := by
    simpa [prefixWord, tailWord_556551, baseEnd_556551] using wordTrace_append hprefix tailTrace_556551
  have hstable : (prefixWord ++ tailWord_556551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556551).length < 2 ^ (prefixWord ++ tailWord_556551).sum := by decide
  have hdescent : baseEnd_556551 < baseStart_556551 := by decide
  rcases family_descends (prefixWord ++ tailWord_556551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556624 : List Nat := [2, 1, 1, 1, 1, 3, 7, 4]
def baseStart_556624 : Nat := 118140960795 + 556624 * 2 ^ 59
def prefixEnd_556624 : Nat := 4983230072969 + 3 ^ 40 * 556624 * 2
def baseEnd_556624 : Nat := 84686120245432722885967

theorem tailTrace_556624 : CollatzResearch.WordTrace tailWord_556624 prefixEnd_556624 84686120245432722885967 := by
  unfold tailWord_556624
  simp only [CollatzResearch.WordTrace]
  refine ⟨10150872567726893327946463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13534496756969191103928617 10150872567726893327946463)
  ·
    refine ⟨15226308851590339991919695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10150872567726893327946463 15226308851590339991919695)
    ·
      refine ⟨22839463277385509987879543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15226308851590339991919695 22839463277385509987879543)
      ·
        refine ⟨34259194916078264981819315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22839463277385509987879543 34259194916078264981819315)
        ·
          refine ⟨51388792374117397472728973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34259194916078264981819315 51388792374117397472728973)
          ·
            refine ⟨19270797140294024052273365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51388792374117397472728973 19270797140294024052273365)
            ·
              refine ⟨451659307975641188725157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19270797140294024052273365 451659307975641188725157)
              ·
                refine ⟨84686120245432722885967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 451659307975641188725157 84686120245432722885967)
                ·
                  rfl

theorem cell20_556624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_556624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556624 prefixEnd_556624 := by exact prefixLift 556624
  have htrace : WordTrace (prefixWord ++ tailWord_556624) baseStart_556624 baseEnd_556624 := by
    simpa [prefixWord, tailWord_556624, baseEnd_556624] using wordTrace_append hprefix tailTrace_556624
  have hstable : (prefixWord ++ tailWord_556624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556624).length < 2 ^ (prefixWord ++ tailWord_556624).sum := by decide
  have hdescent : baseEnd_556624 < baseStart_556624 := by decide
  rcases family_descends (prefixWord ++ tailWord_556624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556648 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 5]
def baseStart_556648 : Nat := 118140960795 + 556648 * 2 ^ 59
def prefixEnd_556648 : Nat := 4983230072969 + 3 ^ 40 * 556648 * 2
def baseEnd_556648 : Nat := 254069314990260751857803

theorem tailTrace_556648 : CollatzResearch.WordTrace tailWord_556648 prefixEnd_556648 254069314990260751857803 := by
  unfold tailWord_556648
  simp only [CollatzResearch.WordTrace]
  refine ⟨10151310243683419377383299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13535080324911225836511065 10151310243683419377383299)
  ·
    refine ⟨15226965365525129066074949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10151310243683419377383299 15226965365525129066074949)
    ·
      refine ⟨2855056006035961699889053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15226965365525129066074949 2855056006035961699889053)
      ·
        refine ⟨1070646002263485637458395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2855056006035961699889053 1070646002263485637458395)
        ·
          refine ⟨1605969003395228456187593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070646002263485637458395 1605969003395228456187593)
          ·
            refine ⟨1204476752546421342140695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1605969003395228456187593 1204476752546421342140695)
            ·
              refine ⟨1806715128819632013211043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204476752546421342140695 1806715128819632013211043)
              ·
                refine ⟨2710072693229448019816565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1806715128819632013211043 2710072693229448019816565)
                ·
                  refine ⟨254069314990260751857803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2710072693229448019816565 254069314990260751857803)
                  ·
                    rfl

theorem cell20_556648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_556648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556648 prefixEnd_556648 := by exact prefixLift 556648
  have htrace : WordTrace (prefixWord ++ tailWord_556648) baseStart_556648 baseEnd_556648 := by
    simpa [prefixWord, tailWord_556648, baseEnd_556648] using wordTrace_append hprefix tailTrace_556648
  have hstable : (prefixWord ++ tailWord_556648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556648).length < 2 ^ (prefixWord ++ tailWord_556648).sum := by decide
  have hdescent : baseEnd_556648 < baseStart_556648 := by decide
  rcases family_descends (prefixWord ++ tailWord_556648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556679 : List Nat := [1, 1, 4, 2, 1, 5, 2, 4]
def baseStart_556679 : Nat := 118140960795 + 556679 * 2 ^ 59
def prefixEnd_556679 : Nat := 4983230072969 + 3 ^ 40 * 556679 * 2
def baseEnd_556679 : Nat := 84694488078320807274781

theorem tailTrace_556679 : CollatzResearch.WordTrace tailWord_556679 prefixEnd_556679 84694488078320807274781 := by
  unfold tailWord_556679
  simp only [CollatzResearch.WordTrace]
  refine ⟨20303751150254531049145091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13535834100169687366096727 20303751150254531049145091)
  ·
    refine ⟨30455626725381796573717637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20303751150254531049145091 30455626725381796573717637)
    ·
      refine ⟨5710430011009086857572057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30455626725381796573717637 5710430011009086857572057)
      ·
        refine ⟨4282822508256815143179043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5710430011009086857572057 4282822508256815143179043)
        ·
          refine ⟨6424233762385222714768565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4282822508256815143179043 6424233762385222714768565)
          ·
            refine ⟨602271915223614629509553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6424233762385222714768565 602271915223614629509553)
            ·
              refine ⟨451703936417710972132165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602271915223614629509553 451703936417710972132165)
              ·
                refine ⟨84694488078320807274781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 451703936417710972132165 84694488078320807274781)
                ·
                  rfl

theorem cell20_556679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 4].length) (baseStart_556679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556679 prefixEnd_556679 := by exact prefixLift 556679
  have htrace : WordTrace (prefixWord ++ tailWord_556679) baseStart_556679 baseEnd_556679 := by
    simpa [prefixWord, tailWord_556679, baseEnd_556679] using wordTrace_append hprefix tailTrace_556679
  have hstable : (prefixWord ++ tailWord_556679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556679).length < 2 ^ (prefixWord ++ tailWord_556679).sum := by decide
  have hdescent : baseEnd_556679 < baseStart_556679 := by decide
  rcases family_descends (prefixWord ++ tailWord_556679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556683 : List Nat := [1, 1, 1, 1, 4, 1, 5, 6]
def baseStart_556683 : Nat := 118140960795 + 556683 * 2 ^ 59
def prefixEnd_556683 : Nat := 4983230072969 + 3 ^ 40 * 556683 * 2
def baseEnd_556683 : Nat := 84695096647985395230331

theorem tailTrace_556683 : CollatzResearch.WordTrace tailWord_556683 prefixEnd_556683 84695096647985395230331 := by
  unfold tailWord_556683
  simp only [CollatzResearch.WordTrace]
  refine ⟨20303897042240039732290703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13535931361493359821527135 20303897042240039732290703)
  ·
    refine ⟨30455845563360059598436055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20303897042240039732290703 30455845563360059598436055)
    ·
      refine ⟨45683768345040089397654083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30455845563360059598436055 45683768345040089397654083)
      ·
        refine ⟨68525652517560134096481125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45683768345040089397654083 68525652517560134096481125)
        ·
          refine ⟨12848559847042525143090211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68525652517560134096481125 12848559847042525143090211)
          ·
            refine ⟨19272839770563787714635317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12848559847042525143090211 19272839770563787714635317)
            ·
              refine ⟨1806828728490355098247061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19272839770563787714635317 1806828728490355098247061)
              ·
                refine ⟨84695096647985395230331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1806828728490355098247061 84695096647985395230331)
                ·
                  rfl

theorem cell20_556683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 6].length) (baseStart_556683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556683 prefixEnd_556683 := by exact prefixLift 556683
  have htrace : WordTrace (prefixWord ++ tailWord_556683) baseStart_556683 baseEnd_556683 := by
    simpa [prefixWord, tailWord_556683, baseEnd_556683] using wordTrace_append hprefix tailTrace_556683
  have hstable : (prefixWord ++ tailWord_556683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556683).length < 2 ^ (prefixWord ++ tailWord_556683).sum := by decide
  have hdescent : baseEnd_556683 < baseStart_556683 := by decide
  rcases family_descends (prefixWord ++ tailWord_556683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556706 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 4]
def baseStart_556706 : Nat := 118140960795 + 556706 * 2 ^ 59
def prefixEnd_556706 : Nat := 4983230072969 + 3 ^ 40 * 556706 * 2
def baseEnd_556706 : Nat := 254095787770670327924233

theorem tailTrace_556706 : CollatzResearch.WordTrace tailWord_556706 prefixEnd_556706 254095787770670327924233 := by
  unfold tailWord_556706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5076183980289178665094493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13536490614104476440251981 5076183980289178665094493)
  ·
    refine ⟨1903568992608441999410435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5076183980289178665094493 1903568992608441999410435)
    ·
      refine ⟨2855353488912662999115653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1903568992608441999410435 2855353488912662999115653)
      ·
        refine ⟨535378779171124312334185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2855353488912662999115653 535378779171124312334185)
        ·
          refine ⟨401534084378343234250639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 535378779171124312334185 401534084378343234250639)
          ·
            refine ⟨602301126567514851375959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401534084378343234250639 602301126567514851375959)
            ·
              refine ⟨903451689851272277063939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602301126567514851375959 903451689851272277063939)
              ·
                refine ⟨1355177534776908415595909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 903451689851272277063939 1355177534776908415595909)
                ·
                  refine ⟨254095787770670327924233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1355177534776908415595909 254095787770670327924233)
                  ·
                    rfl

theorem cell20_556706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_556706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556706 prefixEnd_556706 := by exact prefixLift 556706
  have htrace : WordTrace (prefixWord ++ tailWord_556706) baseStart_556706 baseEnd_556706 := by
    simpa [prefixWord, tailWord_556706, baseEnd_556706] using wordTrace_append hprefix tailTrace_556706
  have hstable : (prefixWord ++ tailWord_556706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556706).length < 2 ^ (prefixWord ++ tailWord_556706).sum := by decide
  have hdescent : baseEnd_556706 < baseStart_556706 := by decide
  rcases family_descends (prefixWord ++ tailWord_556706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556707 : List Nat := [1, 1, 1, 4, 1, 1, 4, 4, 3]
def baseStart_556707 : Nat := 118140960795 + 556707 * 2 ^ 59
def prefixEnd_556707 : Nat := 4983230072969 + 3 ^ 40 * 556707 * 2
def baseEnd_556707 : Nat := 254096244197918768890895

theorem tailTrace_556707 : CollatzResearch.WordTrace tailWord_556707 prefixEnd_556707 254096244197918768890895 := by
  unfold tailWord_556707
  simp only [CollatzResearch.WordTrace]
  refine ⟨20304772394153091831164375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13536514929435394554109583 20304772394153091831164375)
  ·
    refine ⟨30457158591229637746746563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20304772394153091831164375 30457158591229637746746563)
    ·
      refine ⟨45685737886844456620119845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30457158591229637746746563 45685737886844456620119845)
      ·
        refine ⟨8566075853783335616272471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45685737886844456620119845 8566075853783335616272471)
        ·
          refine ⟨12849113780675003424408707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8566075853783335616272471 12849113780675003424408707)
          ·
            refine ⟨19273670671012505136613061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12849113780675003424408707 19273670671012505136613061)
            ·
              refine ⟨3613813250814844713114949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19273670671012505136613061 3613813250814844713114949)
              ·
                refine ⟨677589984527783383709053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3613813250814844713114949 677589984527783383709053)
                ·
                  refine ⟨254096244197918768890895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 677589984527783383709053 254096244197918768890895)
                  ·
                    rfl

theorem cell20_556707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 3].length) (baseStart_556707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556707 prefixEnd_556707 := by exact prefixLift 556707
  have htrace : WordTrace (prefixWord ++ tailWord_556707) baseStart_556707 baseEnd_556707 := by
    simpa [prefixWord, tailWord_556707, baseEnd_556707] using wordTrace_append hprefix tailTrace_556707
  have hstable : (prefixWord ++ tailWord_556707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556707).length < 2 ^ (prefixWord ++ tailWord_556707).sum := by decide
  have hdescent : baseEnd_556707 < baseStart_556707 := by decide
  rcases family_descends (prefixWord ++ tailWord_556707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556762 : List Nat := [3, 1, 1, 2, 2, 4, 2, 2, 3]
def baseStart_556762 : Nat := 118140960795 + 556762 * 2 ^ 59
def prefixEnd_556762 : Nat := 4983230072969 + 3 ^ 40 * 556762 * 2
def baseEnd_556762 : Nat := 254121347696583022057337

theorem tailTrace_556762 : CollatzResearch.WordTrace tailWord_556762 prefixEnd_556762 254121347696583022057337 := by
  unfold tailWord_556762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5076694602238459056104135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13537852272635890816277693 5076694602238459056104135)
  ·
    refine ⟨7615041903357688584156203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5076694602238459056104135 7615041903357688584156203)
    ·
      refine ⟨11422562855036532876234305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7615041903357688584156203 11422562855036532876234305)
      ·
        refine ⟨8566922141277399657175729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11422562855036532876234305 8566922141277399657175729)
        ·
          refine ⟨6425191605958049742881797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8566922141277399657175729 6425191605958049742881797)
          ·
            refine ⟨1204723426117134326790337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6425191605958049742881797 1204723426117134326790337)
            ·
              refine ⟨903542569587850745092753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1204723426117134326790337 903542569587850745092753)
              ·
                refine ⟨677656927190888058819565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 903542569587850745092753 677656927190888058819565)
                ·
                  refine ⟨254121347696583022057337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 677656927190888058819565 254121347696583022057337)
                  ·
                    rfl

theorem cell20_556762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_556762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556762 prefixEnd_556762 := by exact prefixLift 556762
  have htrace : WordTrace (prefixWord ++ tailWord_556762) baseStart_556762 baseEnd_556762 := by
    simpa [prefixWord, tailWord_556762, baseEnd_556762] using wordTrace_append hprefix tailTrace_556762
  have hstable : (prefixWord ++ tailWord_556762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556762).length < 2 ^ (prefixWord ++ tailWord_556762).sum := by decide
  have hdescent : baseEnd_556762 < baseStart_556762 := by decide
  rcases family_descends (prefixWord ++ tailWord_556762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556776 : List Nat := [2, 1, 4, 1, 3, 1, 3, 5]
def baseStart_556776 : Nat := 118140960795 + 556776 * 2 ^ 59
def prefixEnd_556776 : Nat := 4983230072969 + 3 ^ 40 * 556776 * 2
def baseEnd_556776 : Nat := 84709245892687065196871

theorem tailTrace_556776 : CollatzResearch.WordTrace tailWord_556776 prefixEnd_556776 84709245892687065196871 := by
  unfold tailWord_556776
  simp only [CollatzResearch.WordTrace]
  refine ⟨10153644515451558307713091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13538192687268744410284121 10153644515451558307713091)
  ·
    refine ⟨15230466773177337461569637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10153644515451558307713091 15230466773177337461569637)
    ·
      refine ⟨2855712519970750774044307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15230466773177337461569637 2855712519970750774044307)
      ·
        refine ⟨4283568779956126161066461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2855712519970750774044307 4283568779956126161066461)
        ·
          refine ⟨1606338292483547310399923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4283568779956126161066461 1606338292483547310399923)
          ·
            refine ⟨2409507438725320965599885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1606338292483547310399923 2409507438725320965599885)
            ·
              refine ⟨903565289521995362099957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2409507438725320965599885 903565289521995362099957)
              ·
                refine ⟨84709245892687065196871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 903565289521995362099957 84709245892687065196871)
                ·
                  rfl

theorem cell20_556776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_556776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556776 prefixEnd_556776 := by exact prefixLift 556776
  have htrace : WordTrace (prefixWord ++ tailWord_556776) baseStart_556776 baseEnd_556776 := by
    simpa [prefixWord, tailWord_556776, baseEnd_556776] using wordTrace_append hprefix tailTrace_556776
  have hstable : (prefixWord ++ tailWord_556776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556776).length < 2 ^ (prefixWord ++ tailWord_556776).sum := by decide
  have hdescent : baseEnd_556776 < baseStart_556776 := by decide
  rcases family_descends (prefixWord ++ tailWord_556776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556783 : List Nat := [1, 1, 2, 1, 5, 1, 1, 5, 3]
def baseStart_556783 : Nat := 118140960795 + 556783 * 2 ^ 59
def prefixEnd_556783 : Nat := 4983230072969 + 3 ^ 40 * 556783 * 2
def baseEnd_556783 : Nat := 254130932668800282357251

theorem tailTrace_556783 : CollatzResearch.WordTrace tailWord_556783 prefixEnd_556783 254130932668800282357251 := by
  unfold tailWord_556783
  simp only [CollatzResearch.WordTrace]
  refine ⟨20307544341877756810931003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13538362894585171207287335 20307544341877756810931003)
  ·
    refine ⟨30461316512816635216396505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20307544341877756810931003 30461316512816635216396505)
    ·
      refine ⟨22845987384612476412297379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30461316512816635216396505 22845987384612476412297379)
      ·
        refine ⟨34268981076918714618446069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22845987384612476412297379 34268981076918714618446069)
        ·
          refine ⟨3212716975961129495479319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34268981076918714618446069 3212716975961129495479319)
          ·
            refine ⟨4819075463941694243218979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3212716975961129495479319 4819075463941694243218979)
            ·
              refine ⟨7228613195912541364828469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4819075463941694243218979 7228613195912541364828469)
              ·
                refine ⟨677682487116800752952669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7228613195912541364828469 677682487116800752952669)
                ·
                  refine ⟨254130932668800282357251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 677682487116800752952669 254130932668800282357251)
                  ·
                    rfl

theorem cell20_556783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 3].length) (baseStart_556783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556783 prefixEnd_556783 := by exact prefixLift 556783
  have htrace : WordTrace (prefixWord ++ tailWord_556783) baseStart_556783 baseEnd_556783 := by
    simpa [prefixWord, tailWord_556783, baseEnd_556783] using wordTrace_append hprefix tailTrace_556783
  have hstable : (prefixWord ++ tailWord_556783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556783).length < 2 ^ (prefixWord ++ tailWord_556783).sum := by decide
  have hdescent : baseEnd_556783 < baseStart_556783 := by decide
  rcases family_descends (prefixWord ++ tailWord_556783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556806 : List Nat := [6, 2, 2, 1, 1, 1, 7]
def baseStart_556806 : Nat := 118140960795 + 556806 * 2 ^ 59
def prefixEnd_556806 : Nat := 4983230072969 + 3 ^ 40 * 556806 * 2
def baseEnd_556806 : Nat := 28237936721723824954499

theorem tailTrace_556806 : CollatzResearch.WordTrace tailWord_556806 prefixEnd_556806 28237936721723824954499 := by
  unfold tailWord_556806
  simp only [CollatzResearch.WordTrace]
  refine ⟨634636975649825991844321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13538922147196287826012181 634636975649825991844321)
  ·
    refine ⟨475977731737369493883241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 634636975649825991844321 475977731737369493883241)
    ·
      refine ⟨356983298803027120412431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 475977731737369493883241 356983298803027120412431)
      ·
        refine ⟨535474948204540680618647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356983298803027120412431 535474948204540680618647)
        ·
          refine ⟨803212422306811020927971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535474948204540680618647 803212422306811020927971)
          ·
            refine ⟨1204818633460216531391957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803212422306811020927971 1204818633460216531391957)
            ·
              refine ⟨28237936721723824954499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1204818633460216531391957 28237936721723824954499)
              ·
                rfl

theorem cell20_556806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 7].length) (baseStart_556806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556806 prefixEnd_556806 := by exact prefixLift 556806
  have htrace : WordTrace (prefixWord ++ tailWord_556806) baseStart_556806 baseEnd_556806 := by
    simpa [prefixWord, tailWord_556806, baseEnd_556806] using wordTrace_append hprefix tailTrace_556806
  have hstable : (prefixWord ++ tailWord_556806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556806).length < 2 ^ (prefixWord ++ tailWord_556806).sum := by decide
  have hdescent : baseEnd_556806 < baseStart_556806 := by decide
  rcases family_descends (prefixWord ++ tailWord_556806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556813 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 5]
def baseStart_556813 : Nat := 118140960795 + 556813 * 2 ^ 59
def prefixEnd_556813 : Nat := 4983230072969 + 3 ^ 40 * 556813 * 2
def baseEnd_556813 : Nat := 254144625486253511357129

theorem tailTrace_556813 : CollatzResearch.WordTrace tailWord_556813 prefixEnd_556813 254144625486253511357129 := by
  unfold tailWord_556813
  simp only [CollatzResearch.WordTrace]
  refine ⟨20308638531769071934523093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13539092354512714623015395 20308638531769071934523093)
  ·
    refine ⟨475983715588337623465385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 20308638531769071934523093 475983715588337623465385)
    ·
      refine ⟨356987786691253217599039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 475983715588337623465385 356987786691253217599039)
      ·
        refine ⟨535481680036879826398559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356987786691253217599039 535481680036879826398559)
        ·
          refine ⟨803222520055319739597839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535481680036879826398559 803222520055319739597839)
          ·
            refine ⟨1204833780082979609396759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803222520055319739597839 1204833780082979609396759)
            ·
              refine ⟨1807250670124469414095139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204833780082979609396759 1807250670124469414095139)
              ·
                refine ⟨2710876005186704121142709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1807250670124469414095139 2710876005186704121142709)
                ·
                  refine ⟨254144625486253511357129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2710876005186704121142709 254144625486253511357129)
                  ·
                    rfl

theorem cell20_556813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_556813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556813 prefixEnd_556813 := by exact prefixLift 556813
  have htrace : WordTrace (prefixWord ++ tailWord_556813) baseStart_556813 baseEnd_556813 := by
    simpa [prefixWord, tailWord_556813, baseEnd_556813] using wordTrace_append hprefix tailTrace_556813
  have hstable : (prefixWord ++ tailWord_556813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556813).length < 2 ^ (prefixWord ++ tailWord_556813).sum := by decide
  have hdescent : baseEnd_556813 < baseStart_556813 := by decide
  rcases family_descends (prefixWord ++ tailWord_556813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556820 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 4]
def baseStart_556820 : Nat := 118140960795 + 556820 * 2 ^ 59
def prefixEnd_556820 : Nat := 4983230072969 + 3 ^ 40 * 556820 * 2
def baseEnd_556820 : Nat := 254147820476992598123767

theorem tailTrace_556820 : CollatzResearch.WordTrace tailWord_556820 prefixEnd_556820 254147820476992598123767 := by
  unfold tailWord_556820
  simp only [CollatzResearch.WordTrace]
  refine ⟨10154446921371856065013957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13539262561829141420018609 10154446921371856065013957)
  ·
    refine ⟨1903958797757223012190117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10154446921371856065013957 1903958797757223012190117)
    ·
      refine ⟨356992274579479314785647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1903958797757223012190117 356992274579479314785647)
      ·
        refine ⟨535488411869218972178471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356992274579479314785647 535488411869218972178471)
        ·
          refine ⟨803232617803828458267707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535488411869218972178471 803232617803828458267707)
          ·
            refine ⟨1204848926705742687401561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803232617803828458267707 1204848926705742687401561)
            ·
              refine ⟨903636695029307015551171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1204848926705742687401561 903636695029307015551171)
              ·
                refine ⟨1355455042543960523326757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 903636695029307015551171 1355455042543960523326757)
                ·
                  refine ⟨254147820476992598123767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1355455042543960523326757 254147820476992598123767)
                  ·
                    rfl

theorem cell20_556820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_556820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556820 prefixEnd_556820 := by exact prefixLift 556820
  have htrace : WordTrace (prefixWord ++ tailWord_556820) baseStart_556820 baseEnd_556820 := by
    simpa [prefixWord, tailWord_556820, baseEnd_556820] using wordTrace_append hprefix tailTrace_556820
  have hstable : (prefixWord ++ tailWord_556820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556820).length < 2 ^ (prefixWord ++ tailWord_556820).sum := by decide
  have hdescent : baseEnd_556820 < baseStart_556820 := by decide
  rcases family_descends (prefixWord ++ tailWord_556820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556821 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 5]
def baseStart_556821 : Nat := 118140960795 + 556821 * 2 ^ 59
def prefixEnd_556821 : Nat := 4983230072969 + 3 ^ 40 * 556821 * 2
def baseEnd_556821 : Nat := 254148276904241039090429

theorem tailTrace_556821 : CollatzResearch.WordTrace tailWord_556821 prefixEnd_556821 254148276904241039090429 := by
  unfold tailWord_556821
  simp only [CollatzResearch.WordTrace]
  refine ⟨20308930315740089300814317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13539286877160059533876211 20308930315740089300814317)
  ·
    refine ⟨7615848868402533487805369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20308930315740089300814317 7615848868402533487805369)
    ·
      refine ⟨5711886651301900115854027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7615848868402533487805369 5711886651301900115854027)
      ·
        refine ⟨8567829976952850173781041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5711886651301900115854027 8567829976952850173781041)
        ·
          refine ⟨6425872482714637630335781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8567829976952850173781041 6425872482714637630335781)
          ·
            refine ⟨1204851090508994555687959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6425872482714637630335781 1204851090508994555687959)
            ·
              refine ⟨1807276635763491833531939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204851090508994555687959 1807276635763491833531939)
              ·
                refine ⟨2710914953645237750297909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1807276635763491833531939 2710914953645237750297909)
                ·
                  refine ⟨254148276904241039090429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2710914953645237750297909 254148276904241039090429)
                  ·
                    rfl

theorem cell20_556821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_556821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556821 prefixEnd_556821 := by exact prefixLift 556821
  have htrace : WordTrace (prefixWord ++ tailWord_556821) baseStart_556821 baseEnd_556821 := by
    simpa [prefixWord, tailWord_556821, baseEnd_556821] using wordTrace_append hprefix tailTrace_556821
  have hstable : (prefixWord ++ tailWord_556821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556821).length < 2 ^ (prefixWord ++ tailWord_556821).sum := by decide
  have hdescent : baseEnd_556821 < baseStart_556821 := by decide
  rcases family_descends (prefixWord ++ tailWord_556821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556897 : List Nat := [1, 2, 3, 1, 1, 1, 5, 3, 3]
def baseStart_556897 : Nat := 118140960795 + 556897 * 2 ^ 59
def prefixEnd_556897 : Nat := 4983230072969 + 3 ^ 40 * 556897 * 2
def baseEnd_556897 : Nat := 254182965375122552556785

theorem tailTrace_556897 : CollatzResearch.WordTrace tailWord_556897 prefixEnd_556897 254182965375122552556785 := by
  unfold tailWord_556897
  simp only [CollatzResearch.WordTrace]
  refine ⟨20311702263464754280580945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13541134842309836187053963 20311702263464754280580945)
  ·
    refine ⟨15233776697598565710435709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20311702263464754280580945 15233776697598565710435709)
    ·
      refine ⟨5712666261599462141413391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15233776697598565710435709 5712666261599462141413391)
      ·
        refine ⟨8568999392399193212120087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5712666261599462141413391 8568999392399193212120087)
        ·
          refine ⟨12853499088598789818180131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8568999392399193212120087 12853499088598789818180131)
          ·
            refine ⟨19280248632898184727270197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12853499088598789818180131 19280248632898184727270197)
            ·
              refine ⟨1807523309334204818181581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19280248632898184727270197 1807523309334204818181581)
              ·
                refine ⟨677821241000326806818093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1807523309334204818181581 677821241000326806818093)
                ·
                  refine ⟨254182965375122552556785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 677821241000326806818093 254182965375122552556785)
                  ·
                    rfl

theorem cell20_556897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_556897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556897 prefixEnd_556897 := by exact prefixLift 556897
  have htrace : WordTrace (prefixWord ++ tailWord_556897) baseStart_556897 baseEnd_556897 := by
    simpa [prefixWord, tailWord_556897, baseEnd_556897] using wordTrace_append hprefix tailTrace_556897
  have hstable : (prefixWord ++ tailWord_556897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556897).length < 2 ^ (prefixWord ++ tailWord_556897).sum := by decide
  have hdescent : baseEnd_556897 < baseStart_556897 := by decide
  rcases family_descends (prefixWord ++ tailWord_556897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556904 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 6]
def baseStart_556904 : Nat := 118140960795 + 556904 * 2 ^ 59
def prefixEnd_556904 : Nat := 4983230072969 + 3 ^ 40 * 556904 * 2
def baseEnd_556904 : Nat := 254186160365861639323423

theorem tailTrace_556904 : CollatzResearch.WordTrace tailWord_556904 prefixEnd_556904 254186160365861639323423 := by
  unfold tailWord_556904
  simp only [CollatzResearch.WordTrace]
  refine ⟨10155978787219697238042883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13541305049626262984057177 10155978787219697238042883)
  ·
    refine ⟨15233968180829545857064325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10155978787219697238042883 15233968180829545857064325)
    ·
      refine ⟨2856369033905539848199561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15233968180829545857064325 2856369033905539848199561)
      ·
        refine ⟨2142276775429154886149671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2856369033905539848199561 2142276775429154886149671)
        ·
          refine ⟨3213415163143732329224507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2142276775429154886149671 3213415163143732329224507)
          ·
            refine ⟨4820122744715598493836761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3213415163143732329224507 4820122744715598493836761)
            ·
              refine ⟨3615092058536698870377571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4820122744715598493836761 3615092058536698870377571)
              ·
                refine ⟨5422638087805048305566357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3615092058536698870377571 5422638087805048305566357)
                ·
                  refine ⟨254186160365861639323423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5422638087805048305566357 254186160365861639323423)
                  ·
                    rfl

theorem cell20_556904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_556904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556904 prefixEnd_556904 := by exact prefixLift 556904
  have htrace : WordTrace (prefixWord ++ tailWord_556904) baseStart_556904 baseEnd_556904 := by
    simpa [prefixWord, tailWord_556904, baseEnd_556904] using wordTrace_append hprefix tailTrace_556904
  have hstable : (prefixWord ++ tailWord_556904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556904).length < 2 ^ (prefixWord ++ tailWord_556904).sum := by decide
  have hdescent : baseEnd_556904 < baseStart_556904 := by decide
  rcases family_descends (prefixWord ++ tailWord_556904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556921 : List Nat := [1, 2, 1, 3, 2, 2, 2, 5, 2]
def baseStart_556921 : Nat := 118140960795 + 556921 * 2 ^ 59
def prefixEnd_556921 : Nat := 4983230072969 + 3 ^ 40 * 556921 * 2
def baseEnd_556921 : Nat := 254193919629085135756687

theorem tailTrace_556921 : CollatzResearch.WordTrace tailWord_556921 prefixEnd_556921 254193919629085135756687 := by
  unfold tailWord_556921
  simp only [CollatzResearch.WordTrace]
  refine ⟨20312577615377806379454617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13541718410251870919636411 20312577615377806379454617)
  ·
    refine ⟨15234433211533354784590963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20312577615377806379454617 15234433211533354784590963)
    ·
      refine ⟨22851649817300032176886445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15234433211533354784590963 22851649817300032176886445)
      ·
        refine ⟨8569368681487512066332417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22851649817300032176886445 8569368681487512066332417)
        ·
          refine ⟨6427026511115634049749313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8569368681487512066332417 6427026511115634049749313)
          ·
            refine ⟨4820269883336725537311985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6427026511115634049749313 4820269883336725537311985)
            ·
              refine ⟨3615202412502544152983989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4820269883336725537311985 3615202412502544152983989)
              ·
                refine ⟨338925226172113514342249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3615202412502544152983989 338925226172113514342249)
                ·
                  refine ⟨254193919629085135756687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338925226172113514342249 254193919629085135756687)
                  ·
                    rfl

theorem cell20_556921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 2].length) (baseStart_556921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556921 prefixEnd_556921 := by exact prefixLift 556921
  have htrace : WordTrace (prefixWord ++ tailWord_556921) baseStart_556921 baseEnd_556921 := by
    simpa [prefixWord, tailWord_556921, baseEnd_556921] using wordTrace_append hprefix tailTrace_556921
  have hstable : (prefixWord ++ tailWord_556921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556921).length < 2 ^ (prefixWord ++ tailWord_556921).sum := by decide
  have hdescent : baseEnd_556921 < baseStart_556921 := by decide
  rcases family_descends (prefixWord ++ tailWord_556921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556959 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 4]
def baseStart_556959 : Nat := 118140960795 + 556959 * 2 ^ 59
def prefixEnd_556959 : Nat := 4983230072969 + 3 ^ 40 * 556959 * 2
def baseEnd_556959 : Nat := 254211263864525892489865

theorem tailTrace_556959 : CollatzResearch.WordTrace tailWord_556959 prefixEnd_556959 254211263864525892489865 := by
  unfold tailWord_556959
  simp only [CollatzResearch.WordTrace]
  refine ⟨20313963589240138869337931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13542642392826759246225287 20313963589240138869337931)
  ·
    refine ⟨30470945383860208304006897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20313963589240138869337931 30470945383860208304006897)
    ·
      refine ⟨22853209037895156228005173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30470945383860208304006897 22853209037895156228005173)
      ·
        refine ⟨2142488347302670896375485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22853209037895156228005173 2142488347302670896375485)
        ·
          refine ⟨803433130238501586140807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2142488347302670896375485 803433130238501586140807)
          ·
            refine ⟨1205149695357752379211211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803433130238501586140807 1205149695357752379211211)
            ·
              refine ⟨1807724543036628568816817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205149695357752379211211 1807724543036628568816817)
              ·
                refine ⟨1355793407277471426612613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1807724543036628568816817 1355793407277471426612613)
                ·
                  refine ⟨254211263864525892489865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1355793407277471426612613 254211263864525892489865)
                  ·
                    rfl

theorem cell20_556959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 4].length) (baseStart_556959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556959 prefixEnd_556959 := by exact prefixLift 556959
  have htrace : WordTrace (prefixWord ++ tailWord_556959) baseStart_556959 baseEnd_556959 := by
    simpa [prefixWord, tailWord_556959, baseEnd_556959] using wordTrace_append hprefix tailTrace_556959
  have hstable : (prefixWord ++ tailWord_556959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556959).length < 2 ^ (prefixWord ++ tailWord_556959).sum := by decide
  have hdescent : baseEnd_556959 < baseStart_556959 := by decide
  rcases family_descends (prefixWord ++ tailWord_556959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556990 : List Nat := [4, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_556990 : Nat := 118140960795 + 556990 * 2 ^ 59
def prefixEnd_556990 : Nat := 4983230072969 + 3 ^ 40 * 556990 * 2
def baseEnd_556990 : Nat := 254225413109227562456405

theorem tailTrace_556990 : CollatzResearch.WordTrace tailWord_556990 prefixEnd_556990 254225413109227562456405 := by
  unfold tailWord_556990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2539386781515978895464553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13543396168085220775810949 2539386781515978895464553)
  ·
    refine ⟨1904540086136984171598415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2539386781515978895464553 1904540086136984171598415)
    ·
      refine ⟨2856810129205476257397623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1904540086136984171598415 2856810129205476257397623)
      ·
        refine ⟨4285215193808214386096435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2856810129205476257397623 4285215193808214386096435)
        ·
          refine ⟨6427822790712321579144653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4285215193808214386096435 6427822790712321579144653)
          ·
            refine ⟨2410433546517120592179245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6427822790712321579144653 2410433546517120592179245)
            ·
              refine ⟨903912579943920222067217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2410433546517120592179245 903912579943920222067217)
              ·
                refine ⟨677934434957940166550413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 903912579943920222067217 677934434957940166550413)
                ·
                  refine ⟨254225413109227562456405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 677934434957940166550413 254225413109227562456405)
                  ·
                    rfl

theorem cell20_556990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_556990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_556990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_556990 prefixEnd_556990 := by exact prefixLift 556990
  have htrace : WordTrace (prefixWord ++ tailWord_556990) baseStart_556990 baseEnd_556990 := by
    simpa [prefixWord, tailWord_556990, baseEnd_556990] using wordTrace_append hprefix tailTrace_556990
  have hstable : (prefixWord ++ tailWord_556990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556990).length < 2 ^ (prefixWord ++ tailWord_556990).sum := by decide
  have hdescent : baseEnd_556990 < baseStart_556990 := by decide
  rcases family_descends (prefixWord ++ tailWord_556990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557001 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 8]
def baseStart_557001 : Nat := 118140960795 + 557001 * 2 ^ 59
def prefixEnd_557001 : Nat := 4983230072969 + 3 ^ 40 * 557001 * 2
def baseEnd_557001 : Nat := 254230433808960413089693

theorem tailTrace_557001 : CollatzResearch.WordTrace tailWord_557001 prefixEnd_557001 254230433808960413089693 := by
  unfold tailWord_557001
  simp only [CollatzResearch.WordTrace]
  refine ⟨20315495455087980042366857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13543663636725320028244571 20315495455087980042366857)
  ·
    refine ⟨15236621591315985031775143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20315495455087980042366857 15236621591315985031775143)
    ·
      refine ⟨22854932386973977547662715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15236621591315985031775143 22854932386973977547662715)
      ·
        refine ⟨34282398580460966321494073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22854932386973977547662715 34282398580460966321494073)
        ·
          refine ⟨25711798935345724741120555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34282398580460966321494073 25711798935345724741120555)
          ·
            refine ⟨38567698403018587111680833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25711798935345724741120555 38567698403018587111680833)
            ·
              refine ⟨28925773802263940333760625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38567698403018587111680833 28925773802263940333760625)
              ·
                refine ⟨21694330351697955250320469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28925773802263940333760625 21694330351697955250320469)
                ·
                  refine ⟨254230433808960413089693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21694330351697955250320469 254230433808960413089693)
                  ·
                    rfl

theorem cell20_557001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_557001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557001 prefixEnd_557001 := by exact prefixLift 557001
  have htrace : WordTrace (prefixWord ++ tailWord_557001) baseStart_557001 baseEnd_557001 := by
    simpa [prefixWord, tailWord_557001, baseEnd_557001] using wordTrace_append hprefix tailTrace_557001
  have hstable : (prefixWord ++ tailWord_557001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557001).length < 2 ^ (prefixWord ++ tailWord_557001).sum := by decide
  have hdescent : baseEnd_557001 < baseStart_557001 := by decide
  rcases family_descends (prefixWord ++ tailWord_557001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557031 : List Nat := [1, 1, 5, 2, 3, 2, 1, 3, 2]
def baseStart_557031 : Nat := 118140960795 + 557031 * 2 ^ 59
def prefixEnd_557031 : Nat := 4983230072969 + 3 ^ 40 * 557031 * 2
def baseEnd_557031 : Nat := 254244126626413642089571

theorem tailTrace_557031 : CollatzResearch.WordTrace tailWord_557031 prefixEnd_557031 254244126626413642089571 := by
  unfold tailWord_557031
  simp only [CollatzResearch.WordTrace]
  refine ⟨20316589644979295165958947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13544393096652863443972631 20316589644979295165958947)
  ·
    refine ⟨30474884467468942748938421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20316589644979295165958947 30474884467468942748938421)
    ·
      refine ⟨2857020418825213382712977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30474884467468942748938421 2857020418825213382712977)
      ·
        refine ⟨2142765314118910037034733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2857020418825213382712977 2142765314118910037034733)
        ·
          refine ⟨803536992794591263888025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2142765314118910037034733 803536992794591263888025)
          ·
            refine ⟨602652744595943447916019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 803536992794591263888025 602652744595943447916019)
            ·
              refine ⟨903979116893915171874029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602652744595943447916019 903979116893915171874029)
              ·
                refine ⟨338992168835218189452761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 903979116893915171874029 338992168835218189452761)
                ·
                  refine ⟨254244126626413642089571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338992168835218189452761 254244126626413642089571)
                  ·
                    rfl

theorem cell20_557031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 2].length) (baseStart_557031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557031 prefixEnd_557031 := by exact prefixLift 557031
  have htrace : WordTrace (prefixWord ++ tailWord_557031) baseStart_557031 baseEnd_557031 := by
    simpa [prefixWord, tailWord_557031, baseEnd_557031] using wordTrace_append hprefix tailTrace_557031
  have hstable : (prefixWord ++ tailWord_557031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557031).length < 2 ^ (prefixWord ++ tailWord_557031).sum := by decide
  have hdescent : baseEnd_557031 < baseStart_557031 := by decide
  rcases family_descends (prefixWord ++ tailWord_557031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557052 : List Nat := [2, 2, 2, 1, 2, 2, 5, 2, 2]
def baseStart_557052 : Nat := 118140960795 + 557052 * 2 ^ 59
def prefixEnd_557052 : Nat := 4983230072969 + 3 ^ 40 * 557052 * 2
def baseEnd_557052 : Nat := 254253711598630902389485

theorem tailTrace_557052 : CollatzResearch.WordTrace tailWord_557052 prefixEnd_557052 254253711598630902389485 := by
  unfold tailWord_557052
  simp only [CollatzResearch.WordTrace]
  refine ⟨10158677788951607876236705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13544903718602143834982273 10158677788951607876236705)
  ·
    refine ⟨7619008341713705907177529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10158677788951607876236705 7619008341713705907177529)
    ·
      refine ⟨5714256256285279430383147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7619008341713705907177529 5714256256285279430383147)
      ·
        refine ⟨8571384384427919145574721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5714256256285279430383147 8571384384427919145574721)
        ·
          refine ⟨6428538288320939359181041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8571384384427919145574721 6428538288320939359181041)
          ·
            refine ⟨4821403716240704519385781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6428538288320939359181041 4821403716240704519385781)
            ·
              refine ⟨452006598397566048692417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4821403716240704519385781 452006598397566048692417)
              ·
                refine ⟨339004948798174536519313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 452006598397566048692417 339004948798174536519313)
                ·
                  refine ⟨254253711598630902389485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339004948798174536519313 254253711598630902389485)
                  ·
                    rfl

theorem cell20_557052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_557052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557052 prefixEnd_557052 := by exact prefixLift 557052
  have htrace : WordTrace (prefixWord ++ tailWord_557052) baseStart_557052 baseEnd_557052 := by
    simpa [prefixWord, tailWord_557052, baseEnd_557052] using wordTrace_append hprefix tailTrace_557052
  have hstable : (prefixWord ++ tailWord_557052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557052).length < 2 ^ (prefixWord ++ tailWord_557052).sum := by decide
  have hdescent : baseEnd_557052 < baseStart_557052 := by decide
  rcases family_descends (prefixWord ++ tailWord_557052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557063 : List Nat := [1, 1, 4, 3, 1, 2, 1, 7]
def baseStart_557063 : Nat := 118140960795 + 557063 * 2 ^ 59
def prefixEnd_557063 : Nat := 4983230072969 + 3 ^ 40 * 557063 * 2
def baseEnd_557063 : Nat := 84752910766121251007591

theorem tailTrace_557063 : CollatzResearch.WordTrace tailWord_557063 prefixEnd_557063 84752910766121251007591 := by
  unfold tailWord_557063
  simp only [CollatzResearch.WordTrace]
  refine ⟨20317756780863364631123843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13545171187242243087415895 20317756780863364631123843)
  ·
    refine ⟨30476635171295046946685765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20317756780863364631123843 30476635171295046946685765)
    ·
      refine ⟨5714369094617821302503581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30476635171295046946685765 5714369094617821302503581)
      ·
        refine ⟨2142888410481682988438843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5714369094617821302503581 2142888410481682988438843)
        ·
          refine ⟨3214332615722524482658265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2142888410481682988438843 3214332615722524482658265)
          ·
            refine ⟨2410749461791893361993699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3214332615722524482658265 2410749461791893361993699)
            ·
              refine ⟨3616124192687840042990549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2410749461791893361993699 3616124192687840042990549)
              ·
                refine ⟨84752910766121251007591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3616124192687840042990549 84752910766121251007591)
                ·
                  rfl

theorem cell20_557063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 7].length) (baseStart_557063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557063 prefixEnd_557063 := by exact prefixLift 557063
  have htrace : WordTrace (prefixWord ++ tailWord_557063) baseStart_557063 baseEnd_557063 := by
    simpa [prefixWord, tailWord_557063, baseEnd_557063] using wordTrace_append hprefix tailTrace_557063
  have hstable : (prefixWord ++ tailWord_557063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557063).length < 2 ^ (prefixWord ++ tailWord_557063).sum := by decide
  have hdescent : baseEnd_557063 < baseStart_557063 := by decide
  rcases family_descends (prefixWord ++ tailWord_557063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557066 : List Nat := [3, 1, 2, 2, 4, 1, 1, 3, 3]
def baseStart_557066 : Nat := 118140960795 + 557066 * 2 ^ 59
def prefixEnd_557066 : Nat := 4983230072969 + 3 ^ 40 * 557066 * 2
def baseEnd_557066 : Nat := 254260101580109075922761

theorem tailTrace_557066 : CollatzResearch.WordTrace tailWord_557066 prefixEnd_557066 254260101580109075922761 := by
  unfold tailWord_557066
  simp only [CollatzResearch.WordTrace]
  refine ⟨5079466549963124035870763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13545244133234997428988701 5079466549963124035870763)
  ·
    refine ⟨7619199824944686053806145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5079466549963124035870763 7619199824944686053806145)
    ·
      refine ⟨5714399868708514540354609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7619199824944686053806145 5714399868708514540354609)
      ·
        refine ⟨4285799901531385905265957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5714399868708514540354609 4285799901531385905265957)
        ·
          refine ⟨803587481537134857237367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4285799901531385905265957 803587481537134857237367)
          ·
            refine ⟨1205381222305702285856051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803587481537134857237367 1205381222305702285856051)
            ·
              refine ⟨1808071833458553428784077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205381222305702285856051 1808071833458553428784077)
              ·
                refine ⟨678026937546957535794029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1808071833458553428784077 678026937546957535794029)
                ·
                  refine ⟨254260101580109075922761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 678026937546957535794029 254260101580109075922761)
                  ·
                    rfl

theorem cell20_557066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_557066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557066 prefixEnd_557066 := by exact prefixLift 557066
  have htrace : WordTrace (prefixWord ++ tailWord_557066) baseStart_557066 baseEnd_557066 := by
    simpa [prefixWord, tailWord_557066, baseEnd_557066] using wordTrace_append hprefix tailTrace_557066
  have hstable : (prefixWord ++ tailWord_557066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557066).length < 2 ^ (prefixWord ++ tailWord_557066).sum := by decide
  have hdescent : baseEnd_557066 < baseStart_557066 := by decide
  rcases family_descends (prefixWord ++ tailWord_557066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557146 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_557146 : Nat := 118140960795 + 557146 * 2 ^ 59
def prefixEnd_557146 : Nat := 4983230072969 + 3 ^ 40 * 557146 * 2
def baseEnd_557146 : Nat := 254296615759984353255767

theorem tailTrace_557146 : CollatzResearch.WordTrace tailWord_557146 prefixEnd_557146 254296615759984353255767 := by
  unfold tailWord_557146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5080196009890667451598823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13547189359708446537596861 5080196009890667451598823)
  ·
    refine ⟨7620294014836001177398235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5080196009890667451598823 7620294014836001177398235)
    ·
      refine ⟨11430441022254001766097353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7620294014836001177398235 11430441022254001766097353)
      ·
        refine ⟨8572830766690501324573015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11430441022254001766097353 8572830766690501324573015)
        ·
          refine ⟨12859246150035751986859523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8572830766690501324573015 12859246150035751986859523)
          ·
            refine ⟨19288869225053627980289285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12859246150035751986859523 19288869225053627980289285)
            ·
              refine ⟨3616662979697555246304241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19288869225053627980289285 3616662979697555246304241)
              ·
                refine ⟨2712497234773166434728181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3616662979697555246304241 2712497234773166434728181)
                ·
                  refine ⟨254296615759984353255767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2712497234773166434728181 254296615759984353255767)
                  ·
                    rfl

theorem cell20_557146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_557146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557146 prefixEnd_557146 := by exact prefixLift 557146
  have htrace : WordTrace (prefixWord ++ tailWord_557146) baseStart_557146 baseEnd_557146 := by
    simpa [prefixWord, tailWord_557146, baseEnd_557146] using wordTrace_append hprefix tailTrace_557146
  have hstable : (prefixWord ++ tailWord_557146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557146).length < 2 ^ (prefixWord ++ tailWord_557146).sum := by decide
  have hdescent : baseEnd_557146 < baseStart_557146 := by decide
  rcases family_descends (prefixWord ++ tailWord_557146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557153 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 8]
def baseStart_557153 : Nat := 118140960795 + 557153 * 2 ^ 59
def prefixEnd_557153 : Nat := 4983230072969 + 3 ^ 40 * 557153 * 2
def baseEnd_557153 : Nat := 254299810750723440022405

theorem tailTrace_557153 : CollatzResearch.WordTrace tailWord_557153 prefixEnd_557153 254299810750723440022405 := by
  unfold tailWord_557153
  simp only [CollatzResearch.WordTrace]
  refine ⟨20321039350537310001900113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13547359567024873334600075 20321039350537310001900113)
  ·
    refine ⟨15240779512902982501425085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20321039350537310001900113 15240779512902982501425085)
    ·
      refine ⟨5715292317338618438034407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15240779512902982501425085 5715292317338618438034407)
      ·
        refine ⟨8572938476007927657051611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5715292317338618438034407 8572938476007927657051611)
        ·
          refine ⟨12859407714011891485577417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8572938476007927657051611 12859407714011891485577417)
          ·
            refine ⟨9644555785508918614183063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12859407714011891485577417 9644555785508918614183063)
            ·
              refine ⟨14466833678263377921274595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9644555785508918614183063 14466833678263377921274595)
              ·
                refine ⟨21700250517395066881911893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14466833678263377921274595 21700250517395066881911893)
                ·
                  refine ⟨254299810750723440022405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21700250517395066881911893 254299810750723440022405)
                  ·
                    rfl

theorem cell20_557153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_557153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557153 prefixEnd_557153 := by exact prefixLift 557153
  have htrace : WordTrace (prefixWord ++ tailWord_557153) baseStart_557153 baseEnd_557153 := by
    simpa [prefixWord, tailWord_557153, baseEnd_557153] using wordTrace_append hprefix tailTrace_557153
  have hstable : (prefixWord ++ tailWord_557153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557153).length < 2 ^ (prefixWord ++ tailWord_557153).sum := by decide
  have hdescent : baseEnd_557153 < baseStart_557153 := by decide
  rcases family_descends (prefixWord ++ tailWord_557153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557170 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_557170 : Nat := 118140960795 + 557170 * 2 ^ 59
def prefixEnd_557170 : Nat := 4983230072969 + 3 ^ 40 * 557170 * 2
def baseEnd_557170 : Nat := 254307570013946936455669

theorem tailTrace_557170 : CollatzResearch.WordTrace tailWord_557170 prefixEnd_557170 254307570013946936455669 := by
  unfold tailWord_557170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5080414847868930476317241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13547772927650481270179309 5080414847868930476317241)
  ·
    refine ⟨3810311135901697857237931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5080414847868930476317241 3810311135901697857237931)
    ·
      refine ⟨5715466703852546785856897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3810311135901697857237931 5715466703852546785856897)
      ·
        refine ⟨4286600027889410089392673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5715466703852546785856897 4286600027889410089392673)
        ·
          refine ⟨3214950020917057567044505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4286600027889410089392673 3214950020917057567044505)
          ·
            refine ⟨2411212515687793175283379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3214950020917057567044505 2411212515687793175283379)
            ·
              refine ⟨3616818773531689762925069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2411212515687793175283379 3616818773531689762925069)
              ·
                refine ⟨1356307040074383661096901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3616818773531689762925069 1356307040074383661096901)
                ·
                  refine ⟨254307570013946936455669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1356307040074383661096901 254307570013946936455669)
                  ·
                    rfl

theorem cell20_557170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_557170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557170 prefixEnd_557170 := by exact prefixLift 557170
  have htrace : WordTrace (prefixWord ++ tailWord_557170) baseStart_557170 baseEnd_557170 := by
    simpa [prefixWord, tailWord_557170, baseEnd_557170] using wordTrace_append hprefix tailTrace_557170
  have hstable : (prefixWord ++ tailWord_557170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557170).length < 2 ^ (prefixWord ++ tailWord_557170).sum := by decide
  have hdescent : baseEnd_557170 < baseStart_557170 := by decide
  rcases family_descends (prefixWord ++ tailWord_557170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557180 : List Nat := [2, 2, 2, 1, 1, 5, 3, 1, 3]
def baseStart_557180 : Nat := 118140960795 + 557180 * 2 ^ 59
def prefixEnd_557180 : Nat := 4983230072969 + 3 ^ 40 * 557180 * 2
def baseEnd_557180 : Nat := 254312134286431346122295

theorem tailTrace_557180 : CollatzResearch.WordTrace tailWord_557180 prefixEnd_557180 254312134286431346122295 := by
  unfold tailWord_557180
  simp only [CollatzResearch.WordTrace]
  refine ⟨10161012060719746806566497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13548016080959662408755329 10161012060719746806566497)
  ·
    refine ⟨7620759045539810104924873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10161012060719746806566497 7620759045539810104924873)
    ·
      refine ⟨5715569284154857578693655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7620759045539810104924873 5715569284154857578693655)
      ·
        refine ⟨8573353926232286368040483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5715569284154857578693655 8573353926232286368040483)
        ·
          refine ⟨12860030889348429552060725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8573353926232286368040483 12860030889348429552060725)
          ·
            refine ⟨1205627895876415270505693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12860030889348429552060725 1205627895876415270505693)
            ·
              refine ⟨452110460953655726439635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1205627895876415270505693 452110460953655726439635)
              ·
                refine ⟨678165691430483589659453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452110460953655726439635 678165691430483589659453)
                ·
                  refine ⟨254312134286431346122295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 678165691430483589659453 254312134286431346122295)
                  ·
                    rfl

theorem cell20_557180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_557180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557180 prefixEnd_557180 := by exact prefixLift 557180
  have htrace : WordTrace (prefixWord ++ tailWord_557180) baseStart_557180 baseEnd_557180 := by
    simpa [prefixWord, tailWord_557180, baseEnd_557180] using wordTrace_append hprefix tailTrace_557180
  have hstable : (prefixWord ++ tailWord_557180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557180).length < 2 ^ (prefixWord ++ tailWord_557180).sum := by decide
  have hdescent : baseEnd_557180 < baseStart_557180 := by decide
  rcases family_descends (prefixWord ++ tailWord_557180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557194 : List Nat := [3, 1, 2, 3, 1, 2, 4, 4]
def baseStart_557194 : Nat := 118140960795 + 557194 * 2 ^ 59
def prefixEnd_557194 : Nat := 4983230072969 + 3 ^ 40 * 557194 * 2
def baseEnd_557194 : Nat := 84772841422636506551857

theorem tailTrace_557194 : CollatzResearch.WordTrace tailWord_557194 prefixEnd_557194 84772841422636506551857 := by
  unfold tailWord_557194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5080633685847193501035659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13548356495592516002761757 5080633685847193501035659)
  ·
    refine ⟨7620950528770790251553489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5080633685847193501035659 7620950528770790251553489)
    ·
      refine ⟨5715712896578092688665117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7620950528770790251553489 5715712896578092688665117)
      ·
        refine ⟨2143392336216784758249419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5715712896578092688665117 2143392336216784758249419)
        ·
          refine ⟨3215088504325177137374129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2143392336216784758249419 3215088504325177137374129)
          ·
            refine ⟨2411316378243882853030597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3215088504325177137374129 2411316378243882853030597)
            ·
              refine ⟨452121820920728034943237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2411316378243882853030597 452121820920728034943237)
              ·
                refine ⟨84772841422636506551857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 452121820920728034943237 84772841422636506551857)
                ·
                  rfl

theorem cell20_557194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_557194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557194 prefixEnd_557194 := by exact prefixLift 557194
  have htrace : WordTrace (prefixWord ++ tailWord_557194) baseStart_557194 baseEnd_557194 := by
    simpa [prefixWord, tailWord_557194, baseEnd_557194] using wordTrace_append hprefix tailTrace_557194
  have hstable : (prefixWord ++ tailWord_557194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557194).length < 2 ^ (prefixWord ++ tailWord_557194).sum := by decide
  have hdescent : baseEnd_557194 < baseStart_557194 := by decide
  rcases family_descends (prefixWord ++ tailWord_557194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557215 : List Nat := [1, 1, 2, 6, 1, 1, 8]
def baseStart_557215 : Nat := 118140960795 + 557215 * 2 ^ 59
def prefixEnd_557215 : Nat := 4983230072969 + 3 ^ 40 * 557215 * 2
def baseEnd_557215 : Nat := 28258678804458531106165

theorem tailTrace_557215 : CollatzResearch.WordTrace tailWord_557215 prefixEnd_557215 28258678804458531106165 := by
  unfold tailWord_557215
  simp only [CollatzResearch.WordTrace]
  refine ⟨20323300676312694590657099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13548867117541796393771399 20323300676312694590657099)
  ·
    refine ⟨30484951014469041885985649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20323300676312694590657099 30484951014469041885985649)
    ·
      refine ⟨22863713260851781414489237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30484951014469041885985649 22863713260851781414489237)
      ·
        refine ⟨1071736559102427253804183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22863713260851781414489237 1071736559102427253804183)
        ·
          refine ⟨1607604838653640880706275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071736559102427253804183 1607604838653640880706275)
          ·
            refine ⟨2411407257980461321059413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607604838653640880706275 2411407257980461321059413)
            ·
              refine ⟨28258678804458531106165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2411407257980461321059413 28258678804458531106165)
              ·
                rfl

theorem cell20_557215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 8].length) (baseStart_557215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557215 prefixEnd_557215 := by exact prefixLift 557215
  have htrace : WordTrace (prefixWord ++ tailWord_557215) baseStart_557215 baseEnd_557215 := by
    simpa [prefixWord, tailWord_557215, baseEnd_557215] using wordTrace_append hprefix tailTrace_557215
  have hstable : (prefixWord ++ tailWord_557215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557215).length < 2 ^ (prefixWord ++ tailWord_557215).sum := by decide
  have hdescent : baseEnd_557215 < baseStart_557215 := by decide
  rcases family_descends (prefixWord ++ tailWord_557215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557239 : List Nat := [1, 1, 3, 1, 4, 3, 1, 3, 3]
def baseStart_557239 : Nat := 118140960795 + 557239 * 2 ^ 59
def prefixEnd_557239 : Nat := 4983230072969 + 3 ^ 40 * 557239 * 2
def baseEnd_557239 : Nat := 254339063494089363155387

theorem tailTrace_557239 : CollatzResearch.WordTrace tailWord_557239 prefixEnd_557239 254339063494089363155387 := by
  unfold tailWord_557239
  simp only [CollatzResearch.WordTrace]
  refine ⟨20324176028225746689530771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13549450685483831126353847 20324176028225746689530771)
  ·
    refine ⟨30486264042338620034296157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20324176028225746689530771 30486264042338620034296157)
    ·
      refine ⟨11432349015876982512861059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30486264042338620034296157 11432349015876982512861059)
      ·
        refine ⟨17148523523815473769291589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11432349015876982512861059 17148523523815473769291589)
        ·
          refine ⟨3215348160715401331742173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17148523523815473769291589 3215348160715401331742173)
          ·
            refine ⟨1205755560268275499403315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3215348160715401331742173 1205755560268275499403315)
            ·
              refine ⟨1808633340402413249104973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205755560268275499403315 1808633340402413249104973)
              ·
                refine ⟨678237502650904968414365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1808633340402413249104973 678237502650904968414365)
                ·
                  refine ⟨254339063494089363155387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 678237502650904968414365 254339063494089363155387)
                  ·
                    rfl

theorem cell20_557239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 3].length) (baseStart_557239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557239 prefixEnd_557239 := by exact prefixLift 557239
  have htrace : WordTrace (prefixWord ++ tailWord_557239) baseStart_557239 baseEnd_557239 := by
    simpa [prefixWord, tailWord_557239, baseEnd_557239] using wordTrace_append hprefix tailTrace_557239
  have hstable : (prefixWord ++ tailWord_557239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557239).length < 2 ^ (prefixWord ++ tailWord_557239).sum := by decide
  have hdescent : baseEnd_557239 < baseStart_557239 := by decide
  rcases family_descends (prefixWord ++ tailWord_557239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557270 : List Nat := [5, 2, 1, 2, 1, 9]
def baseStart_557270 : Nat := 118140960795 + 557270 * 2 ^ 59
def prefixEnd_557270 : Nat := 4983230072969 + 3 ^ 40 * 557270 * 2
def baseEnd_557270 : Nat := 9420489360695964189701

theorem tailTrace_557270 : CollatzResearch.WordTrace tailWord_557270 prefixEnd_557270 9420489360695964189701 := by
  unfold tailWord_557270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1270331668194589936494329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13550204460742292655939509 1270331668194589936494329)
  ·
    refine ⟨952748751145942452370747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1270331668194589936494329 952748751145942452370747)
    ·
      refine ⟨1429123126718913678556121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 952748751145942452370747 1429123126718913678556121)
      ·
        refine ⟨1071842345039185258917091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1429123126718913678556121 1071842345039185258917091)
        ·
          refine ⟨1607763517558777888375637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071842345039185258917091 1607763517558777888375637)
          ·
            refine ⟨9420489360695964189701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1607763517558777888375637 9420489360695964189701)
            ·
              rfl

theorem cell20_557270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 9].length) (baseStart_557270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557270 prefixEnd_557270 := by exact prefixLift 557270
  have htrace : WordTrace (prefixWord ++ tailWord_557270) baseStart_557270 baseEnd_557270 := by
    simpa [prefixWord, tailWord_557270, baseEnd_557270] using wordTrace_append hprefix tailTrace_557270
  have hstable : (prefixWord ++ tailWord_557270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557270).length < 2 ^ (prefixWord ++ tailWord_557270).sum := by decide
  have hdescent : baseEnd_557270 < baseStart_557270 := by decide
  rcases family_descends (prefixWord ++ tailWord_557270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557308 : List Nat := [2, 2, 2, 1, 4, 2, 3, 4]
def baseStart_557308 : Nat := 118140960795 + 557308 * 2 ^ 59
def prefixEnd_557308 : Nat := 4983230072969 + 3 ^ 40 * 557308 * 2
def baseEnd_557308 : Nat := 84790185658077263285035

theorem tailTrace_557308 : CollatzResearch.WordTrace tailWord_557308 prefixEnd_557308 84790185658077263285035 := by
  unfold tailWord_557308
  simp only [CollatzResearch.WordTrace]
  refine ⟨10163346332487885736896289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13551128443317180982528385 10163346332487885736896289)
  ·
    refine ⟨7622509749365914302672217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10163346332487885736896289 7622509749365914302672217)
    ·
      refine ⟨5716882312024435727004163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7622509749365914302672217 5716882312024435727004163)
      ·
        refine ⟨8575323468036653590506245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5716882312024435727004163 8575323468036653590506245)
        ·
          refine ⟨1607873150256872548219921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8575323468036653590506245 1607873150256872548219921)
          ·
            refine ⟨1205904862692654411164941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1607873150256872548219921 1205904862692654411164941)
            ·
              refine ⟨452214323509745404186853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1205904862692654411164941 452214323509745404186853)
              ·
                refine ⟨84790185658077263285035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 452214323509745404186853 84790185658077263285035)
                ·
                  rfl

theorem cell20_557308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_557308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557308 prefixEnd_557308 := by exact prefixLift 557308
  have htrace : WordTrace (prefixWord ++ tailWord_557308) baseStart_557308 baseEnd_557308 := by
    simpa [prefixWord, tailWord_557308, baseEnd_557308] using wordTrace_append hprefix tailTrace_557308
  have hstable : (prefixWord ++ tailWord_557308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557308).length < 2 ^ (prefixWord ++ tailWord_557308).sum := by decide
  have hdescent : baseEnd_557308 < baseStart_557308 := by decide
  rcases family_descends (prefixWord ++ tailWord_557308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557312 : List Nat := [2, 1, 1, 2, 1, 1, 4, 8]
def baseStart_557312 : Nat := 118140960795 + 557312 * 2 ^ 59
def prefixEnd_557312 : Nat := 4983230072969 + 3 ^ 40 * 557312 * 2
def baseEnd_557312 : Nat := 84790794227741851240585

theorem tailTrace_557312 : CollatzResearch.WordTrace tailWord_557312 prefixEnd_557312 84790794227741851240585 := by
  unfold tailWord_557312
  simp only [CollatzResearch.WordTrace]
  refine ⟨10163419278480640078469095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13551225704640853437958793 10163419278480640078469095)
  ·
    refine ⟨15245128917720960117703643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10163419278480640078469095 15245128917720960117703643)
    ·
      refine ⟨22867693376581440176555465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15245128917720960117703643 22867693376581440176555465)
      ·
        refine ⟨17150770032436080132416599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22867693376581440176555465 17150770032436080132416599)
        ·
          refine ⟨25726155048654120198624899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17150770032436080132416599 25726155048654120198624899)
          ·
            refine ⟨38589232572981180297937349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25726155048654120198624899 38589232572981180297937349)
            ·
              refine ⟨7235481107433971305863253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38589232572981180297937349 7235481107433971305863253)
              ·
                refine ⟨84790794227741851240585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7235481107433971305863253 84790794227741851240585)
                ·
                  rfl

theorem cell20_557312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_557312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557312 prefixEnd_557312 := by exact prefixLift 557312
  have htrace : WordTrace (prefixWord ++ tailWord_557312) baseStart_557312 baseEnd_557312 := by
    simpa [prefixWord, tailWord_557312, baseEnd_557312] using wordTrace_append hprefix tailTrace_557312
  have hstable : (prefixWord ++ tailWord_557312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557312).length < 2 ^ (prefixWord ++ tailWord_557312).sum := by decide
  have hdescent : baseEnd_557312 < baseStart_557312 := by decide
  rcases family_descends (prefixWord ++ tailWord_557312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557336 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 5]
def baseStart_557336 : Nat := 118140960795 + 557336 * 2 ^ 59
def prefixEnd_557336 : Nat := 4983230072969 + 3 ^ 40 * 557336 * 2
def baseEnd_557336 : Nat := 254383336937188136921657

theorem tailTrace_557336 : CollatzResearch.WordTrace tailWord_557336 prefixEnd_557336 254383336937188136921657 := by
  unfold tailWord_557336
  simp only [CollatzResearch.WordTrace]
  refine ⟨10163856954437166127905931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13551809272582888170541241 10163856954437166127905931)
  ·
    refine ⟨15245785431655749191858897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10163856954437166127905931 15245785431655749191858897)
    ·
      refine ⟨11434339073741811893894173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15245785431655749191858897 11434339073741811893894173)
      ·
        refine ⟨4287877152653179460210315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11434339073741811893894173 4287877152653179460210315)
        ·
          refine ⟨6431815728979769190315473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4287877152653179460210315 6431815728979769190315473)
          ·
            refine ⟨4823861796734826892736605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6431815728979769190315473 4823861796734826892736605)
            ·
              refine ⟨1808948173775560084776227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4823861796734826892736605 1808948173775560084776227)
              ·
                refine ⟨2713422260663340127164341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1808948173775560084776227 2713422260663340127164341)
                ·
                  refine ⟨254383336937188136921657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2713422260663340127164341 254383336937188136921657)
                  ·
                    rfl

theorem cell20_557336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_557336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557336 prefixEnd_557336 := by exact prefixLift 557336
  have htrace : WordTrace (prefixWord ++ tailWord_557336) baseStart_557336 baseEnd_557336 := by
    simpa [prefixWord, tailWord_557336, baseEnd_557336] using wordTrace_append hprefix tailTrace_557336
  have hstable : (prefixWord ++ tailWord_557336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557336).length < 2 ^ (prefixWord ++ tailWord_557336).sum := by decide
  have hdescent : baseEnd_557336 < baseStart_557336 := by decide
  rcases family_descends (prefixWord ++ tailWord_557336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557404 : List Nat := [2, 2, 4, 3, 1, 2, 2, 1, 3]
def baseStart_557404 : Nat := 118140960795 + 557404 * 2 ^ 59
def prefixEnd_557404 : Nat := 4983230072969 + 3 ^ 40 * 557404 * 2
def baseEnd_557404 : Nat := 254414373990082122654713

theorem tailTrace_557404 : CollatzResearch.WordTrace tailWord_557404 prefixEnd_557404 254414373990082122654713 := by
  unfold tailWord_557404
  simp only [CollatzResearch.WordTrace]
  refine ⟨10165097036313989934643633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13553462715085319912858177 10165097036313989934643633)
  ·
    refine ⟨7623822777235492450982725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10165097036313989934643633 7623822777235492450982725)
    ·
      refine ⟨1429466770731654834559261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7623822777235492450982725 1429466770731654834559261)
      ·
        refine ⟨536050039024370562959723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1429466770731654834559261 536050039024370562959723)
        ·
          refine ⟨804075058536555844439585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536050039024370562959723 804075058536555844439585)
          ·
            refine ⟨603056293902416883329689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 804075058536555844439585 603056293902416883329689)
            ·
              refine ⟨452292220426812662497267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 603056293902416883329689 452292220426812662497267)
              ·
                refine ⟨678438330640218993745901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452292220426812662497267 678438330640218993745901)
                ·
                  refine ⟨254414373990082122654713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 678438330640218993745901 254414373990082122654713)
                  ·
                    rfl

theorem cell20_557404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_557404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557404 prefixEnd_557404 := by exact prefixLift 557404
  have htrace : WordTrace (prefixWord ++ tailWord_557404) baseStart_557404 baseEnd_557404 := by
    simpa [prefixWord, tailWord_557404, baseEnd_557404] using wordTrace_append hprefix tailTrace_557404
  have hstable : (prefixWord ++ tailWord_557404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557404).length < 2 ^ (prefixWord ++ tailWord_557404).sum := by decide
  have hdescent : baseEnd_557404 < baseStart_557404 := by decide
  rcases family_descends (prefixWord ++ tailWord_557404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557443 : List Nat := [1, 1, 1, 3, 7, 7]
def baseStart_557443 : Nat := 118140960795 + 557443 * 2 ^ 59
def prefixEnd_557443 : Nat := 4983230072969 + 3 ^ 40 * 557443 * 2
def baseEnd_557443 : Nat := 9423413876028567420539

theorem tailTrace_557443 : CollatzResearch.WordTrace tailWord_557443 prefixEnd_557443 9423413876028567420539 := by
  unfold tailWord_557443
  simp only [CollatzResearch.WordTrace]
  refine ⟨20331616519486689529956983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13554411012991126353304655 20331616519486689529956983)
  ·
    refine ⟨30497424779230034294935475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20331616519486689529956983 30497424779230034294935475)
    ·
      refine ⟨45746137168845051442403213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30497424779230034294935475 45746137168845051442403213)
      ·
        refine ⟨17154801438316894290901205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45746137168845051442403213 17154801438316894290901205)
        ·
          refine ⟨402065658710552209942997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 17154801438316894290901205 402065658710552209942997)
          ·
            refine ⟨9423413876028567420539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 402065658710552209942997 9423413876028567420539)
            ·
              rfl

theorem cell20_557443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 7].length) (baseStart_557443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557443 prefixEnd_557443 := by exact prefixLift 557443
  have htrace : WordTrace (prefixWord ++ tailWord_557443) baseStart_557443 baseEnd_557443 := by
    simpa [prefixWord, tailWord_557443, baseEnd_557443] using wordTrace_append hprefix tailTrace_557443
  have hstable : (prefixWord ++ tailWord_557443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557443).length < 2 ^ (prefixWord ++ tailWord_557443).sum := by decide
  have hdescent : baseEnd_557443 < baseStart_557443 := by decide
  rcases family_descends (prefixWord ++ tailWord_557443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557474 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_557474 : Nat := 118140960795 + 557474 * 2 ^ 59
def prefixEnd_557474 : Nat := 4983230072969 + 3 ^ 40 * 557474 * 2
def baseEnd_557474 : Nat := 254446323897472990321093

theorem tailTrace_557474 : CollatzResearch.WordTrace tailWord_557474 prefixEnd_557474 254446323897472990321093 := by
  unfold tailWord_557474
  simp only [CollatzResearch.WordTrace]
  refine ⟨5083186795593595456083869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13555164788249587882890317 5083186795593595456083869)
  ·
    refine ⟨1906195048347598296031451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5083186795593595456083869 1906195048347598296031451)
    ·
      refine ⟨2859292572521397444047177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1906195048347598296031451 2859292572521397444047177)
      ·
        refine ⟨2144469429391048083035383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2859292572521397444047177 2144469429391048083035383)
        ·
          refine ⟨3216704144086572124553075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2144469429391048083035383 3216704144086572124553075)
          ·
            refine ⟨4825056216129858186829613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3216704144086572124553075 4825056216129858186829613)
            ·
              refine ⟨1809396081048696820061105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4825056216129858186829613 1809396081048696820061105)
              ·
                refine ⟨1357047060786522615045829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1809396081048696820061105 1357047060786522615045829)
                ·
                  refine ⟨254446323897472990321093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1357047060786522615045829 254446323897472990321093)
                  ·
                    rfl

theorem cell20_557474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_557474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557474 prefixEnd_557474 := by exact prefixLift 557474
  have htrace : WordTrace (prefixWord ++ tailWord_557474) baseStart_557474 baseEnd_557474 := by
    simpa [prefixWord, tailWord_557474, baseEnd_557474] using wordTrace_append hprefix tailTrace_557474
  have hstable : (prefixWord ++ tailWord_557474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557474).length < 2 ^ (prefixWord ++ tailWord_557474).sum := by decide
  have hdescent : baseEnd_557474 < baseStart_557474 := by decide
  rcases family_descends (prefixWord ++ tailWord_557474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557512 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 4]
def baseStart_557512 : Nat := 118140960795 + 557512 * 2 ^ 59
def prefixEnd_557512 : Nat := 4983230072969 + 3 ^ 40 * 557512 * 2
def baseEnd_557512 : Nat := 254463668132913747054271

theorem tailTrace_557512 : CollatzResearch.WordTrace tailWord_557512 prefixEnd_557512 254463668132913747054271 := by
  unfold tailWord_557512
  simp only [CollatzResearch.WordTrace]
  refine ⟨10167066578118357157109395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13556088770824476209479193 10167066578118357157109395)
  ·
    refine ⟨15250599867177535735664093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10167066578118357157109395 15250599867177535735664093)
    ·
      refine ⟨5718974950191575900874035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15250599867177535735664093 5718974950191575900874035)
      ·
        refine ⟨8578462425287363851311053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5718974950191575900874035 8578462425287363851311053)
        ·
          refine ⟨3216923409482761444241645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8578462425287363851311053 3216923409482761444241645)
          ·
            refine ⟨1206346278556035541590617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3216923409482761444241645 1206346278556035541590617)
            ·
              refine ⟨904759708917026656192963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1206346278556035541590617 904759708917026656192963)
              ·
                refine ⟨1357139563375539984289445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904759708917026656192963 1357139563375539984289445)
                ·
                  refine ⟨254463668132913747054271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1357139563375539984289445 254463668132913747054271)
                  ·
                    rfl

theorem cell20_557512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_557512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557512 prefixEnd_557512 := by exact prefixLift 557512
  have htrace : WordTrace (prefixWord ++ tailWord_557512) baseStart_557512 baseEnd_557512 := by
    simpa [prefixWord, tailWord_557512, baseEnd_557512] using wordTrace_append hprefix tailTrace_557512
  have hstable : (prefixWord ++ tailWord_557512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557512).length < 2 ^ (prefixWord ++ tailWord_557512).sum := by decide
  have hdescent : baseEnd_557512 < baseStart_557512 := by decide
  rcases family_descends (prefixWord ++ tailWord_557512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557546 : List Nat := [3, 1, 3, 1, 3, 3, 1, 3, 2]
def baseStart_557546 : Nat := 118140960795 + 557546 * 2 ^ 59
def prefixEnd_557546 : Nat := 4983230072969 + 3 ^ 40 * 557546 * 2
def baseEnd_557546 : Nat := 254479186659360739920799

theorem tailTrace_557546 : CollatzResearch.WordTrace tailWord_557546 prefixEnd_557546 254479186659360739920799 := by
  unfold tailWord_557546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5083843309528384530239123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13556915492075692080637661 5083843309528384530239123)
  ·
    refine ⟨7625764964292576795358685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5083843309528384530239123 7625764964292576795358685)
    ·
      refine ⟨2859661861609716298259507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7625764964292576795358685 2859661861609716298259507)
      ·
        refine ⟨4289492792414574447389261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2859661861609716298259507 4289492792414574447389261)
        ·
          refine ⟨1608559797155465417770973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4289492792414574447389261 1608559797155465417770973)
          ·
            refine ⟨603209923933299531664115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1608559797155465417770973 603209923933299531664115)
            ·
              refine ⟨904814885899949297496173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 603209923933299531664115 904814885899949297496173)
              ·
                refine ⟨339305582212480986561065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 904814885899949297496173 339305582212480986561065)
                ·
                  refine ⟨254479186659360739920799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339305582212480986561065 254479186659360739920799)
                  ·
                    rfl

theorem cell20_557546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_557546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557546 prefixEnd_557546 := by exact prefixLift 557546
  have htrace : WordTrace (prefixWord ++ tailWord_557546) baseStart_557546 baseEnd_557546 := by
    simpa [prefixWord, tailWord_557546, baseEnd_557546] using wordTrace_append hprefix tailTrace_557546
  have hstable : (prefixWord ++ tailWord_557546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557546).length < 2 ^ (prefixWord ++ tailWord_557546).sum := by decide
  have hdescent : baseEnd_557546 < baseStart_557546 := by decide
  rcases family_descends (prefixWord ++ tailWord_557546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557547 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 7]
def baseStart_557547 : Nat := 118140960795 + 557547 * 2 ^ 59
def prefixEnd_557547 : Nat := 4983230072969 + 3 ^ 40 * 557547 * 2
def baseEnd_557547 : Nat := 254479643086609180887461

theorem tailTrace_557547 : CollatzResearch.WordTrace tailWord_557547 prefixEnd_557547 254479643086609180887461 := by
  unfold tailWord_557547
  simp only [CollatzResearch.WordTrace]
  refine ⟨20335409711109915291742895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13556939807406610194495263 20335409711109915291742895)
  ·
    refine ⟨30503114566664872937614343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20335409711109915291742895 30503114566664872937614343)
    ·
      refine ⟨45754671849997309406421515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30503114566664872937614343 45754671849997309406421515)
      ·
        refine ⟨68632007774995964109632273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45754671849997309406421515 68632007774995964109632273)
        ·
          refine ⟨51474005831246973082224205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68632007774995964109632273 51474005831246973082224205)
          ·
            refine ⟨19302752186717614905834077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51474005831246973082224205 19302752186717614905834077)
            ·
              refine ⟨7238532070019105589687779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19302752186717614905834077 7238532070019105589687779)
              ·
                refine ⟨10857798105028658384531669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7238532070019105589687779 10857798105028658384531669)
                ·
                  refine ⟨254479643086609180887461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10857798105028658384531669 254479643086609180887461)
                  ·
                    rfl

theorem cell20_557547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_557547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557547 prefixEnd_557547 := by exact prefixLift 557547
  have htrace : WordTrace (prefixWord ++ tailWord_557547) baseStart_557547 baseEnd_557547 := by
    simpa [prefixWord, tailWord_557547, baseEnd_557547] using wordTrace_append hprefix tailTrace_557547
  have hstable : (prefixWord ++ tailWord_557547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557547).length < 2 ^ (prefixWord ++ tailWord_557547).sum := by decide
  have hdescent : baseEnd_557547 < baseStart_557547 := by decide
  rcases family_descends (prefixWord ++ tailWord_557547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557564 : List Nat := [2, 2, 2, 1, 2, 1, 1, 6, 3]
def baseStart_557564 : Nat := 118140960795 + 557564 * 2 ^ 59
def prefixEnd_557564 : Nat := 4983230072969 + 3 ^ 40 * 557564 * 2
def baseEnd_557564 : Nat := 254487402349832677320725

theorem tailTrace_557564 : CollatzResearch.WordTrace tailWord_557564 prefixEnd_557564 254487402349832677320725 := by
  unfold tailWord_557564
  simp only [CollatzResearch.WordTrace]
  refine ⟨10168014876024163597555873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13557353168032218130074497 10168014876024163597555873)
  ·
    refine ⟨7626011157018122698166905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10168014876024163597555873 7626011157018122698166905)
    ·
      refine ⟨5719508367763592023625179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7626011157018122698166905 5719508367763592023625179)
      ·
        refine ⟨8579262551645388035437769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5719508367763592023625179 8579262551645388035437769)
        ·
          refine ⟨6434446913734041026578327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8579262551645388035437769 6434446913734041026578327)
          ·
            refine ⟨9651670370601061539867491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6434446913734041026578327 9651670370601061539867491)
            ·
              refine ⟨14477505555901592309801237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9651670370601061539867491 14477505555901592309801237)
              ·
                refine ⟨678633072932887139521933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14477505555901592309801237 678633072932887139521933)
                ·
                  refine ⟨254487402349832677320725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 678633072932887139521933 254487402349832677320725)
                  ·
                    rfl

theorem cell20_557564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_557564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557564 prefixEnd_557564 := by exact prefixLift 557564
  have htrace : WordTrace (prefixWord ++ tailWord_557564) baseStart_557564 baseEnd_557564 := by
    simpa [prefixWord, tailWord_557564, baseEnd_557564] using wordTrace_append hprefix tailTrace_557564
  have hstable : (prefixWord ++ tailWord_557564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557564).length < 2 ^ (prefixWord ++ tailWord_557564).sum := by decide
  have hdescent : baseEnd_557564 < baseStart_557564 := by decide
  rcases family_descends (prefixWord ++ tailWord_557564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557567 : List Nat := [1, 1, 2, 2, 1, 2, 7, 2, 2]
def baseStart_557567 : Nat := 118140960795 + 557567 * 2 ^ 59
def prefixEnd_557567 : Nat := 4983230072969 + 3 ^ 40 * 557567 * 2
def baseEnd_557567 : Nat := 254488771631578000220713

theorem tailTrace_557567 : CollatzResearch.WordTrace tailWord_557567 prefixEnd_557567 254488771631578000220713 := by
  unfold tailWord_557567
  simp only [CollatzResearch.WordTrace]
  refine ⟨20336139171037458707470955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13557426114024972471647303 20336139171037458707470955)
  ·
    refine ⟨30504208756556188061206433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20336139171037458707470955 30504208756556188061206433)
    ·
      refine ⟨22878156567417141045904825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30504208756556188061206433 22878156567417141045904825)
      ·
        refine ⟨17158617425562855784428619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22878156567417141045904825 17158617425562855784428619)
        ·
          refine ⟨25737926138344283676642929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17158617425562855784428619 25737926138344283676642929)
          ·
            refine ⟨19303444603758212757482197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25737926138344283676642929 19303444603758212757482197)
            ·
              refine ⟨452424482900583111503489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19303444603758212757482197 452424482900583111503489)
              ·
                refine ⟨339318362175437333627617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 452424482900583111503489 339318362175437333627617)
                ·
                  refine ⟨254488771631578000220713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339318362175437333627617 254488771631578000220713)
                  ·
                    rfl

theorem cell20_557567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 2].length) (baseStart_557567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557567 prefixEnd_557567 := by exact prefixLift 557567
  have htrace : WordTrace (prefixWord ++ tailWord_557567) baseStart_557567 baseEnd_557567 := by
    simpa [prefixWord, tailWord_557567, baseEnd_557567] using wordTrace_append hprefix tailTrace_557567
  have hstable : (prefixWord ++ tailWord_557567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557567).length < 2 ^ (prefixWord ++ tailWord_557567).sum := by decide
  have hdescent : baseEnd_557567 < baseStart_557567 := by decide
  rcases family_descends (prefixWord ++ tailWord_557567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557585 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 7]
def baseStart_557585 : Nat := 118140960795 + 557585 * 2 ^ 59
def prefixEnd_557585 : Nat := 4983230072969 + 3 ^ 40 * 557585 * 2
def baseEnd_557585 : Nat := 254496987322049937620639

theorem tailTrace_557585 : CollatzResearch.WordTrace tailWord_557585 prefixEnd_557585 254496987322049937620639 := by
  unfold tailWord_557585
  simp only [CollatzResearch.WordTrace]
  refine ⟨20336795684972247781626209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13557863789981498521084139 20336795684972247781626209)
  ·
    refine ⟨15252596763729185836219657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20336795684972247781626209 15252596763729185836219657)
    ·
      refine ⟨11439447572796889377164743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15252596763729185836219657 11439447572796889377164743)
      ·
        refine ⟨17159171359195334065747115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11439447572796889377164743 17159171359195334065747115)
        ·
          refine ⟨25738757038793001098620673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17159171359195334065747115 25738757038793001098620673)
          ·
            refine ⟨19304067779094750823965505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25738757038793001098620673 19304067779094750823965505)
            ·
              refine ⟨14478050834321063117974129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19304067779094750823965505 14478050834321063117974129)
              ·
                refine ⟨10858538125740797338480597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14478050834321063117974129 10858538125740797338480597)
                ·
                  refine ⟨254496987322049937620639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10858538125740797338480597 254496987322049937620639)
                  ·
                    rfl

theorem cell20_557585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_557585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557585 prefixEnd_557585 := by exact prefixLift 557585
  have htrace : WordTrace (prefixWord ++ tailWord_557585) baseStart_557585 baseEnd_557585 := by
    simpa [prefixWord, tailWord_557585, baseEnd_557585] using wordTrace_append hprefix tailTrace_557585
  have hstable : (prefixWord ++ tailWord_557585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557585).length < 2 ^ (prefixWord ++ tailWord_557585).sum := by decide
  have hdescent : baseEnd_557585 < baseStart_557585 := by decide
  rcases family_descends (prefixWord ++ tailWord_557585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557622 : List Nat := [5, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_557622 : Nat := 118140960795 + 557622 * 2 ^ 59
def prefixEnd_557622 : Nat := 4983230072969 + 3 ^ 40 * 557622 * 2
def baseEnd_557622 : Nat := 254513875130242253387155

theorem tailTrace_557622 : CollatzResearch.WordTrace tailWord_557622 prefixEnd_557622 254513875130242253387155 := by
  unfold tailWord_557622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1271134074114887693795195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13558763457225468733815413 1271134074114887693795195)
  ·
    refine ⟨1906701111172331540692793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1271134074114887693795195 1906701111172331540692793)
    ·
      refine ⟨1430025833379248655519595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1906701111172331540692793 1430025833379248655519595)
      ·
        refine ⟨2145038750068872983279393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1430025833379248655519595 2145038750068872983279393)
        ·
          refine ⟨1608779062551654737459545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2145038750068872983279393 1608779062551654737459545)
          ·
            refine ⟨1206584296913741053094659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1608779062551654737459545 1206584296913741053094659)
            ·
              refine ⟨1809876445370611579641989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1206584296913741053094659 1809876445370611579641989)
              ·
                refine ⟨339351833506989671182873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1809876445370611579641989 339351833506989671182873)
                ·
                  refine ⟨254513875130242253387155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339351833506989671182873 254513875130242253387155)
                  ·
                    rfl

theorem cell20_557622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_557622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557622 prefixEnd_557622 := by exact prefixLift 557622
  have htrace : WordTrace (prefixWord ++ tailWord_557622) baseStart_557622 baseEnd_557622 := by
    simpa [prefixWord, tailWord_557622, baseEnd_557622] using wordTrace_append hprefix tailTrace_557622
  have hstable : (prefixWord ++ tailWord_557622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557622).length < 2 ^ (prefixWord ++ tailWord_557622).sum := by decide
  have hdescent : baseEnd_557622 < baseStart_557622 := by decide
  rcases family_descends (prefixWord ++ tailWord_557622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557633 : List Nat := [1, 2, 5, 1, 1, 2, 3, 5]
def baseStart_557633 : Nat := 118140960795 + 557633 * 2 ^ 59
def prefixEnd_557633 : Nat := 4983230072969 + 3 ^ 40 * 557633 * 2
def baseEnd_557633 : Nat := 84839631943325034673481

theorem tailTrace_557633 : CollatzResearch.WordTrace tailWord_557633 prefixEnd_557633 84839631943325034673481 := by
  unfold tailWord_557633
  simp only [CollatzResearch.WordTrace]
  refine ⟨20338546388798351979373553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13559030925865567986249035 20338546388798351979373553)
  ·
    refine ⟨15253909791598763984530165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20338546388798351979373553 15253909791598763984530165)
    ·
      refine ⟨1430054042962384123549703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15253909791598763984530165 1430054042962384123549703)
      ·
        refine ⟨2145081064443576185324555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1430054042962384123549703 2145081064443576185324555)
        ·
          refine ⟨3217621596665364277986833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2145081064443576185324555 3217621596665364277986833)
          ·
            refine ⟨2413216197499023208490125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3217621596665364277986833 2413216197499023208490125)
            ·
              refine ⟨904956074062133703183797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2413216197499023208490125 904956074062133703183797)
              ·
                refine ⟨84839631943325034673481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 904956074062133703183797 84839631943325034673481)
                ·
                  rfl

theorem cell20_557633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 5].length) (baseStart_557633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557633 prefixEnd_557633 := by exact prefixLift 557633
  have htrace : WordTrace (prefixWord ++ tailWord_557633) baseStart_557633 baseEnd_557633 := by
    simpa [prefixWord, tailWord_557633, baseEnd_557633] using wordTrace_append hprefix tailTrace_557633
  have hstable : (prefixWord ++ tailWord_557633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557633).length < 2 ^ (prefixWord ++ tailWord_557633).sum := by decide
  have hdescent : baseEnd_557633 < baseStart_557633 := by decide
  rcases family_descends (prefixWord ++ tailWord_557633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557660 : List Nat := [2, 2, 4, 1, 3, 1, 2, 3, 2]
def baseStart_557660 : Nat := 118140960795 + 557660 * 2 ^ 59
def prefixEnd_557660 : Nat := 4983230072969 + 3 ^ 40 * 557660 * 2
def baseEnd_557660 : Nat := 254531219365683010120333

theorem tailTrace_557660 : CollatzResearch.WordTrace tailWord_557660 prefixEnd_557660 254531219365683010120333 := by
  unfold tailWord_557660
  simp only [CollatzResearch.WordTrace]
  refine ⟨10169765579850267795303217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13559687439800357060404289 10169765579850267795303217)
  ·
    refine ⟨7627324184887700846477413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10169765579850267795303217 7627324184887700846477413)
    ·
      refine ⟨1430123284666443908714515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7627324184887700846477413 1430123284666443908714515)
      ·
        refine ⟨2145184926999665863071773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1430123284666443908714515 2145184926999665863071773)
        ·
          refine ⟨804444347624874698651915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2145184926999665863071773 804444347624874698651915)
          ·
            refine ⟨1206666521437312047977873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804444347624874698651915 1206666521437312047977873)
            ·
              refine ⟨904999891077984035983405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1206666521437312047977873 904999891077984035983405)
              ·
                refine ⟨339374959154244013493777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 904999891077984035983405 339374959154244013493777)
                ·
                  refine ⟨254531219365683010120333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339374959154244013493777 254531219365683010120333)
                  ·
                    rfl

theorem cell20_557660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_557660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557660 prefixEnd_557660 := by exact prefixLift 557660
  have htrace : WordTrace (prefixWord ++ tailWord_557660) baseStart_557660 baseEnd_557660 := by
    simpa [prefixWord, tailWord_557660, baseEnd_557660] using wordTrace_append hprefix tailTrace_557660
  have hstable : (prefixWord ++ tailWord_557660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557660).length < 2 ^ (prefixWord ++ tailWord_557660).sum := by decide
  have hdescent : baseEnd_557660 < baseStart_557660 := by decide
  rcases family_descends (prefixWord ++ tailWord_557660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557664 : List Nat := [2, 1, 1, 3, 2, 1, 3, 5, 2]
def baseStart_557664 : Nat := 118140960795 + 557664 * 2 ^ 59
def prefixEnd_557664 : Nat := 4983230072969 + 3 ^ 40 * 557664 * 2
def baseEnd_557664 : Nat := 254533045074676773986983

theorem tailTrace_557664 : CollatzResearch.WordTrace tailWord_557664 prefixEnd_557664 254533045074676773986983 := by
  unfold tailWord_557664
  simp only [CollatzResearch.WordTrace]
  refine ⟨10169838525843022136876023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13559784701124029515834697 10169838525843022136876023)
  ·
    refine ⟨15254757788764533205314035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10169838525843022136876023 15254757788764533205314035)
    ·
      refine ⟨22882136683146799807971053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15254757788764533205314035 22882136683146799807971053)
      ·
        refine ⟨8580801256180049927989145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22882136683146799807971053 8580801256180049927989145)
        ·
          refine ⟨6435600942135037445991859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8580801256180049927989145 6435600942135037445991859)
          ·
            refine ⟨9653401413202556168987789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6435600942135037445991859 9653401413202556168987789)
            ·
              refine ⟨3620025529950958563370421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9653401413202556168987789 3620025529950958563370421)
              ·
                refine ⟨339377393432902365315977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3620025529950958563370421 339377393432902365315977)
                ·
                  refine ⟨254533045074676773986983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339377393432902365315977 254533045074676773986983)
                  ·
                    rfl

theorem cell20_557664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 2].length) (baseStart_557664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557664 prefixEnd_557664 := by exact prefixLift 557664
  have htrace : WordTrace (prefixWord ++ tailWord_557664) baseStart_557664 baseEnd_557664 := by
    simpa [prefixWord, tailWord_557664, baseEnd_557664] using wordTrace_append hprefix tailTrace_557664
  have hstable : (prefixWord ++ tailWord_557664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557664).length < 2 ^ (prefixWord ++ tailWord_557664).sum := by decide
  have hdescent : baseEnd_557664 < baseStart_557664 := by decide
  rcases family_descends (prefixWord ++ tailWord_557664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557754 : List Nat := [3, 1, 1, 1, 2, 3, 3, 3, 3]
def baseStart_557754 : Nat := 118140960795 + 557754 * 2 ^ 59
def prefixEnd_557754 : Nat := 4983230072969 + 3 ^ 40 * 557754 * 2
def baseEnd_557754 : Nat := 254574123527036460986615

theorem tailTrace_557754 : CollatzResearch.WordTrace tailWord_557754 prefixEnd_557754 254574123527036460986615 := by
  unfold tailWord_557754
  simp only [CollatzResearch.WordTrace]
  refine ⟨5085739905339997411132079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13561973080906659763018877 5085739905339997411132079)
  ·
    refine ⟨7628609858009996116698119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5085739905339997411132079 7628609858009996116698119)
    ·
      refine ⟨11442914787014994175047179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7628609858009996116698119 11442914787014994175047179)
      ·
        refine ⟨17164372180522491262570769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11442914787014994175047179 17164372180522491262570769)
        ·
          refine ⟨12873279135391868446928077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17164372180522491262570769 12873279135391868446928077)
          ·
            refine ⟨4827479675771950667598029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12873279135391868446928077 4827479675771950667598029)
            ·
              refine ⟨1810304878414481500349261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4827479675771950667598029 1810304878414481500349261)
              ·
                refine ⟨678864329405430562630973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1810304878414481500349261 678864329405430562630973)
                ·
                  refine ⟨254574123527036460986615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 678864329405430562630973 254574123527036460986615)
                  ·
                    rfl

theorem cell20_557754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_557754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557754 prefixEnd_557754 := by exact prefixLift 557754
  have htrace : WordTrace (prefixWord ++ tailWord_557754) baseStart_557754 baseEnd_557754 := by
    simpa [prefixWord, tailWord_557754, baseEnd_557754] using wordTrace_append hprefix tailTrace_557754
  have hstable : (prefixWord ++ tailWord_557754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557754).length < 2 ^ (prefixWord ++ tailWord_557754).sum := by decide
  have hdescent : baseEnd_557754 < baseStart_557754 := by decide
  rcases family_descends (prefixWord ++ tailWord_557754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557768 : List Nat := [2, 1, 3, 1, 2, 3, 2, 6]
def baseStart_557768 : Nat := 118140960795 + 557768 * 2 ^ 59
def prefixEnd_557768 : Nat := 4983230072969 + 3 ^ 40 * 557768 * 2
def baseEnd_557768 : Nat := 84860171169504878173297

theorem tailTrace_557768 : CollatzResearch.WordTrace tailWord_557768 prefixEnd_557768 84860171169504878173297 := by
  unfold tailWord_557768
  simp only [CollatzResearch.WordTrace]
  refine ⟨10171735121654635017768979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13562313495539513357025305 10171735121654635017768979)
  ·
    refine ⟨15257602682481952526653469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10171735121654635017768979 15257602682481952526653469)
    ·
      refine ⟨5721601005930732197495051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15257602682481952526653469 5721601005930732197495051)
      ·
        refine ⟨8582401508896098296242577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5721601005930732197495051 8582401508896098296242577)
        ·
          refine ⟨6436801131672073722181933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8582401508896098296242577 6436801131672073722181933)
          ·
            refine ⟨2413800424377027645818225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6436801131672073722181933 2413800424377027645818225)
            ·
              refine ⟨1810350318282770734363669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2413800424377027645818225 1810350318282770734363669)
              ·
                refine ⟨84860171169504878173297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1810350318282770734363669 84860171169504878173297)
                ·
                  rfl

theorem cell20_557768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_557768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557768 prefixEnd_557768 := by exact prefixLift 557768
  have htrace : WordTrace (prefixWord ++ tailWord_557768) baseStart_557768 baseEnd_557768 := by
    simpa [prefixWord, tailWord_557768, baseEnd_557768] using wordTrace_append hprefix tailTrace_557768
  have hstable : (prefixWord ++ tailWord_557768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557768).length < 2 ^ (prefixWord ++ tailWord_557768).sum := by decide
  have hdescent : baseEnd_557768 < baseStart_557768 := by decide
  rcases family_descends (prefixWord ++ tailWord_557768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557788 : List Nat := [2, 2, 5, 1, 1, 2, 2, 2, 3]
def baseStart_557788 : Nat := 118140960795 + 557788 * 2 ^ 59
def prefixEnd_557788 : Nat := 4983230072969 + 3 ^ 40 * 557788 * 2
def baseEnd_557788 : Nat := 254589642053483453853143

theorem tailTrace_557788 : CollatzResearch.WordTrace tailWord_557788 prefixEnd_557788 254589642053483453853143 := by
  unfold tailWord_557788
  simp only [CollatzResearch.WordTrace]
  refine ⟨10172099851618406725633009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13562799802157875634177345 10172099851618406725633009)
  ·
    refine ⟨7629074888713805044224757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10172099851618406725633009 7629074888713805044224757)
    ·
      refine ⟨715225770816919222896071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7629074888713805044224757 715225770816919222896071)
      ·
        refine ⟨1072838656225378834344107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 715225770816919222896071 1072838656225378834344107)
        ·
          refine ⟨1609257984338068251516161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1072838656225378834344107 1609257984338068251516161)
          ·
            refine ⟨1206943488253551188637121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1609257984338068251516161 1206943488253551188637121)
            ·
              refine ⟨905207616190163391477841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1206943488253551188637121 905207616190163391477841)
              ·
                refine ⟨678905712142622543608381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 905207616190163391477841 678905712142622543608381)
                ·
                  refine ⟨254589642053483453853143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 678905712142622543608381 254589642053483453853143)
                  ·
                    rfl

theorem cell20_557788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_557788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557788 prefixEnd_557788 := by exact prefixLift 557788
  have htrace : WordTrace (prefixWord ++ tailWord_557788) baseStart_557788 baseEnd_557788 := by
    simpa [prefixWord, tailWord_557788, baseEnd_557788] using wordTrace_append hprefix tailTrace_557788
  have hstable : (prefixWord ++ tailWord_557788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557788).length < 2 ^ (prefixWord ++ tailWord_557788).sum := by decide
  have hdescent : baseEnd_557788 < baseStart_557788 := by decide
  rcases family_descends (prefixWord ++ tailWord_557788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557795 : List Nat := [1, 1, 1, 7, 1, 2, 1, 4, 2]
def baseStart_557795 : Nat := 118140960795 + 557795 * 2 ^ 59
def prefixEnd_557795 : Nat := 4983230072969 + 3 ^ 40 * 557795 * 2
def baseEnd_557795 : Nat := 254592837044222540619781

theorem tailTrace_557795 : CollatzResearch.WordTrace tailWord_557795 prefixEnd_557795 254592837044222540619781 := by
  unfold tailWord_557795
  simp only [CollatzResearch.WordTrace]
  refine ⟨20344455014211453646770839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13562970009474302431180559 20344455014211453646770839)
  ·
    refine ⟨30516682521317180470156259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20344455014211453646770839 30516682521317180470156259)
    ·
      refine ⟨45775023781975770705234389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30516682521317180470156259 45775023781975770705234389)
      ·
        refine ⟨1072852119890057125903931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 45775023781975770705234389 1072852119890057125903931)
        ·
          refine ⟨1609278179835085688855897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1072852119890057125903931 1609278179835085688855897)
          ·
            refine ⟨1206958634876314266641923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1609278179835085688855897 1206958634876314266641923)
            ·
              refine ⟨1810437952314471399962885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1206958634876314266641923 1810437952314471399962885)
              ·
                refine ⟨339457116058963387493041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1810437952314471399962885 339457116058963387493041)
                ·
                  refine ⟨254592837044222540619781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339457116058963387493041 254592837044222540619781)
                  ·
                    rfl

theorem cell20_557795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 2].length) (baseStart_557795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557795 prefixEnd_557795 := by exact prefixLift 557795
  have htrace : WordTrace (prefixWord ++ tailWord_557795) baseStart_557795 baseEnd_557795 := by
    simpa [prefixWord, tailWord_557795, baseEnd_557795] using wordTrace_append hprefix tailTrace_557795
  have hstable : (prefixWord ++ tailWord_557795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557795).length < 2 ^ (prefixWord ++ tailWord_557795).sum := by decide
  have hdescent : baseEnd_557795 < baseStart_557795 := by decide
  rcases family_descends (prefixWord ++ tailWord_557795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557812 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 4]
def baseStart_557812 : Nat := 118140960795 + 557812 * 2 ^ 59
def prefixEnd_557812 : Nat := 4983230072969 + 3 ^ 40 * 557812 * 2
def baseEnd_557812 : Nat := 254600596307446037053045

theorem tailTrace_557812 : CollatzResearch.WordTrace tailWord_557812 prefixEnd_557812 254600596307446037053045 := by
  unfold tailWord_557812
  simp only [CollatzResearch.WordTrace]
  refine ⟨10172537527574932775069845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13563383370099910366759793 10172537527574932775069845)
  ·
    refine ⟨476837696605074973831399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10172537527574932775069845 476837696605074973831399)
    ·
      refine ⟨715256544907612460747099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 476837696605074973831399 715256544907612460747099)
      ·
        refine ⟨1072884817361418691120649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 715256544907612460747099 1072884817361418691120649)
        ·
          refine ⟨804663613021064018340487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1072884817361418691120649 804663613021064018340487)
          ·
            refine ⟨1206995419531596027510731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804663613021064018340487 1206995419531596027510731)
            ·
              refine ⟨1810493129297394041266097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1206995419531596027510731 1810493129297394041266097)
              ·
                refine ⟨1357869846973045530949573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1810493129297394041266097 1357869846973045530949573)
                ·
                  refine ⟨254600596307446037053045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1357869846973045530949573 254600596307446037053045)
                  ·
                    rfl

theorem cell20_557812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_557812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557812 prefixEnd_557812 := by exact prefixLift 557812
  have htrace : WordTrace (prefixWord ++ tailWord_557812) baseStart_557812 baseEnd_557812 := by
    simpa [prefixWord, tailWord_557812, baseEnd_557812] using wordTrace_append hprefix tailTrace_557812
  have hstable : (prefixWord ++ tailWord_557812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557812).length < 2 ^ (prefixWord ++ tailWord_557812).sum := by decide
  have hdescent : baseEnd_557812 < baseStart_557812 := by decide
  rcases family_descends (prefixWord ++ tailWord_557812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557875 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 4]
def baseStart_557875 : Nat := 118140960795 + 557875 * 2 ^ 59
def prefixEnd_557875 : Nat := 4983230072969 + 3 ^ 40 * 557875 * 2
def baseEnd_557875 : Nat := 254629351224097817952787

theorem tailTrace_557875 : CollatzResearch.WordTrace tailWord_557875 prefixEnd_557875 254629351224097817952787 := by
  unfold tailWord_557875
  simp only [CollatzResearch.WordTrace]
  refine ⟨20347372853921627309683079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13564915235947751539788719 20347372853921627309683079)
  ·
    refine ⟨30521059280882440964524619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20347372853921627309683079 30521059280882440964524619)
    ·
      refine ⟨45781588921323661446786929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30521059280882440964524619 45781588921323661446786929)
      ·
        refine ⟨34336191690992746085090197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45781588921323661446786929 34336191690992746085090197)
        ·
          refine ⟨1609508985515284972738603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34336191690992746085090197 1609508985515284972738603)
          ·
            refine ⟨2414263478272927459107905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1609508985515284972738603 2414263478272927459107905)
            ·
              refine ⟨1810697608704695594330929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2414263478272927459107905 1810697608704695594330929)
              ·
                refine ⟨1358023206528521695748197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1810697608704695594330929 1358023206528521695748197)
                ·
                  refine ⟨254629351224097817952787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1358023206528521695748197 254629351224097817952787)
                  ·
                    rfl

theorem cell20_557875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_557875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557875 prefixEnd_557875 := by exact prefixLift 557875
  have htrace : WordTrace (prefixWord ++ tailWord_557875) baseStart_557875 baseEnd_557875 := by
    simpa [prefixWord, tailWord_557875, baseEnd_557875] using wordTrace_append hprefix tailTrace_557875
  have hstable : (prefixWord ++ tailWord_557875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557875).length < 2 ^ (prefixWord ++ tailWord_557875).sum := by decide
  have hdescent : baseEnd_557875 < baseStart_557875 := by decide
  rcases family_descends (prefixWord ++ tailWord_557875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557878 : List Nat := [5, 1, 2, 2, 2, 1, 1, 6]
def baseStart_557878 : Nat := 118140960795 + 557878 * 2 ^ 59
def prefixEnd_557878 : Nat := 4983230072969 + 3 ^ 40 * 557878 * 2
def baseEnd_557878 : Nat := 84876906835281046950925

theorem tailTrace_557878 : CollatzResearch.WordTrace tailWord_557878 prefixEnd_557878 84876906835281046950925 := by
  unfold tailWord_557878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1271717642056922426377643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13564988181940505881361525 1271717642056922426377643)
  ·
    refine ⟨1907576463085383639566465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1271717642056922426377643 1907576463085383639566465)
    ·
      refine ⟨1430682347314037729674849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1907576463085383639566465 1430682347314037729674849)
      ·
        refine ⟨1073011760485528297256137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1430682347314037729674849 1073011760485528297256137)
        ·
          refine ⟨804758820364146222942103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1073011760485528297256137 804758820364146222942103)
          ·
            refine ⟨1207138230546219334413155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804758820364146222942103 1207138230546219334413155)
            ·
              refine ⟨1810707345819329001619733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1207138230546219334413155 1810707345819329001619733)
              ·
                refine ⟨84876906835281046950925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1810707345819329001619733 84876906835281046950925)
                ·
                  rfl

theorem cell20_557878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_557878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557878 prefixEnd_557878 := by exact prefixLift 557878
  have htrace : WordTrace (prefixWord ++ tailWord_557878) baseStart_557878 baseEnd_557878 := by
    simpa [prefixWord, tailWord_557878, baseEnd_557878] using wordTrace_append hprefix tailTrace_557878
  have hstable : (prefixWord ++ tailWord_557878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557878).length < 2 ^ (prefixWord ++ tailWord_557878).sum := by decide
  have hdescent : baseEnd_557878 < baseStart_557878 := by decide
  rcases family_descends (prefixWord ++ tailWord_557878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557906 : List Nat := [3, 2, 2, 1, 1, 2, 2, 4, 3]
def baseStart_557906 : Nat := 118140960795 + 557906 * 2 ^ 59
def prefixEnd_557906 : Nat := 4983230072969 + 3 ^ 40 * 557906 * 2
def baseEnd_557906 : Nat := 254643500468799487919327

theorem tailTrace_557906 : CollatzResearch.WordTrace tailWord_557906 prefixEnd_557906 254643500468799487919327 := by
  unfold tailWord_557906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5087125879202329901015393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13565669011206213069374381 5087125879202329901015393)
  ·
    refine ⟨3815344409401747425761545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5087125879202329901015393 3815344409401747425761545)
    ·
      refine ⟨2861508307051310569321159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3815344409401747425761545 2861508307051310569321159)
      ·
        refine ⟨4292262460576965853981739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2861508307051310569321159 4292262460576965853981739)
        ·
          refine ⟨6438393690865448780972609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4292262460576965853981739 6438393690865448780972609)
          ·
            refine ⟨4828795268149086585729457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6438393690865448780972609 4828795268149086585729457)
            ·
              refine ⟨3621596451111814939297093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4828795268149086585729457 3621596451111814939297093)
              ·
                refine ⟨679049334583465301118205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3621596451111814939297093 679049334583465301118205)
                ·
                  refine ⟨254643500468799487919327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679049334583465301118205 254643500468799487919327)
                  ·
                    rfl

theorem cell20_557906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_557906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557906 prefixEnd_557906 := by exact prefixLift 557906
  have htrace : WordTrace (prefixWord ++ tailWord_557906) baseStart_557906 baseEnd_557906 := by
    simpa [prefixWord, tailWord_557906, baseEnd_557906] using wordTrace_append hprefix tailTrace_557906
  have hstable : (prefixWord ++ tailWord_557906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557906).length < 2 ^ (prefixWord ++ tailWord_557906).sum := by decide
  have hdescent : baseEnd_557906 < baseStart_557906 := by decide
  rcases family_descends (prefixWord ++ tailWord_557906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557909 : List Nat := [1, 3, 2, 2, 2, 1, 5, 2, 2]
def baseStart_557909 : Nat := 118140960795 + 557909 * 2 ^ 59
def prefixEnd_557909 : Nat := 4983230072969 + 3 ^ 40 * 557909 * 2
def baseEnd_557909 : Nat := 254644869750544810819315

theorem tailTrace_557909 : CollatzResearch.WordTrace tailWord_557909 prefixEnd_557909 254644869750544810819315 := by
  unfold tailWord_557909
  simp only [CollatzResearch.WordTrace]
  refine ⟨20348612935798451116420781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13565741957198967410947187 20348612935798451116420781)
  ·
    refine ⟨7630729850924419168657793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20348612935798451116420781 7630729850924419168657793)
    ·
      refine ⟨5723047388193314376493345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7630729850924419168657793 5723047388193314376493345)
      ·
        refine ⟨4292285541144985782370009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5723047388193314376493345 4292285541144985782370009)
        ·
          refine ⟨3219214155858739336777507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4292285541144985782370009 3219214155858739336777507)
          ·
            refine ⟨4828821233788109005166261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3219214155858739336777507 4828821233788109005166261)
            ·
              refine ⟨452701990667635219234337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4828821233788109005166261 452701990667635219234337)
              ·
                refine ⟨339526493000726414425753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 452701990667635219234337 339526493000726414425753)
                ·
                  refine ⟨254644869750544810819315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339526493000726414425753 254644869750544810819315)
                  ·
                    rfl

theorem cell20_557909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_557909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557909 prefixEnd_557909 := by exact prefixLift 557909
  have htrace : WordTrace (prefixWord ++ tailWord_557909) baseStart_557909 baseEnd_557909 := by
    simpa [prefixWord, tailWord_557909, baseEnd_557909] using wordTrace_append hprefix tailTrace_557909
  have hstable : (prefixWord ++ tailWord_557909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557909).length < 2 ^ (prefixWord ++ tailWord_557909).sum := by decide
  have hdescent : baseEnd_557909 < baseStart_557909 := by decide
  rcases family_descends (prefixWord ++ tailWord_557909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557913 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 4]
def baseStart_557913 : Nat := 118140960795 + 557913 * 2 ^ 59
def prefixEnd_557913 : Nat := 4983230072969 + 3 ^ 40 * 557913 * 2
def baseEnd_557913 : Nat := 254646695459538574685965

theorem tailTrace_557913 : CollatzResearch.WordTrace tailWord_557913 prefixEnd_557913 254646695459538574685965 := by
  unfold tailWord_557913
  simp only [CollatzResearch.WordTrace]
  refine ⟨20348758827783959799566393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13565839218522639866377595 20348758827783959799566393)
  ·
    refine ⟨15261569120837969849674795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20348758827783959799566393 15261569120837969849674795)
    ·
      refine ⟨22892353681256954774512193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15261569120837969849674795 22892353681256954774512193)
      ·
        refine ⟨17169265260942716080884145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22892353681256954774512193 17169265260942716080884145)
        ·
          refine ⟨12876948945707037060663109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17169265260942716080884145 12876948945707037060663109)
          ·
            refine ⟨2414427927320069448874333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12876948945707037060663109 2414427927320069448874333)
            ·
              refine ⟨905410472745026043327875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2414427927320069448874333 905410472745026043327875)
              ·
                refine ⟨1358115709117539064991813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 905410472745026043327875 1358115709117539064991813)
                ·
                  refine ⟨254646695459538574685965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1358115709117539064991813 254646695459538574685965)
                  ·
                    rfl

theorem cell20_557913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_557913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557913 prefixEnd_557913 := by exact prefixLift 557913
  have htrace : WordTrace (prefixWord ++ tailWord_557913) baseStart_557913 baseEnd_557913 := by
    simpa [prefixWord, tailWord_557913, baseEnd_557913] using wordTrace_append hprefix tailTrace_557913
  have hstable : (prefixWord ++ tailWord_557913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557913).length < 2 ^ (prefixWord ++ tailWord_557913).sum := by decide
  have hdescent : baseEnd_557913 < baseStart_557913 := by decide
  rcases family_descends (prefixWord ++ tailWord_557913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557920 : List Nat := [2, 1, 1, 3, 3, 1, 4, 5]
def baseStart_557920 : Nat := 118140960795 + 557920 * 2 ^ 59
def prefixEnd_557920 : Nat := 4983230072969 + 3 ^ 40 * 557920 * 2
def baseEnd_557920 : Nat := 84883296816759220484201

theorem tailTrace_557920 : CollatzResearch.WordTrace tailWord_557920 prefixEnd_557920 84883296816759220484201 := by
  unfold tailWord_557920
  simp only [CollatzResearch.WordTrace]
  refine ⟨10174507069379299997535607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13566009425839066663380809 10174507069379299997535607)
  ·
    refine ⟨15261760604068949996303411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10174507069379299997535607 15261760604068949996303411)
    ·
      refine ⟨22892640906103424994455117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15261760604068949996303411 22892640906103424994455117)
      ·
        refine ⟨8584740339788784372920669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22892640906103424994455117 8584740339788784372920669)
        ·
          refine ⟨3219277627420794139845251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8584740339788784372920669 3219277627420794139845251)
          ·
            refine ⟨4828916441131191209767877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3219277627420794139845251 4828916441131191209767877)
            ·
              refine ⟨905421832712098351831477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4828916441131191209767877 905421832712098351831477)
              ·
                refine ⟨84883296816759220484201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 905421832712098351831477 84883296816759220484201)
                ·
                  rfl

theorem cell20_557920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_557920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557920 prefixEnd_557920 := by exact prefixLift 557920
  have htrace : WordTrace (prefixWord ++ tailWord_557920) baseStart_557920 baseEnd_557920 := by
    simpa [prefixWord, tailWord_557920, baseEnd_557920] using wordTrace_append hprefix tailTrace_557920
  have hstable : (prefixWord ++ tailWord_557920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557920).length < 2 ^ (prefixWord ++ tailWord_557920).sum := by decide
  have hdescent : baseEnd_557920 < baseStart_557920 := by decide
  rcases family_descends (prefixWord ++ tailWord_557920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557923 : List Nat := [1, 1, 1, 5, 3, 1, 4, 1, 3]
def baseStart_557923 : Nat := 118140960795 + 557923 * 2 ^ 59
def prefixEnd_557923 : Nat := 4983230072969 + 3 ^ 40 * 557923 * 2
def baseEnd_557923 : Nat := 254651259732022984352591

theorem tailTrace_557923 : CollatzResearch.WordTrace tailWord_557923 prefixEnd_557923 254651259732022984352591 := by
  unfold tailWord_557923
  simp only [CollatzResearch.WordTrace]
  refine ⟨20349123557747731507430423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13566082371831821004953615 20349123557747731507430423)
  ·
    refine ⟨30523685336621597261145635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20349123557747731507430423 30523685336621597261145635)
    ·
      refine ⟨45785528004932395891718453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30523685336621597261145635 45785528004932395891718453)
      ·
        refine ⟨4292393250462412114848605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45785528004932395891718453 4292393250462412114848605)
        ·
          refine ⟨1609647468923404543068227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4292393250462412114848605 1609647468923404543068227)
          ·
            refine ⟨2414471203385106814602341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1609647468923404543068227 2414471203385106814602341)
            ·
              refine ⟨452713350634707527737939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2414471203385106814602341 452713350634707527737939)
              ·
                refine ⟨679070025952061291606909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452713350634707527737939 679070025952061291606909)
                ·
                  refine ⟨254651259732022984352591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679070025952061291606909 254651259732022984352591)
                  ·
                    rfl

theorem cell20_557923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 3].length) (baseStart_557923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557923 prefixEnd_557923 := by exact prefixLift 557923
  have htrace : WordTrace (prefixWord ++ tailWord_557923) baseStart_557923 baseEnd_557923 := by
    simpa [prefixWord, tailWord_557923, baseEnd_557923] using wordTrace_append hprefix tailTrace_557923
  have hstable : (prefixWord ++ tailWord_557923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557923).length < 2 ^ (prefixWord ++ tailWord_557923).sum := by decide
  have hdescent : baseEnd_557923 < baseStart_557923 := by decide
  rcases family_descends (prefixWord ++ tailWord_557923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557954 : List Nat := [3, 4, 2, 2, 1, 8]
def baseStart_557954 : Nat := 118140960795 + 557954 * 2 ^ 59
def prefixEnd_557954 : Nat := 4983230072969 + 3 ^ 40 * 557954 * 2
def baseEnd_557954 : Nat := 9432052184323135345153

theorem tailTrace_557954 : CollatzResearch.WordTrace tailWord_557954 prefixEnd_557954 9432052184323135345153 := by
  unfold tailWord_557954
  simp only [CollatzResearch.WordTrace]
  refine ⟨5087563555158855950452229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13566836147090282534539277 5087563555158855950452229)
  ·
    refine ⟨953918166592285490709793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5087563555158855950452229 953918166592285490709793)
    ·
      refine ⟨715438624944214118032345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 953918166592285490709793 715438624944214118032345)
      ·
        refine ⟨536578968708160588524259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 715438624944214118032345 536578968708160588524259)
        ·
          refine ⟨804868453062240882786389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536578968708160588524259 804868453062240882786389)
          ·
            refine ⟨9432052184323135345153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 804868453062240882786389 9432052184323135345153)
            ·
              rfl

theorem cell20_557954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 8].length) (baseStart_557954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_557954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_557954 prefixEnd_557954 := by exact prefixLift 557954
  have htrace : WordTrace (prefixWord ++ tailWord_557954) baseStart_557954 baseEnd_557954 := by
    simpa [prefixWord, tailWord_557954, baseEnd_557954] using wordTrace_append hprefix tailTrace_557954
  have hstable : (prefixWord ++ tailWord_557954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557954).length < 2 ^ (prefixWord ++ tailWord_557954).sum := by decide
  have hdescent : baseEnd_557954 < baseStart_557954 := by decide
  rcases family_descends (prefixWord ++ tailWord_557954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558010 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_558010 : Nat := 118140960795 + 558010 * 2 ^ 59
def prefixEnd_558010 : Nat := 4983230072969 + 3 ^ 40 * 558010 * 2
def baseEnd_558010 : Nat := 254690968902637348452235

theorem tailTrace_558010 : CollatzResearch.WordTrace tailWord_558010 prefixEnd_558010 254690968902637348452235 := by
  unfold tailWord_558010
  simp only [CollatzResearch.WordTrace]
  refine ⟨5088074177108136341461871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13568197805621696910564989 5088074177108136341461871)
  ·
    refine ⟨7632111265662204512192807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5088074177108136341461871 7632111265662204512192807)
    ·
      refine ⟨11448166898493306768289211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7632111265662204512192807 11448166898493306768289211)
      ·
        refine ⟨17172250347739960152433817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11448166898493306768289211 17172250347739960152433817)
        ·
          refine ⟨12879187760804970114325363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17172250347739960152433817 12879187760804970114325363)
          ·
            refine ⟨19318781641207455171488045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12879187760804970114325363 19318781641207455171488045)
            ·
              refine ⟨7244543115452795689308017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19318781641207455171488045 7244543115452795689308017)
              ·
                refine ⟨5433407336589596766981013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7244543115452795689308017 5433407336589596766981013)
                ·
                  refine ⟨254690968902637348452235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5433407336589596766981013 254690968902637348452235)
                  ·
                    rfl

theorem cell20_558010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_558010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558010 prefixEnd_558010 := by exact prefixLift 558010
  have htrace : WordTrace (prefixWord ++ tailWord_558010) baseStart_558010 baseEnd_558010 := by
    simpa [prefixWord, tailWord_558010, baseEnd_558010] using wordTrace_append hprefix tailTrace_558010
  have hstable : (prefixWord ++ tailWord_558010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558010).length < 2 ^ (prefixWord ++ tailWord_558010).sum := by decide
  have hdescent : baseEnd_558010 < baseStart_558010 := by decide
  rcases family_descends (prefixWord ++ tailWord_558010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558027 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 4]
def baseStart_558027 : Nat := 118140960795 + 558027 * 2 ^ 59
def prefixEnd_558027 : Nat := 4983230072969 + 3 ^ 40 * 558027 * 2
def baseEnd_558027 : Nat := 254698728165860844885499

theorem tailTrace_558027 : CollatzResearch.WordTrace tailWord_558027 prefixEnd_558027 254698728165860844885499 := by
  unfold tailWord_558027
  simp only [CollatzResearch.WordTrace]
  refine ⟨20352916749370957269216335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13568611166247304846144223 20352916749370957269216335)
  ·
    refine ⟨30529375124056435903824503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20352916749370957269216335 30529375124056435903824503)
    ·
      refine ⟨45794062686084653855736755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30529375124056435903824503 45794062686084653855736755)
      ·
        refine ⟨68691094029126980783605133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45794062686084653855736755 68691094029126980783605133)
        ·
          refine ⟨25759160260922617793851925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68691094029126980783605133 25759160260922617793851925)
          ·
            refine ⟨1207460637230747709086809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25759160260922617793851925 1207460637230747709086809)
            ·
              refine ⟨905595477923060781815107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1207460637230747709086809 905595477923060781815107)
              ·
                refine ⟨1358393216884591172722661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 905595477923060781815107 1358393216884591172722661)
                ·
                  refine ⟨254698728165860844885499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1358393216884591172722661 254698728165860844885499)
                  ·
                    rfl

theorem cell20_558027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 4].length) (baseStart_558027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558027 prefixEnd_558027 := by exact prefixLift 558027
  have htrace : WordTrace (prefixWord ++ tailWord_558027) baseStart_558027 baseEnd_558027 := by
    simpa [prefixWord, tailWord_558027, baseEnd_558027] using wordTrace_append hprefix tailTrace_558027
  have hstable : (prefixWord ++ tailWord_558027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558027).length < 2 ^ (prefixWord ++ tailWord_558027).sum := by decide
  have hdescent : baseEnd_558027 < baseStart_558027 := by decide
  rcases family_descends (prefixWord ++ tailWord_558027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558078 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 4]
def baseStart_558078 : Nat := 118140960795 + 558078 * 2 ^ 59
def prefixEnd_558078 : Nat := 4983230072969 + 3 ^ 40 * 558078 * 2
def baseEnd_558078 : Nat := 254722005955531334185291

theorem tailTrace_558078 : CollatzResearch.WordTrace tailWord_558078 prefixEnd_558078 254722005955531334185291 := by
  unfold tailWord_558078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2544347109023274122415361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13569851248124128652881925 2544347109023274122415361)
  ·
    refine ⟨1908260331767455591811521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2544347109023274122415361 1908260331767455591811521)
    ·
      refine ⟨1431195248825591693858641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1908260331767455591811521 1431195248825591693858641)
      ·
        refine ⟨1073396436619193770393981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1431195248825591693858641 1073396436619193770393981)
        ·
          refine ⟨402523663732197663897743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1073396436619193770393981 402523663732197663897743)
          ·
            refine ⟨603785495598296495846615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402523663732197663897743 603785495598296495846615)
            ·
              refine ⟨905678243397444743769923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 603785495598296495846615 905678243397444743769923)
              ·
                refine ⟨1358517365096167115654885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 905678243397444743769923 1358517365096167115654885)
                ·
                  refine ⟨254722005955531334185291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1358517365096167115654885 254722005955531334185291)
                  ·
                    rfl

theorem cell20_558078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_558078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558078 prefixEnd_558078 := by exact prefixLift 558078
  have htrace : WordTrace (prefixWord ++ tailWord_558078) baseStart_558078 baseEnd_558078 := by
    simpa [prefixWord, tailWord_558078, baseEnd_558078] using wordTrace_append hprefix tailTrace_558078
  have hstable : (prefixWord ++ tailWord_558078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558078).length < 2 ^ (prefixWord ++ tailWord_558078).sum := by decide
  have hdescent : baseEnd_558078 < baseStart_558078 := by decide
  rcases family_descends (prefixWord ++ tailWord_558078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558137 : List Nat := [1, 2, 1, 5, 2, 1, 4, 2, 2]
def baseStart_558137 : Nat := 118140960795 + 558137 * 2 ^ 59
def prefixEnd_558137 : Nat := 4983230072969 + 3 ^ 40 * 558137 * 2
def baseEnd_558137 : Nat := 254748935163189351218383

theorem tailTrace_558137 : CollatzResearch.WordTrace tailWord_558137 prefixEnd_558137 254748935163189351218383 := by
  unfold tailWord_558137
  simp only [CollatzResearch.WordTrace]
  refine ⟨20356928778972446055720665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13571285852648297370480443 20356928778972446055720665)
  ·
    refine ⟨15267696584229334541790499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20356928778972446055720665 15267696584229334541790499)
    ·
      refine ⟨22901544876344001812685749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15267696584229334541790499 22901544876344001812685749)
      ·
        refine ⟨2147019832157250169939289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22901544876344001812685749 2147019832157250169939289)
        ·
          refine ⟨1610264874117937627454467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2147019832157250169939289 1610264874117937627454467)
          ·
            refine ⟨2415397311176906441181701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1610264874117937627454467 2415397311176906441181701)
            ·
              refine ⟨452886995845669957721569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2415397311176906441181701 452886995845669957721569)
              ·
                refine ⟨339665246884252468291177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 452886995845669957721569 339665246884252468291177)
                ·
                  refine ⟨254748935163189351218383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339665246884252468291177 254748935163189351218383)
                  ·
                    rfl

theorem cell20_558137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 2].length) (baseStart_558137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558137 prefixEnd_558137 := by exact prefixLift 558137
  have htrace : WordTrace (prefixWord ++ tailWord_558137) baseStart_558137 baseEnd_558137 := by
    simpa [prefixWord, tailWord_558137, baseEnd_558137] using wordTrace_append hprefix tailTrace_558137
  have hstable : (prefixWord ++ tailWord_558137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558137).length < 2 ^ (prefixWord ++ tailWord_558137).sum := by decide
  have hdescent : baseEnd_558137 < baseStart_558137 := by decide
  rcases family_descends (prefixWord ++ tailWord_558137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558186 : List Nat := [3, 1, 3, 2, 2, 2, 7]
def baseStart_558186 : Nat := 118140960795 + 558186 * 2 ^ 59
def prefixEnd_558186 : Nat := 4983230072969 + 3 ^ 40 * 558186 * 2
def baseEnd_558186 : Nat := 28307922233151439842761

theorem tailTrace_558186 : CollatzResearch.WordTrace tailWord_558186 prefixEnd_558186 28307922233151439842761 := by
  unfold tailWord_558186
  simp only [CollatzResearch.WordTrace]
  refine ⟨5089678988948731856063603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13572477303863284949502941 5089678988948731856063603)
  ·
    refine ⟨7634518483423097784095405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5089678988948731856063603 7634518483423097784095405)
    ·
      refine ⟨2862944431283661669035777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7634518483423097784095405 2862944431283661669035777)
      ·
        refine ⟨2147208323462746251776833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2862944431283661669035777 2147208323462746251776833)
        ·
          refine ⟨1610406242597059688832625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2147208323462746251776833 1610406242597059688832625)
          ·
            refine ⟨1207804681947794766624469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1610406242597059688832625 1207804681947794766624469)
            ·
              refine ⟨28307922233151439842761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1207804681947794766624469 28307922233151439842761)
              ·
                rfl

theorem cell20_558186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 7].length) (baseStart_558186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558186 prefixEnd_558186 := by exact prefixLift 558186
  have htrace : WordTrace (prefixWord ++ tailWord_558186) baseStart_558186 baseEnd_558186 := by
    simpa [prefixWord, tailWord_558186, baseEnd_558186] using wordTrace_append hprefix tailTrace_558186
  have hstable : (prefixWord ++ tailWord_558186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558186).length < 2 ^ (prefixWord ++ tailWord_558186).sum := by decide
  have hdescent : baseEnd_558186 < baseStart_558186 := by decide
  rcases family_descends (prefixWord ++ tailWord_558186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558189 : List Nat := [1, 5, 1, 1, 2, 4, 1, 2, 3]
def baseStart_558189 : Nat := 118140960795 + 558189 * 2 ^ 59
def prefixEnd_558189 : Nat := 4983230072969 + 3 ^ 40 * 558189 * 2
def baseEnd_558189 : Nat := 254772669380108281484837

theorem tailTrace_558189 : CollatzResearch.WordTrace tailWord_558189 prefixEnd_558189 254772669380108281484837 := by
  unfold tailWord_558189
  simp only [CollatzResearch.WordTrace]
  refine ⟨20358825374784058936613621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13572550249856039291075747 20358825374784058936613621)
  ·
    refine ⟨1908639878886005525307527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20358825374784058936613621 1908639878886005525307527)
    ·
      refine ⟨2862959818329008287961291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1908639878886005525307527 2862959818329008287961291)
      ·
        refine ⟨4294439727493512431941937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2862959818329008287961291 4294439727493512431941937)
        ·
          refine ⟨3220829795620134323956453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4294439727493512431941937 3220829795620134323956453)
          ·
            refine ⟨603905586678775185741835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3220829795620134323956453 603905586678775185741835)
            ·
              refine ⟨905858380018162778612753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 603905586678775185741835 905858380018162778612753)
              ·
                refine ⟨679393785013622083959565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 905858380018162778612753 679393785013622083959565)
                ·
                  refine ⟨254772669380108281484837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679393785013622083959565 254772669380108281484837)
                  ·
                    rfl

theorem cell20_558189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_558189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558189 prefixEnd_558189 := by exact prefixLift 558189
  have htrace : WordTrace (prefixWord ++ tailWord_558189) baseStart_558189 baseEnd_558189 := by
    simpa [prefixWord, tailWord_558189, baseEnd_558189] using wordTrace_append hprefix tailTrace_558189
  have hstable : (prefixWord ++ tailWord_558189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558189).length < 2 ^ (prefixWord ++ tailWord_558189).sum := by decide
  have hdescent : baseEnd_558189 < baseStart_558189 := by decide
  rcases family_descends (prefixWord ++ tailWord_558189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558193 : List Nat := [1, 2, 2, 2, 1, 1, 2, 6, 3]
def baseStart_558193 : Nat := 118140960795 + 558193 * 2 ^ 59
def prefixEnd_558193 : Nat := 4983230072969 + 3 ^ 40 * 558193 * 2
def baseEnd_558193 : Nat := 254774495089102045351487

theorem tailTrace_558193 : CollatzResearch.WordTrace tailWord_558193 prefixEnd_558193 254774495089102045351487 := by
  unfold tailWord_558193
  simp only [CollatzResearch.WordTrace]
  refine ⟨20358971266769567619759233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13572647511179711746506155 20358971266769567619759233)
  ·
    refine ⟨15269228450077175714819425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20358971266769567619759233 15269228450077175714819425)
    ·
      refine ⟨11451921337557881786114569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15269228450077175714819425 11451921337557881786114569)
      ·
        refine ⟨8588941003168411339585927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11451921337557881786114569 8588941003168411339585927)
        ·
          refine ⟨12883411504752617009378891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8588941003168411339585927 12883411504752617009378891)
          ·
            refine ⟨19325117257128925514068337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12883411504752617009378891 19325117257128925514068337)
            ·
              refine ⟨14493837942846694135551253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19325117257128925514068337 14493837942846694135551253)
              ·
                refine ⟨679398653570938787603965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14493837942846694135551253 679398653570938787603965)
                ·
                  refine ⟨254774495089102045351487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679398653570938787603965 254774495089102045351487)
                  ·
                    rfl

theorem cell20_558193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_558193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558193 prefixEnd_558193 := by exact prefixLift 558193
  have htrace : WordTrace (prefixWord ++ tailWord_558193) baseStart_558193 baseEnd_558193 := by
    simpa [prefixWord, tailWord_558193, baseEnd_558193] using wordTrace_append hprefix tailTrace_558193
  have hstable : (prefixWord ++ tailWord_558193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558193).length < 2 ^ (prefixWord ++ tailWord_558193).sum := by decide
  have hdescent : baseEnd_558193 < baseStart_558193 := by decide
  rcases family_descends (prefixWord ++ tailWord_558193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558200 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 4]
def baseStart_558200 : Nat := 118140960795 + 558200 * 2 ^ 59
def prefixEnd_558200 : Nat := 4983230072969 + 3 ^ 40 * 558200 * 2
def baseEnd_558200 : Nat := 254777690079841132118125

theorem tailTrace_558200 : CollatzResearch.WordTrace tailWord_558200 prefixEnd_558200 254777690079841132118125 := by
  unfold tailWord_558200
  simp only [CollatzResearch.WordTrace]
  refine ⟨10179613288872103907632027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13572817718496138543509369 10179613288872103907632027)
  ·
    refine ⟨15269419933308155861448041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10179613288872103907632027 15269419933308155861448041)
    ·
      refine ⟨11452064949981116896086031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15269419933308155861448041 11452064949981116896086031)
      ·
        refine ⟨17178097424971675344129047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11452064949981116896086031 17178097424971675344129047)
        ·
          refine ⟨25767146137457513016193571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17178097424971675344129047 25767146137457513016193571)
          ·
            refine ⟨38650719206186269524290357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25767146137457513016193571 38650719206186269524290357)
            ·
              refine ⟨3623504925579962767902221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38650719206186269524290357 3623504925579962767902221)
              ·
                refine ⟨1358814347092486037963333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3623504925579962767902221 1358814347092486037963333)
                ·
                  refine ⟨254777690079841132118125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1358814347092486037963333 254777690079841132118125)
                  ·
                    rfl

theorem cell20_558200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_558200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558200 prefixEnd_558200 := by exact prefixLift 558200
  have htrace : WordTrace (prefixWord ++ tailWord_558200) baseStart_558200 baseEnd_558200 := by
    simpa [prefixWord, tailWord_558200, baseEnd_558200] using wordTrace_append hprefix tailTrace_558200
  have hstable : (prefixWord ++ tailWord_558200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558200).length < 2 ^ (prefixWord ++ tailWord_558200).sum := by decide
  have hdescent : baseEnd_558200 < baseStart_558200 := by decide
  rcases family_descends (prefixWord ++ tailWord_558200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558231 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 5]
def baseStart_558231 : Nat := 118140960795 + 558231 * 2 ^ 59
def prefixEnd_558231 : Nat := 4983230072969 + 3 ^ 40 * 558231 * 2
def baseEnd_558231 : Nat := 254791839324542802084665

theorem tailTrace_558231 : CollatzResearch.WordTrace tailWord_558231 prefixEnd_558231 254791839324542802084665 := by
  unfold tailWord_558231
  simp only [CollatzResearch.WordTrace]
  refine ⟨20360357240631900109642547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13573571493754600073095031 20360357240631900109642547)
  ·
    refine ⟨30540535860947850164463821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20360357240631900109642547 30540535860947850164463821)
    ·
      refine ⟨11452700947855443811673933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30540535860947850164463821 11452700947855443811673933)
      ·
        refine ⟨4294762855445791429377725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11452700947855443811673933 4294762855445791429377725)
        ·
          refine ⟨1610536070792171786016647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4294762855445791429377725 1610536070792171786016647)
          ·
            refine ⟨2415804106188257679024971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1610536070792171786016647 2415804106188257679024971)
            ·
              refine ⟨3623706159282386518537457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2415804106188257679024971 3623706159282386518537457)
              ·
                refine ⟨2717779619461789888903093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3623706159282386518537457 2717779619461789888903093)
                ·
                  refine ⟨254791839324542802084665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2717779619461789888903093 254791839324542802084665)
                  ·
                    rfl

theorem cell20_558231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_558231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558231 prefixEnd_558231 := by exact prefixLift 558231
  have htrace : WordTrace (prefixWord ++ tailWord_558231) baseStart_558231 baseEnd_558231 := by
    simpa [prefixWord, tailWord_558231, baseEnd_558231] using wordTrace_append hprefix tailTrace_558231
  have hstable : (prefixWord ++ tailWord_558231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558231).length < 2 ^ (prefixWord ++ tailWord_558231).sum := by decide
  have hdescent : baseEnd_558231 < baseStart_558231 := by decide
  rcases family_descends (prefixWord ++ tailWord_558231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558245 : List Nat := [1, 3, 1, 2, 1, 4, 8]
def baseStart_558245 : Nat := 118140960795 + 558245 * 2 ^ 59
def prefixEnd_558245 : Nat := 4983230072969 + 3 ^ 40 * 558245 * 2
def baseEnd_558245 : Nat := 28310914367335663957549

theorem tailTrace_558245 : CollatzResearch.WordTrace tailWord_558245 prefixEnd_558245 28310914367335663957549 := by
  unfold tailWord_558245
  simp only [CollatzResearch.WordTrace]
  refine ⟨20360867862581180500652189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13573911908387453667101459 20360867862581180500652189)
  ·
    refine ⟨7635325448467942687744571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20360867862581180500652189 7635325448467942687744571)
    ·
      refine ⟨11452988172701914031616857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7635325448467942687744571 11452988172701914031616857)
      ·
        refine ⟨8589741129526435523712643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11452988172701914031616857 8589741129526435523712643)
        ·
          refine ⟨12884611694289653285568965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8589741129526435523712643 12884611694289653285568965)
          ·
            refine ⟨2415864692679309991044181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12884611694289653285568965 2415864692679309991044181)
            ·
              refine ⟨28310914367335663957549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2415864692679309991044181 28310914367335663957549)
              ·
                rfl

theorem cell20_558245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 8].length) (baseStart_558245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558245 prefixEnd_558245 := by exact prefixLift 558245
  have htrace : WordTrace (prefixWord ++ tailWord_558245) baseStart_558245 baseEnd_558245 := by
    simpa [prefixWord, tailWord_558245, baseEnd_558245] using wordTrace_append hprefix tailTrace_558245
  have hstable : (prefixWord ++ tailWord_558245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558245).length < 2 ^ (prefixWord ++ tailWord_558245).sum := by decide
  have hdescent : baseEnd_558245 < baseStart_558245 := by decide
  rcases family_descends (prefixWord ++ tailWord_558245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558255 : List Nat := [1, 1, 2, 1, 2, 3, 2, 6, 2]
def baseStart_558255 : Nat := 118140960795 + 558255 * 2 ^ 59
def prefixEnd_558255 : Nat := 4983230072969 + 3 ^ 40 * 558255 * 2
def baseEnd_558255 : Nat := 254802793578505385284567

theorem tailTrace_558255 : CollatzResearch.WordTrace tailWord_558255 prefixEnd_558255 254802793578505385284567 := by
  unfold tailWord_558255
  simp only [CollatzResearch.WordTrace]
  refine ⟨20361232592544952208516219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13574155061696634805677479 20361232592544952208516219)
  ·
    refine ⟨30541848888817428312774329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20361232592544952208516219 30541848888817428312774329)
    ·
      refine ⟨22906386666613071234580747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30541848888817428312774329 22906386666613071234580747)
      ·
        refine ⟨34359579999919606851871121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22906386666613071234580747 34359579999919606851871121)
        ·
          refine ⟨25769684999939705138903341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34359579999919606851871121 25769684999939705138903341)
          ·
            refine ⟨9663631874977389427088753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25769684999939705138903341 9663631874977389427088753)
            ·
              refine ⟨7247723906233042070316565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9663631874977389427088753 7247723906233042070316565)
              ·
                refine ⟨339737058104673847046089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7247723906233042070316565 339737058104673847046089)
                ·
                  refine ⟨254802793578505385284567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339737058104673847046089 254802793578505385284567)
                  ·
                    rfl

theorem cell20_558255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 2].length) (baseStart_558255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558255 prefixEnd_558255 := by exact prefixLift 558255
  have htrace : WordTrace (prefixWord ++ tailWord_558255) baseStart_558255 baseEnd_558255 := by
    simpa [prefixWord, tailWord_558255, baseEnd_558255] using wordTrace_append hprefix tailTrace_558255
  have hstable : (prefixWord ++ tailWord_558255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558255).length < 2 ^ (prefixWord ++ tailWord_558255).sum := by decide
  have hdescent : baseEnd_558255 < baseStart_558255 := by decide
  rcases family_descends (prefixWord ++ tailWord_558255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558265 : List Nat := [1, 2, 1, 4, 1, 5, 2, 1, 3]
def baseStart_558265 : Nat := 118140960795 + 558265 * 2 ^ 59
def prefixEnd_558265 : Nat := 4983230072969 + 3 ^ 40 * 558265 * 2
def baseEnd_558265 : Nat := 254807357850989794951193

theorem tailTrace_558265 : CollatzResearch.WordTrace tailWord_558265 prefixEnd_558265 254807357850989794951193 := by
  unfold tailWord_558265
  simp only [CollatzResearch.WordTrace]
  refine ⟨20361597322508723916380249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13574398215005815944253499 20361597322508723916380249)
  ·
    refine ⟨15271197991881542937285187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20361597322508723916380249 15271197991881542937285187)
    ·
      refine ⟨22906796987822314405927781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15271197991881542937285187 22906796987822314405927781)
      ·
        refine ⟨4295024435216683951111459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22906796987822314405927781 4295024435216683951111459)
        ·
          refine ⟨6442536652825025926667189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4295024435216683951111459 6442536652825025926667189)
          ·
            refine ⟨603987811202346180625049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6442536652825025926667189 603987811202346180625049)
            ·
              refine ⟨452990858401759635468787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 603987811202346180625049 452990858401759635468787)
              ·
                refine ⟨679486287602639453203181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452990858401759635468787 679486287602639453203181)
                ·
                  refine ⟨254807357850989794951193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679486287602639453203181 254807357850989794951193)
                  ·
                    rfl

theorem cell20_558265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_558265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558265 prefixEnd_558265 := by exact prefixLift 558265
  have htrace : WordTrace (prefixWord ++ tailWord_558265) baseStart_558265 baseEnd_558265 := by
    simpa [prefixWord, tailWord_558265, baseEnd_558265] using wordTrace_append hprefix tailTrace_558265
  have hstable : (prefixWord ++ tailWord_558265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558265).length < 2 ^ (prefixWord ++ tailWord_558265).sum := by decide
  have hdescent : baseEnd_558265 < baseStart_558265 := by decide
  rcases family_descends (prefixWord ++ tailWord_558265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558317 : List Nat := [1, 5, 1, 2, 2, 3, 1, 5]
def baseStart_558317 : Nat := 118140960795 + 558317 * 2 ^ 59
def prefixEnd_558317 : Nat := 4983230072969 + 3 ^ 40 * 558317 * 2
def baseEnd_558317 : Nat := 84943697355969575072549

theorem tailTrace_558317 : CollatzResearch.WordTrace tailWord_558317 prefixEnd_558317 84943697355969575072549 := by
  unfold tailWord_558317
  simp only [CollatzResearch.WordTrace]
  refine ⟨20363493918320336797273205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13575662612213557864848803 20363493918320336797273205)
  ·
    refine ⟨1909077554842531574744363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20363493918320336797273205 1909077554842531574744363)
    ·
      refine ⟨2863616332263797362116545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1909077554842531574744363 2863616332263797362116545)
      ·
        refine ⟨2147712249197848021587409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2863616332263797362116545 2147712249197848021587409)
        ·
          refine ⟨1610784186898386016190557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2147712249197848021587409 1610784186898386016190557)
          ·
            refine ⟨604044070086894756071459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1610784186898386016190557 604044070086894756071459)
            ·
              refine ⟨906066105130342134107189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604044070086894756071459 906066105130342134107189)
              ·
                refine ⟨84943697355969575072549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 906066105130342134107189 84943697355969575072549)
                ·
                  rfl

theorem cell20_558317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 5].length) (baseStart_558317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558317 prefixEnd_558317 := by exact prefixLift 558317
  have htrace : WordTrace (prefixWord ++ tailWord_558317) baseStart_558317 baseEnd_558317 := by
    simpa [prefixWord, tailWord_558317, baseEnd_558317] using wordTrace_append hprefix tailTrace_558317
  have hstable : (prefixWord ++ tailWord_558317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558317).length < 2 ^ (prefixWord ++ tailWord_558317).sum := by decide
  have hdescent : baseEnd_558317 < baseStart_558317 := by decide
  rcases family_descends (prefixWord ++ tailWord_558317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558328 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 9]
def baseStart_558328 : Nat := 118140960795 + 558328 * 2 ^ 59
def prefixEnd_558328 : Nat := 4983230072969 + 3 ^ 40 * 558328 * 2
def baseEnd_558328 : Nat := 254836112767641575850935

theorem tailTrace_558328 : CollatzResearch.WordTrace tailWord_558328 prefixEnd_558328 254836112767641575850935 := by
  unfold tailWord_558328
  simp only [CollatzResearch.WordTrace]
  refine ⟨10181947560640242837961819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13575930080853657117282425 10181947560640242837961819)
  ·
    refine ⟨15272921340960364256942729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10181947560640242837961819 15272921340960364256942729)
    ·
      refine ⟨11454691005720273192707047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15272921340960364256942729 11454691005720273192707047)
      ·
        refine ⟨17182036508580409789060571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11454691005720273192707047 17182036508580409789060571)
        ·
          refine ⟨25773054762870614683590857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17182036508580409789060571 25773054762870614683590857)
          ·
            refine ⟨19329791072152961012693143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25773054762870614683590857 19329791072152961012693143)
            ·
              refine ⟨28994686608229441519039715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19329791072152961012693143 28994686608229441519039715)
              ·
                refine ⟨43492029912344162278559573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28994686608229441519039715 43492029912344162278559573)
                ·
                  refine ⟨254836112767641575850935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43492029912344162278559573 254836112767641575850935)
                  ·
                    rfl

theorem cell20_558328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_558328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558328 prefixEnd_558328 := by exact prefixLift 558328
  have htrace : WordTrace (prefixWord ++ tailWord_558328) baseStart_558328 baseEnd_558328 := by
    simpa [prefixWord, tailWord_558328, baseEnd_558328] using wordTrace_append hprefix tailTrace_558328
  have hstable : (prefixWord ++ tailWord_558328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558328).length < 2 ^ (prefixWord ++ tailWord_558328).sum := by decide
  have hdescent : baseEnd_558328 < baseStart_558328 := by decide
  rcases family_descends (prefixWord ++ tailWord_558328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558348 : List Nat := [2, 2, 1, 2, 2, 4, 2, 3, 2]
def baseStart_558348 : Nat := 118140960795 + 558348 * 2 ^ 59
def prefixEnd_558348 : Nat := 4983230072969 + 3 ^ 40 * 558348 * 2
def baseEnd_558348 : Nat := 254845241312610395184187

theorem tailTrace_558348 : CollatzResearch.WordTrace tailWord_558348 prefixEnd_558348 254845241312610395184187 := by
  unfold tailWord_558348
  simp only [CollatzResearch.WordTrace]
  refine ⟨10182312290604014545825849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13576416387472019394434465 10182312290604014545825849)
  ·
    refine ⟨7636734217953010909369387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10182312290604014545825849 7636734217953010909369387)
    ·
      refine ⟨11455101326929516364054081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7636734217953010909369387 11455101326929516364054081)
      ·
        refine ⟨8591325995197137273040561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11455101326929516364054081 8591325995197137273040561)
        ·
          refine ⟨6443494496397852954780421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8591325995197137273040561 6443494496397852954780421)
          ·
            refine ⟨1208155218074597429021329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6443494496397852954780421 1208155218074597429021329)
            ·
              refine ⟨906116413555948071765997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1208155218074597429021329 906116413555948071765997)
              ·
                refine ⟨339793655083480526912249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 906116413555948071765997 339793655083480526912249)
                ·
                  refine ⟨254845241312610395184187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339793655083480526912249 254845241312610395184187)
                  ·
                    rfl

theorem cell20_558348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_558348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558348 prefixEnd_558348 := by exact prefixLift 558348
  have htrace : WordTrace (prefixWord ++ tailWord_558348) baseStart_558348 baseEnd_558348 := by
    simpa [prefixWord, tailWord_558348, baseEnd_558348] using wordTrace_append hprefix tailTrace_558348
  have hstable : (prefixWord ++ tailWord_558348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558348).length < 2 ^ (prefixWord ++ tailWord_558348).sum := by decide
  have hdescent : baseEnd_558348 < baseStart_558348 := by decide
  rcases family_descends (prefixWord ++ tailWord_558348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558359 : List Nat := [1, 1, 3, 4, 1, 1, 9]
def baseStart_558359 : Nat := 118140960795 + 558359 * 2 ^ 59
def prefixEnd_558359 : Nat := 4983230072969 + 3 ^ 40 * 558359 * 2
def baseEnd_558359 : Nat := 28316695779149249535275

theorem tailTrace_558359 : CollatzResearch.WordTrace tailWord_558359 prefixEnd_558359 28316695779149249535275 := by
  unfold tailWord_558359
  simp only [CollatzResearch.WordTrace]
  refine ⟨20365025784168177970302131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13576683856112118646868087 20365025784168177970302131)
  ·
    refine ⟨30547538676252266955453197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20365025784168177970302131 30547538676252266955453197)
    ·
      refine ⟨11455327003594600108294949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30547538676252266955453197 11455327003594600108294949)
      ·
        refine ⟨2147873813173987520305303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11455327003594600108294949 2147873813173987520305303)
        ·
          refine ⟨3221810719760981280457955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2147873813173987520305303 3221810719760981280457955)
          ·
            refine ⟨4832716079641471920686933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3221810719760981280457955 4832716079641471920686933)
            ·
              refine ⟨28316695779149249535275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4832716079641471920686933 28316695779149249535275)
              ·
                rfl

theorem cell20_558359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 9].length) (baseStart_558359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558359 prefixEnd_558359 := by exact prefixLift 558359
  have htrace : WordTrace (prefixWord ++ tailWord_558359) baseStart_558359 baseEnd_558359 := by
    simpa [prefixWord, tailWord_558359, baseEnd_558359] using wordTrace_append hprefix tailTrace_558359
  have hstable : (prefixWord ++ tailWord_558359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558359).length < 2 ^ (prefixWord ++ tailWord_558359).sum := by decide
  have hdescent : baseEnd_558359 < baseStart_558359 := by decide
  rcases family_descends (prefixWord ++ tailWord_558359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558362 : List Nat := [3, 1, 1, 3, 3, 1, 3, 2, 3]
def baseStart_558362 : Nat := 118140960795 + 558362 * 2 ^ 59
def prefixEnd_558362 : Nat := 4983230072969 + 3 ^ 40 * 558362 * 2
def baseEnd_558362 : Nat := 254851631294088568717463

theorem tailTrace_558362 : CollatzResearch.WordTrace tailWord_558362 prefixEnd_558362 254851631294088568717463 := by
  unfold tailWord_558362
  simp only [CollatzResearch.WordTrace]
  refine ⟨5091283800789327370665335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13576756802104872988440893 5091283800789327370665335)
  ·
    refine ⟨7636925701183991055998003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5091283800789327370665335 7636925701183991055998003)
    ·
      refine ⟨11455388551775986583997005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7636925701183991055998003 11455388551775986583997005)
      ·
        refine ⟨4295770706915994968998877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11455388551775986583997005 4295770706915994968998877)
        ·
          refine ⟨1610914015093498113374579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4295770706915994968998877 1610914015093498113374579)
          ·
            refine ⟨2416371022640247170061869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1610914015093498113374579 2416371022640247170061869)
            ·
              refine ⟨906139133490092688773201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2416371022640247170061869 906139133490092688773201)
              ·
                refine ⟨679604350117569516579901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906139133490092688773201 679604350117569516579901)
                ·
                  refine ⟨254851631294088568717463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679604350117569516579901 254851631294088568717463)
                  ·
                    rfl

theorem cell20_558362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_558362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558362 prefixEnd_558362 := by exact prefixLift 558362
  have htrace : WordTrace (prefixWord ++ tailWord_558362) baseStart_558362 baseEnd_558362 := by
    simpa [prefixWord, tailWord_558362, baseEnd_558362] using wordTrace_append hprefix tailTrace_558362
  have hstable : (prefixWord ++ tailWord_558362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558362).length < 2 ^ (prefixWord ++ tailWord_558362).sum := by decide
  have hdescent : baseEnd_558362 < baseStart_558362 := by decide
  rcases family_descends (prefixWord ++ tailWord_558362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558421 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 5]
def baseStart_558421 : Nat := 118140960795 + 558421 * 2 ^ 59
def prefixEnd_558421 : Nat := 4983230072969 + 3 ^ 40 * 558421 * 2
def baseEnd_558421 : Nat := 254878560501746585750555

theorem tailTrace_558421 : CollatzResearch.WordTrace tailWord_558421 prefixEnd_558421 254878560501746585750555 := by
  unfold tailWord_558421
  simp only [CollatzResearch.WordTrace]
  refine ⟨20367287109943562559059117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13578191406629041706039411 20367287109943562559059117)
  ·
    refine ⟨7637732666228835959647169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20367287109943562559059117 7637732666228835959647169)
    ·
      refine ⟨5728299499671626969735377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7637732666228835959647169 5728299499671626969735377)
      ·
        refine ⟨4296224624753720227301533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5728299499671626969735377 4296224624753720227301533)
        ·
          refine ⟨1611084234282645085238075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4296224624753720227301533 1611084234282645085238075)
          ·
            refine ⟨2416626351423967627857113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611084234282645085238075 2416626351423967627857113)
            ·
              refine ⟨1812469763567975720892835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2416626351423967627857113 1812469763567975720892835)
              ·
                refine ⟨2718704645351963581339253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1812469763567975720892835 2718704645351963581339253)
                ·
                  refine ⟨254878560501746585750555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2718704645351963581339253 254878560501746585750555)
                  ·
                    rfl

theorem cell20_558421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_558421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558421 prefixEnd_558421 := by exact prefixLift 558421
  have htrace : WordTrace (prefixWord ++ tailWord_558421) baseStart_558421 baseEnd_558421 := by
    simpa [prefixWord, tailWord_558421, baseEnd_558421] using wordTrace_append hprefix tailTrace_558421
  have hstable : (prefixWord ++ tailWord_558421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558421).length < 2 ^ (prefixWord ++ tailWord_558421).sum := by decide
  have hdescent : baseEnd_558421 < baseStart_558421 := by decide
  rcases family_descends (prefixWord ++ tailWord_558421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558424 : List Nat := [2, 1, 2, 2, 1, 1, 7, 2, 2]
def baseStart_558424 : Nat := 118140960795 + 558424 * 2 ^ 59
def prefixEnd_558424 : Nat := 4983230072969 + 3 ^ 40 * 558424 * 2
def baseEnd_558424 : Nat := 254879929783491908650543

theorem tailTrace_558424 : CollatzResearch.WordTrace tailWord_558424 prefixEnd_558424 254879929783491908650543 := by
  unfold tailWord_558424
  simp only [CollatzResearch.WordTrace]
  refine ⟨10183698264466347035709163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13578264352621796047612217 10183698264466347035709163)
  ·
    refine ⟨15275547396699520553563745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10183698264466347035709163 15275547396699520553563745)
    ·
      refine ⟨11456660547524640415172809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15275547396699520553563745 11456660547524640415172809)
      ·
        refine ⟨8592495410643480311379607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11456660547524640415172809 8592495410643480311379607)
        ·
          refine ⟨12888743115965220467069411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8592495410643480311379607 12888743115965220467069411)
          ·
            refine ⟨19333114673947830700604117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12888743115965220467069411 19333114673947830700604117)
            ·
              refine ⟨453119875170652282045409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19333114673947830700604117 453119875170652282045409)
              ·
                refine ⟨339839906377989211534057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453119875170652282045409 339839906377989211534057)
                ·
                  refine ⟨254879929783491908650543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339839906377989211534057 254879929783491908650543)
                  ·
                    rfl

theorem cell20_558424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 2].length) (baseStart_558424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558424 prefixEnd_558424 := by exact prefixLift 558424
  have htrace : WordTrace (prefixWord ++ tailWord_558424) baseStart_558424 baseEnd_558424 := by
    simpa [prefixWord, tailWord_558424, baseEnd_558424] using wordTrace_append hprefix tailTrace_558424
  have hstable : (prefixWord ++ tailWord_558424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558424).length < 2 ^ (prefixWord ++ tailWord_558424).sum := by decide
  have hdescent : baseEnd_558424 < baseStart_558424 := by decide
  rcases family_descends (prefixWord ++ tailWord_558424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558435 : List Nat := [1, 1, 1, 5, 2, 2, 1, 7]
def baseStart_558435 : Nat := 118140960795 + 558435 * 2 ^ 59
def prefixEnd_558435 : Nat := 4983230072969 + 3 ^ 40 * 558435 * 2
def baseEnd_558435 : Nat := 84961650161074919761277

theorem tailTrace_558435 : CollatzResearch.WordTrace tailWord_558435 prefixEnd_558435 84961650161074919761277 := by
  unfold tailWord_558435
  simp only [CollatzResearch.WordTrace]
  refine ⟨20367797731892842950068759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13578531821261895300045839 20367797731892842950068759)
  ·
    refine ⟨30551696597839264425103139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20367797731892842950068759 30551696597839264425103139)
    ·
      refine ⟨45827544896758896637654709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30551696597839264425103139 45827544896758896637654709)
      ·
        refine ⟨4296332334071146559780129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45827544896758896637654709 4296332334071146559780129)
        ·
          refine ⟨3222249250553359919835097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4296332334071146559780129 3222249250553359919835097)
          ·
            refine ⟨2416686937915019939876323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3222249250553359919835097 2416686937915019939876323)
            ·
              refine ⟨3625030406872529909814485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2416686937915019939876323 3625030406872529909814485)
              ·
                refine ⟨84961650161074919761277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3625030406872529909814485 84961650161074919761277)
                ·
                  rfl

theorem cell20_558435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 7].length) (baseStart_558435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558435 prefixEnd_558435 := by exact prefixLift 558435
  have htrace : WordTrace (prefixWord ++ tailWord_558435) baseStart_558435 baseEnd_558435 := by
    simpa [prefixWord, tailWord_558435, baseEnd_558435] using wordTrace_append hprefix tailTrace_558435
  have hstable : (prefixWord ++ tailWord_558435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558435).length < 2 ^ (prefixWord ++ tailWord_558435).sum := by decide
  have hdescent : baseEnd_558435 < baseStart_558435 := by decide
  rcases family_descends (prefixWord ++ tailWord_558435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558473 : List Nat := [1, 2, 1, 1, 7, 8]
def baseStart_558473 : Nat := 118140960795 + 558473 * 2 ^ 59
def prefixEnd_558473 : Nat := 4983230072969 + 3 ^ 40 * 558473 * 2
def baseEnd_558473 : Nat := 9440825730320945037667

theorem tailTrace_558473 : CollatzResearch.WordTrace tailWord_558473 prefixEnd_558473 9440825730320945037667 := by
  unfold tailWord_558473
  simp only [CollatzResearch.WordTrace]
  refine ⟨20369183705755175439952073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13579455803836783626634715 20369183705755175439952073)
  ·
    refine ⟨15276887779316381579964055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20369183705755175439952073 15276887779316381579964055)
    ·
      refine ⟨22915331668974572369946083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15276887779316381579964055 22915331668974572369946083)
      ·
        refine ⟨34372997503461858554919125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22915331668974572369946083 34372997503461858554919125)
        ·
          refine ⟨805617128987387309880917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 34372997503461858554919125 805617128987387309880917)
          ·
            refine ⟨9440825730320945037667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 805617128987387309880917 9440825730320945037667)
            ·
              rfl

theorem cell20_558473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 8].length) (baseStart_558473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558473 prefixEnd_558473 := by exact prefixLift 558473
  have htrace : WordTrace (prefixWord ++ tailWord_558473) baseStart_558473 baseEnd_558473 := by
    simpa [prefixWord, tailWord_558473, baseEnd_558473] using wordTrace_append hprefix tailTrace_558473
  have hstable : (prefixWord ++ tailWord_558473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558473).length < 2 ^ (prefixWord ++ tailWord_558473).sum := by decide
  have hdescent : baseEnd_558473 < baseStart_558473 := by decide
  rcases family_descends (prefixWord ++ tailWord_558473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558542 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_558542 : Nat := 118140960795 + 558542 * 2 ^ 59
def prefixEnd_558542 : Nat := 4983230072969 + 3 ^ 40 * 558542 * 2
def baseEnd_558542 : Nat := 254933788198807942716727

theorem tailTrace_558542 : CollatzResearch.WordTrace tailWord_558542 prefixEnd_558542 254933788198807942716727 := by
  unfold tailWord_558542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2546462542813150028026735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13581133561670133482809253 2546462542813150028026735)
  ·
    refine ⟨3819693814219725042040103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2546462542813150028026735 3819693814219725042040103)
    ·
      refine ⟨5729540721329587563060155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3819693814219725042040103 5729540721329587563060155)
      ·
        refine ⟨8594311081994381344590233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5729540721329587563060155 8594311081994381344590233)
        ·
          refine ⟨6445733311495786008442675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8594311081994381344590233 6445733311495786008442675)
          ·
            refine ⟨9668599967243679012664013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6445733311495786008442675 9668599967243679012664013)
            ·
              refine ⟨3625724987716379629749005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9668599967243679012664013 3625724987716379629749005)
              ·
                refine ⟨1359646870393642361155877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3625724987716379629749005 1359646870393642361155877)
                ·
                  refine ⟨254933788198807942716727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1359646870393642361155877 254933788198807942716727)
                  ·
                    rfl

theorem cell20_558542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_558542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558542 prefixEnd_558542 := by exact prefixLift 558542
  have htrace : WordTrace (prefixWord ++ tailWord_558542) baseStart_558542 baseEnd_558542 := by
    simpa [prefixWord, tailWord_558542, baseEnd_558542] using wordTrace_append hprefix tailTrace_558542
  have hstable : (prefixWord ++ tailWord_558542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558542).length < 2 ^ (prefixWord ++ tailWord_558542).sum := by decide
  have hdescent : baseEnd_558542 < baseStart_558542 := by decide
  rcases family_descends (prefixWord ++ tailWord_558542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558549 : List Nat := [1, 3, 2, 3, 1, 1, 2, 7]
def baseStart_558549 : Nat := 118140960795 + 558549 * 2 ^ 59
def prefixEnd_558549 : Nat := 4983230072969 + 3 ^ 40 * 558549 * 2
def baseEnd_558549 : Nat := 84978994396515676494455

theorem tailTrace_558549 : CollatzResearch.WordTrace tailWord_558549 prefixEnd_558549 84978994396515676494455 := by
  unfold tailWord_558549
  simp only [CollatzResearch.WordTrace]
  refine ⟨20371955653479840419718701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13581303768986560279812467 20371955653479840419718701)
  ·
    refine ⟨7639483370054940157394513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20371955653479840419718701 7639483370054940157394513)
    ·
      refine ⟨5729612527541205118045885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7639483370054940157394513 5729612527541205118045885)
      ·
        refine ⟨2148604697827951919267207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5729612527541205118045885 2148604697827951919267207)
        ·
          refine ⟨3222907046741927878900811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2148604697827951919267207 3222907046741927878900811)
          ·
            refine ⟨4834360570112891818351217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3222907046741927878900811 4834360570112891818351217)
            ·
              refine ⟨3625770427584668863763413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4834360570112891818351217 3625770427584668863763413)
              ·
                refine ⟨84978994396515676494455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3625770427584668863763413 84978994396515676494455)
                ·
                  rfl

theorem cell20_558549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 7].length) (baseStart_558549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558549 prefixEnd_558549 := by exact prefixLift 558549
  have htrace : WordTrace (prefixWord ++ tailWord_558549) baseStart_558549 baseEnd_558549 := by
    simpa [prefixWord, tailWord_558549, baseEnd_558549] using wordTrace_append hprefix tailTrace_558549
  have hstable : (prefixWord ++ tailWord_558549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558549).length < 2 ^ (prefixWord ++ tailWord_558549).sum := by decide
  have hdescent : baseEnd_558549 < baseStart_558549 := by decide
  rcases family_descends (prefixWord ++ tailWord_558549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558576 : List Nat := [2, 1, 1, 1, 3, 6, 1, 3, 2]
def baseStart_558576 : Nat := 118140960795 + 558576 * 2 ^ 59
def prefixEnd_558576 : Nat := 4983230072969 + 3 ^ 40 * 558576 * 2
def baseEnd_558576 : Nat := 254949306725254935583255

theorem tailTrace_558576 : CollatzResearch.WordTrace tailWord_558576 prefixEnd_558576 254949306725254935583255 := by
  unfold tailWord_558576
  simp only [CollatzResearch.WordTrace]
  refine ⟨10186470212191012015475791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13581960282921349353967721 10186470212191012015475791)
  ·
    refine ⟨15279705318286518023213687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10186470212191012015475791 15279705318286518023213687)
    ·
      refine ⟨22919557977429777034820531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15279705318286518023213687 22919557977429777034820531)
      ·
        refine ⟨34379336966144665552230797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22919557977429777034820531 34379336966144665552230797)
        ·
          refine ⟨12892251362304249582086549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34379336966144665552230797 12892251362304249582086549)
          ·
            refine ⟨604324282608011699160307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12892251362304249582086549 604324282608011699160307)
            ·
              refine ⟨906486423912017548740461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604324282608011699160307 906486423912017548740461)
              ·
                refine ⟨339932408967006580777673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 906486423912017548740461 339932408967006580777673)
                ·
                  refine ⟨254949306725254935583255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339932408967006580777673 254949306725254935583255)
                  ·
                    rfl

theorem cell20_558576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 2].length) (baseStart_558576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558576 prefixEnd_558576 := by exact prefixLift 558576
  have htrace : WordTrace (prefixWord ++ tailWord_558576) baseStart_558576 baseEnd_558576 := by
    simpa [prefixWord, tailWord_558576, baseEnd_558576] using wordTrace_append hprefix tailTrace_558576
  have hstable : (prefixWord ++ tailWord_558576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558576).length < 2 ^ (prefixWord ++ tailWord_558576).sum := by decide
  have hdescent : baseEnd_558576 < baseStart_558576 := by decide
  rcases family_descends (prefixWord ++ tailWord_558576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558593 : List Nat := [1, 2, 4, 1, 4, 1, 3, 2, 2]
def baseStart_558593 : Nat := 118140960795 + 558593 * 2 ^ 59
def prefixEnd_558593 : Nat := 4983230072969 + 3 ^ 40 * 558593 * 2
def baseEnd_558593 : Nat := 254957065988478432016519

theorem tailTrace_558593 : CollatzResearch.WordTrace tailWord_558593 prefixEnd_558593 254957065988478432016519 := by
  unfold tailWord_558593
  simp only [CollatzResearch.WordTrace]
  refine ⟨20373560465320435934320433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13582373643546957289546955 20373560465320435934320433)
  ·
    refine ⟨15280170348990326950740325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20373560465320435934320433 15280170348990326950740325)
    ·
      refine ⟨2865031940435686303263811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15280170348990326950740325 2865031940435686303263811)
      ·
        refine ⟨4297547910653529454895717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2865031940435686303263811 4297547910653529454895717)
        ·
          refine ⟨805790233247536772792947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4297547910653529454895717 805790233247536772792947)
          ·
            refine ⟨1208685349871305159189421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805790233247536772792947 1208685349871305159189421)
            ·
              refine ⟨453257006201739434696033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1208685349871305159189421 453257006201739434696033)
              ·
                refine ⟨339942754651304576022025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453257006201739434696033 339942754651304576022025)
                ·
                  refine ⟨254957065988478432016519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339942754651304576022025 254957065988478432016519)
                  ·
                    rfl

theorem cell20_558593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 2].length) (baseStart_558593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558593 prefixEnd_558593 := by exact prefixLift 558593
  have htrace : WordTrace (prefixWord ++ tailWord_558593) baseStart_558593 baseEnd_558593 := by
    simpa [prefixWord, tailWord_558593, baseEnd_558593] using wordTrace_append hprefix tailTrace_558593
  have hstable : (prefixWord ++ tailWord_558593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558593).length < 2 ^ (prefixWord ++ tailWord_558593).sum := by decide
  have hdescent : baseEnd_558593 < baseStart_558593 := by decide
  rcases family_descends (prefixWord ++ tailWord_558593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558604 : List Nat := [2, 2, 1, 2, 5, 1, 2, 5]
def baseStart_558604 : Nat := 118140960795 + 558604 * 2 ^ 59
def prefixEnd_558604 : Nat := 4983230072969 + 3 ^ 40 * 558604 * 2
def baseEnd_558604 : Nat := 84987362229403760883269

theorem tailTrace_558604 : CollatzResearch.WordTrace tailWord_558604 prefixEnd_558604 84987362229403760883269 := by
  unfold tailWord_558604
  simp only [CollatzResearch.WordTrace]
  refine ⟨10186980834140292406485433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13582641112187056541980577 10186980834140292406485433)
  ·
    refine ⟨7640235625605219304864075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10186980834140292406485433 7640235625605219304864075)
    ·
      refine ⟨11460353438407828957296113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7640235625605219304864075 11460353438407828957296113)
      ·
        refine ⟨8595265078805871717972085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11460353438407828957296113 8595265078805871717972085)
        ·
          refine ⟨805806101138050473559883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8595265078805871717972085 805806101138050473559883)
          ·
            refine ⟨1208709151707075710339825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805806101138050473559883 1208709151707075710339825)
            ·
              refine ⟨906531863780306782754869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1208709151707075710339825 906531863780306782754869)
              ·
                refine ⟨84987362229403760883269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 906531863780306782754869 84987362229403760883269)
                ·
                  rfl

theorem cell20_558604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_558604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558604 prefixEnd_558604 := by exact prefixLift 558604
  have htrace : WordTrace (prefixWord ++ tailWord_558604) baseStart_558604 baseEnd_558604 := by
    simpa [prefixWord, tailWord_558604, baseEnd_558604] using wordTrace_append hprefix tailTrace_558604
  have hstable : (prefixWord ++ tailWord_558604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558604).length < 2 ^ (prefixWord ++ tailWord_558604).sum := by decide
  have hdescent : baseEnd_558604 < baseStart_558604 := by decide
  rcases family_descends (prefixWord ++ tailWord_558604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558611 : List Nat := [1, 1, 1, 2, 1, 7, 1, 3, 3]
def baseStart_558611 : Nat := 118140960795 + 558611 * 2 ^ 59
def prefixEnd_558611 : Nat := 4983230072969 + 3 ^ 40 * 558611 * 2
def baseEnd_558611 : Nat := 254965281678950369416445

theorem tailTrace_558611 : CollatzResearch.WordTrace tailWord_558611 prefixEnd_558611 254965281678950369416445 := by
  unfold tailWord_558611
  simp only [CollatzResearch.WordTrace]
  refine ⟨20374216979255225008475687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13582811319503483338983791 20374216979255225008475687)
  ·
    refine ⟨30561325468882837512713531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20374216979255225008475687 30561325468882837512713531)
    ·
      refine ⟨45841988203324256269070297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30561325468882837512713531 45841988203324256269070297)
      ·
        refine ⟨34381491152493192201802723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45841988203324256269070297 34381491152493192201802723)
        ·
          refine ⟨51572236728739788302704085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34381491152493192201802723 51572236728739788302704085)
          ·
            refine ⟨1208724298329838788344627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 51572236728739788302704085 1208724298329838788344627)
            ·
              refine ⟨1813086447494758182516941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1208724298329838788344627 1813086447494758182516941)
              ·
                refine ⟨679907417810534318443853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1813086447494758182516941 679907417810534318443853)
                ·
                  refine ⟨254965281678950369416445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679907417810534318443853 254965281678950369416445)
                  ·
                    rfl

theorem cell20_558611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 3].length) (baseStart_558611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558611 prefixEnd_558611 := by exact prefixLift 558611
  have htrace : WordTrace (prefixWord ++ tailWord_558611) baseStart_558611 baseEnd_558611 := by
    simpa [prefixWord, tailWord_558611, baseEnd_558611] using wordTrace_append hprefix tailTrace_558611
  have hstable : (prefixWord ++ tailWord_558611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558611).length < 2 ^ (prefixWord ++ tailWord_558611).sum := by decide
  have hdescent : baseEnd_558611 < baseStart_558611 := by decide
  rcases family_descends (prefixWord ++ tailWord_558611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558625 : List Nat := [1, 2, 3, 2, 2, 2, 2, 6]
def baseStart_558625 : Nat := 118140960795 + 558625 * 2 ^ 59
def prefixEnd_558625 : Nat := 4983230072969 + 3 ^ 40 * 558625 * 2
def baseEnd_558625 : Nat := 84990557220142847649907

theorem tailTrace_558625 : CollatzResearch.WordTrace tailWord_558625 prefixEnd_558625 84990557220142847649907 := by
  unfold tailWord_558625
  simp only [CollatzResearch.WordTrace]
  refine ⟨20374727601204505399485329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13583151734136336932990219 20374727601204505399485329)
  ·
    refine ⟨15281045700903379049613997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20374727601204505399485329 15281045700903379049613997)
    ·
      refine ⟨5730392137838767143605249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15281045700903379049613997 5730392137838767143605249)
      ·
        refine ⟨4297794103379075357703937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5730392137838767143605249 4297794103379075357703937)
        ·
          refine ⟨3223345577534306518277953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4297794103379075357703937 3223345577534306518277953)
          ·
            refine ⟨2417509183150729888708465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3223345577534306518277953 2417509183150729888708465)
            ·
              refine ⟨1813131887363047416531349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2417509183150729888708465 1813131887363047416531349)
              ·
                refine ⟨84990557220142847649907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1813131887363047416531349 84990557220142847649907)
                ·
                  rfl

theorem cell20_558625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 6].length) (baseStart_558625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558625 prefixEnd_558625 := by exact prefixLift 558625
  have htrace : WordTrace (prefixWord ++ tailWord_558625) baseStart_558625 baseEnd_558625 := by
    simpa [prefixWord, tailWord_558625, baseEnd_558625] using wordTrace_append hprefix tailTrace_558625
  have hstable : (prefixWord ++ tailWord_558625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558625).length < 2 ^ (prefixWord ++ tailWord_558625).sum := by decide
  have hdescent : baseEnd_558625 < baseStart_558625 := by decide
  rcases family_descends (prefixWord ++ tailWord_558625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558649 : List Nat := [1, 2, 1, 5, 1, 2, 1, 4, 3]
def baseStart_558649 : Nat := 118140960795 + 558649 * 2 ^ 59
def prefixEnd_558649 : Nat := 4983230072969 + 3 ^ 40 * 558649 * 2
def baseEnd_558649 : Nat := 254982625914391126149623

theorem tailTrace_558649 : CollatzResearch.WordTrace tailWord_558649 prefixEnd_558649 254982625914391126149623 := by
  unfold tailWord_558649
  simp only [CollatzResearch.WordTrace]
  refine ⟨20375602953117557498359001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13583735302078371665572667 20375602953117557498359001)
  ·
    refine ⟨15281702214838168123769251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20375602953117557498359001 15281702214838168123769251)
    ·
      refine ⟨22922553322257252185653877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15281702214838168123769251 22922553322257252185653877)
      ·
        refine ⟨2148989373961617392405051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22922553322257252185653877 2148989373961617392405051)
        ·
          refine ⟨3223484060942426088607577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2148989373961617392405051 3223484060942426088607577)
          ·
            refine ⟨2417613045706819566455683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3223484060942426088607577 2417613045706819566455683)
            ·
              refine ⟨3626419568560229349683525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2417613045706819566455683 3626419568560229349683525)
              ·
                refine ⟨679953669105043003065661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3626419568560229349683525 679953669105043003065661)
                ·
                  refine ⟨254982625914391126149623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679953669105043003065661 254982625914391126149623)
                  ·
                    rfl

theorem cell20_558649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_558649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558649 prefixEnd_558649 := by exact prefixLift 558649
  have htrace : WordTrace (prefixWord ++ tailWord_558649) baseStart_558649 baseEnd_558649 := by
    simpa [prefixWord, tailWord_558649, baseEnd_558649] using wordTrace_append hprefix tailTrace_558649
  have hstable : (prefixWord ++ tailWord_558649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558649).length < 2 ^ (prefixWord ++ tailWord_558649).sum := by decide
  have hdescent : baseEnd_558649 < baseStart_558649 := by decide
  rcases family_descends (prefixWord ++ tailWord_558649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558652 : List Nat := [2, 2, 2, 2, 4, 1, 1, 4, 2]
def baseStart_558652 : Nat := 118140960795 + 558652 * 2 ^ 59
def prefixEnd_558652 : Nat := 4983230072969 + 3 ^ 40 * 558652 * 2
def baseEnd_558652 : Nat := 254983995196136449049611

theorem tailTrace_558652 : CollatzResearch.WordTrace tailWord_558652 prefixEnd_558652 254983995196136449049611 := by
  unfold tailWord_558652
  simp only [CollatzResearch.WordTrace]
  refine ⟨10187856186053344505359105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13583808248071126007145473 10187856186053344505359105)
  ·
    refine ⟨7640892139540008379019329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10187856186053344505359105 7640892139540008379019329)
    ·
      refine ⟨5730669104655006284264497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7640892139540008379019329 5730669104655006284264497)
      ·
        refine ⟨4298001828491254713198373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5730669104655006284264497 4298001828491254713198373)
        ·
          refine ⟨805875342842110258724695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4298001828491254713198373 805875342842110258724695)
          ·
            refine ⟨1208813014263165388087043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805875342842110258724695 1208813014263165388087043)
            ·
              refine ⟨1813219521394748082130565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1208813014263165388087043 1813219521394748082130565)
              ·
                refine ⟨339978660261515265399481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1813219521394748082130565 339978660261515265399481)
                ·
                  refine ⟨254983995196136449049611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339978660261515265399481 254983995196136449049611)
                  ·
                    rfl

theorem cell20_558652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_558652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558652 prefixEnd_558652 := by exact prefixLift 558652
  have htrace : WordTrace (prefixWord ++ tailWord_558652) baseStart_558652 baseEnd_558652 := by
    simpa [prefixWord, tailWord_558652, baseEnd_558652] using wordTrace_append hprefix tailTrace_558652
  have hstable : (prefixWord ++ tailWord_558652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558652).length < 2 ^ (prefixWord ++ tailWord_558652).sum := by decide
  have hdescent : baseEnd_558652 < baseStart_558652 := by decide
  rcases family_descends (prefixWord ++ tailWord_558652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558670 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_558670 : Nat := 118140960795 + 558670 * 2 ^ 59
def prefixEnd_558670 : Nat := 4983230072969 + 3 ^ 40 * 558670 * 2
def baseEnd_558670 : Nat := 254992210886608386449537

theorem tailTrace_558670 : CollatzResearch.WordTrace tailWord_558670 prefixEnd_558670 254992210886608386449537 := by
  unfold tailWord_558670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2547046110755184760609183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13584245924027652056582309 2547046110755184760609183)
  ·
    refine ⟨3820569166132777140913775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2547046110755184760609183 3820569166132777140913775)
    ·
      refine ⟨5730853749199165711370663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3820569166132777140913775 5730853749199165711370663)
      ·
        refine ⟨8596280623798748567055995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5730853749199165711370663 8596280623798748567055995)
        ·
          refine ⟨12894420935698122850583993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8596280623798748567055995 12894420935698122850583993)
          ·
            refine ⟨9670815701773592137937995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12894420935698122850583993 9670815701773592137937995)
            ·
              refine ⟨14506223552660388206906993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9670815701773592137937995 14506223552660388206906993)
              ·
                refine ⟨10879667664495291155180245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14506223552660388206906993 10879667664495291155180245)
                ·
                  refine ⟨254992210886608386449537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10879667664495291155180245 254992210886608386449537)
                  ·
                    rfl

theorem cell20_558670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_558670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558670 prefixEnd_558670 := by exact prefixLift 558670
  have htrace : WordTrace (prefixWord ++ tailWord_558670) baseStart_558670 baseEnd_558670 := by
    simpa [prefixWord, tailWord_558670, baseEnd_558670] using wordTrace_append hprefix tailTrace_558670
  have hstable : (prefixWord ++ tailWord_558670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558670).length < 2 ^ (prefixWord ++ tailWord_558670).sum := by decide
  have hdescent : baseEnd_558670 < baseStart_558670 := by decide
  rcases family_descends (prefixWord ++ tailWord_558670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558704 : List Nat := [2, 1, 1, 1, 6, 3, 1, 2, 3]
def baseStart_558704 : Nat := 118140960795 + 558704 * 2 ^ 59
def prefixEnd_558704 : Nat := 4983230072969 + 3 ^ 40 * 558704 * 2
def baseEnd_558704 : Nat := 255007729413055379316065

theorem tailTrace_558704 : CollatzResearch.WordTrace tailWord_558704 prefixEnd_558704 255007729413055379316065 := by
  unfold tailWord_558704
  simp only [CollatzResearch.WordTrace]
  refine ⟨10188804483959150945805583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13585072645278867927740777 10188804483959150945805583)
  ·
    refine ⟨15283206725938726418708375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10188804483959150945805583 15283206725938726418708375)
    ·
      refine ⟨22924810088908089628062563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15283206725938726418708375 22924810088908089628062563)
      ·
        refine ⟨34387215133362134442093845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22924810088908089628062563 34387215133362134442093845)
        ·
          refine ⟨1611900709376350051973149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34387215133362134442093845 1611900709376350051973149)
          ·
            refine ⟨604462766016131269489931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1611900709376350051973149 604462766016131269489931)
            ·
              refine ⟨906694149024196904234897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604462766016131269489931 906694149024196904234897)
              ·
                refine ⟨680020611768147678176173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906694149024196904234897 680020611768147678176173)
                ·
                  refine ⟨255007729413055379316065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680020611768147678176173 255007729413055379316065)
                  ·
                    rfl

theorem cell20_558704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_558704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558704 prefixEnd_558704 := by exact prefixLift 558704
  have htrace : WordTrace (prefixWord ++ tailWord_558704) baseStart_558704 baseEnd_558704 := by
    simpa [prefixWord, tailWord_558704, baseEnd_558704] using wordTrace_append hprefix tailTrace_558704
  have hstable : (prefixWord ++ tailWord_558704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558704).length < 2 ^ (prefixWord ++ tailWord_558704).sum := by decide
  have hdescent : baseEnd_558704 < baseStart_558704 := by decide
  rcases family_descends (prefixWord ++ tailWord_558704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558770 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_558770 : Nat := 118140960795 + 558770 * 2 ^ 59
def prefixEnd_558770 : Nat := 4983230072969 + 3 ^ 40 * 558770 * 2
def baseEnd_558770 : Nat := 255037853611452483115795

theorem tailTrace_558770 : CollatzResearch.WordTrace tailWord_558770 prefixEnd_558770 255037853611452483115795 := by
  unfold tailWord_558770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5095004046419798790878441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13586677457119463442342509 5095004046419798790878441)
  ·
    refine ⟨3821253034814849093158831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5095004046419798790878441 3821253034814849093158831)
    ·
      refine ⟨5731879552222273639738247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3821253034814849093158831 5731879552222273639738247)
      ·
        refine ⟨8597819328333410459607371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5731879552222273639738247 8597819328333410459607371)
        ·
          refine ⟨12896728992500115689411057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8597819328333410459607371 12896728992500115689411057)
          ·
            refine ⟨9672546744375086767058293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12896728992500115689411057 9672546744375086767058293)
            ·
              refine ⟨906801257285164384411715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9672546744375086767058293 906801257285164384411715)
              ·
                refine ⟨1360201885927746576617573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906801257285164384411715 1360201885927746576617573)
                ·
                  refine ⟨255037853611452483115795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1360201885927746576617573 255037853611452483115795)
                  ·
                    rfl

theorem cell20_558770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_558770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558770 prefixEnd_558770 := by exact prefixLift 558770
  have htrace : WordTrace (prefixWord ++ tailWord_558770) baseStart_558770 baseEnd_558770 := by
    simpa [prefixWord, tailWord_558770, baseEnd_558770] using wordTrace_append hprefix tailTrace_558770
  have hstable : (prefixWord ++ tailWord_558770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558770).length < 2 ^ (prefixWord ++ tailWord_558770).sum := by decide
  have hdescent : baseEnd_558770 < baseStart_558770 := by decide
  rcases family_descends (prefixWord ++ tailWord_558770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558780 : List Nat := [2, 2, 2, 3, 1, 2, 4, 1, 3]
def baseStart_558780 : Nat := 118140960795 + 558780 * 2 ^ 59
def prefixEnd_558780 : Nat := 4983230072969 + 3 ^ 40 * 558780 * 2
def baseEnd_558780 : Nat := 255042417883936892782421

theorem tailTrace_558780 : CollatzResearch.WordTrace tailWord_558780 prefixEnd_558780 255042417883936892782421 := by
  unfold tailWord_558780
  simp only [CollatzResearch.WordTrace]
  refine ⟨10190190457821483435688897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13586920610428644580918529 10190190457821483435688897)
  ·
    refine ⟨7642642843366112576766673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10190190457821483435688897 7642642843366112576766673)
    ·
      refine ⟨5731982132524584432575005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7642642843366112576766673 5731982132524584432575005)
      ·
        refine ⟨2149493299696719162215627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5731982132524584432575005 2149493299696719162215627)
        ·
          refine ⟨3224239949545078743323441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2149493299696719162215627 3224239949545078743323441)
          ·
            refine ⟨2418179962158809057492581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3224239949545078743323441 2418179962158809057492581)
            ·
              refine ⟨453408742904776698279859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2418179962158809057492581 453408742904776698279859)
              ·
                refine ⟨680113114357165047419789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453408742904776698279859 680113114357165047419789)
                ·
                  refine ⟨255042417883936892782421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680113114357165047419789 255042417883936892782421)
                  ·
                    rfl

theorem cell20_558780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_558780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558780 prefixEnd_558780 := by exact prefixLift 558780
  have htrace : WordTrace (prefixWord ++ tailWord_558780) baseStart_558780 baseEnd_558780 := by
    simpa [prefixWord, tailWord_558780, baseEnd_558780] using wordTrace_append hprefix tailTrace_558780
  have hstable : (prefixWord ++ tailWord_558780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558780).length < 2 ^ (prefixWord ++ tailWord_558780).sum := by decide
  have hdescent : baseEnd_558780 < baseStart_558780 := by decide
  rcases family_descends (prefixWord ++ tailWord_558780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558791 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 6]
def baseStart_558791 : Nat := 118140960795 + 558791 * 2 ^ 59
def prefixEnd_558791 : Nat := 4983230072969 + 3 ^ 40 * 558791 * 2
def baseEnd_558791 : Nat := 255047438583669743415709

theorem tailTrace_558791 : CollatzResearch.WordTrace tailWord_558791 prefixEnd_558791 255047438583669743415709 := by
  unfold tailWord_558791
  simp only [CollatzResearch.WordTrace]
  refine ⟨20380782118603115750028227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13587188079068743833352151 20380782118603115750028227)
  ·
    refine ⟨30571173177904673625042341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20380782118603115750028227 30571173177904673625042341)
    ·
      refine ⟨5732094970857126304695439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30571173177904673625042341 5732094970857126304695439)
      ·
        refine ⟨8598142456285689457043159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5732094970857126304695439 8598142456285689457043159)
        ·
          refine ⟨12897213684428534185564739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8598142456285689457043159 12897213684428534185564739)
          ·
            refine ⟨19345820526642801278347109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12897213684428534185564739 19345820526642801278347109)
            ·
              refine ⟨3627341348745525239690083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19345820526642801278347109 3627341348745525239690083)
              ·
                refine ⟨5441012023118287859535125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3627341348745525239690083 5441012023118287859535125)
                ·
                  refine ⟨255047438583669743415709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5441012023118287859535125 255047438583669743415709)
                  ·
                    rfl

theorem cell20_558791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_558791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558791 prefixEnd_558791 := by exact prefixLift 558791
  have htrace : WordTrace (prefixWord ++ tailWord_558791) baseStart_558791 baseEnd_558791 := by
    simpa [prefixWord, tailWord_558791, baseEnd_558791] using wordTrace_append hprefix tailTrace_558791
  have hstable : (prefixWord ++ tailWord_558791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558791).length < 2 ^ (prefixWord ++ tailWord_558791).sum := by decide
  have hdescent : baseEnd_558791 < baseStart_558791 := by decide
  rcases family_descends (prefixWord ++ tailWord_558791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558884 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 4]
def baseStart_558884 : Nat := 118140960795 + 558884 * 2 ^ 59
def prefixEnd_558884 : Nat := 4983230072969 + 3 ^ 40 * 558884 * 2
def baseEnd_558884 : Nat := 255089886317774753315329

theorem tailTrace_558884 : CollatzResearch.WordTrace tailWord_558884 prefixEnd_558884 255089886317774753315329 := by
  unfold tailWord_558884
  simp only [CollatzResearch.WordTrace]
  refine ⟨10192087053633096316581853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13589449404844128422109137 10192087053633096316581853)
  ·
    refine ⟨3822032645112411118718195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10192087053633096316581853 3822032645112411118718195)
    ·
      refine ⟨5733048967668616678077293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3822032645112411118718195 5733048967668616678077293)
      ·
        refine ⟨2149893362875731254278985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5733048967668616678077293 2149893362875731254278985)
        ·
          refine ⟨1612420022156798440709239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2149893362875731254278985 1612420022156798440709239)
          ·
            refine ⟨2418630033235197661063859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1612420022156798440709239 2418630033235197661063859)
            ·
              refine ⟨3627945049852796491595789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2418630033235197661063859 3627945049852796491595789)
              ·
                refine ⟨1360479393694798684348421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3627945049852796491595789 1360479393694798684348421)
                ·
                  refine ⟨255089886317774753315329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1360479393694798684348421 255089886317774753315329)
                  ·
                    rfl

theorem cell20_558884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_558884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558884 prefixEnd_558884 := by exact prefixLift 558884
  have htrace : WordTrace (prefixWord ++ tailWord_558884) baseStart_558884 baseEnd_558884 := by
    simpa [prefixWord, tailWord_558884, baseEnd_558884] using wordTrace_append hprefix tailTrace_558884
  have hstable : (prefixWord ++ tailWord_558884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558884).length < 2 ^ (prefixWord ++ tailWord_558884).sum := by decide
  have hdescent : baseEnd_558884 < baseStart_558884 := by decide
  rcases family_descends (prefixWord ++ tailWord_558884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558929 : List Nat := [1, 2, 2, 1, 5, 3, 6]
def baseStart_558929 : Nat := 118140960795 + 558929 * 2 ^ 59
def prefixEnd_558929 : Nat := 4983230072969 + 3 ^ 40 * 558929 * 2
def baseEnd_558929 : Nat := 28345602838217177423905

theorem tailTrace_558929 : CollatzResearch.WordTrace tailWord_558929 prefixEnd_558929 28345602838217177423905 := by
  unfold tailWord_558929
  simp only [CollatzResearch.WordTrace]
  refine ⟨20385815392103165318551841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13590543594735443545701227 20385815392103165318551841)
  ·
    refine ⟨15289361544077373988913881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20385815392103165318551841 15289361544077373988913881)
    ·
      refine ⟨11467021158058030491685411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15289361544077373988913881 11467021158058030491685411)
      ·
        refine ⟨17200531737087045737528117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11467021158058030491685411 17200531737087045737528117)
        ·
          refine ⟨1612549850351910537893261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17200531737087045737528117 1612549850351910537893261)
          ·
            refine ⟨604706193881966451709973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1612549850351910537893261 604706193881966451709973)
            ·
              refine ⟨28345602838217177423905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 604706193881966451709973 28345602838217177423905)
              ·
                rfl

theorem cell20_558929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 6].length) (baseStart_558929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558929 prefixEnd_558929 := by exact prefixLift 558929
  have htrace : WordTrace (prefixWord ++ tailWord_558929) baseStart_558929 baseEnd_558929 := by
    simpa [prefixWord, tailWord_558929, baseEnd_558929] using wordTrace_append hprefix tailTrace_558929
  have hstable : (prefixWord ++ tailWord_558929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558929).length < 2 ^ (prefixWord ++ tailWord_558929).sum := by decide
  have hdescent : baseEnd_558929 < baseStart_558929 := by decide
  rcases family_descends (prefixWord ++ tailWord_558929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558946 : List Nat := [3, 3, 2, 1, 2, 2, 2, 5]
def baseStart_558946 : Nat := 118140960795 + 558946 * 2 ^ 59
def prefixEnd_558946 : Nat := 4983230072969 + 3 ^ 40 * 558946 * 2
def baseEnd_558946 : Nat := 85039394935726031082803

theorem tailTrace_558946 : CollatzResearch.WordTrace tailWord_558946 prefixEnd_558946 85039394935726031082803 := by
  unfold tailWord_558946
  simp only [CollatzResearch.WordTrace]
  refine ⟨5096608858260394305480173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13590956955361051481280461 5096608858260394305480173)
  ·
    refine ⟨1911228321847647864555065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5096608858260394305480173 1911228321847647864555065)
    ·
      refine ⟨1433421241385735898416299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1911228321847647864555065 1433421241385735898416299)
      ·
        refine ⟨2150131862078603847624449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1433421241385735898416299 2150131862078603847624449)
        ·
          refine ⟨1612598896558952885718337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2150131862078603847624449 1612598896558952885718337)
          ·
            refine ⟨1209449172419214664288753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1612598896558952885718337 1209449172419214664288753)
            ·
              refine ⟨907086879314410998216565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1209449172419214664288753 907086879314410998216565)
              ·
                refine ⟨85039394935726031082803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 907086879314410998216565 85039394935726031082803)
                ·
                  rfl

theorem cell20_558946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_558946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558946 prefixEnd_558946 := by exact prefixLift 558946
  have htrace : WordTrace (prefixWord ++ tailWord_558946) baseStart_558946 baseEnd_558946 := by
    simpa [prefixWord, tailWord_558946, baseEnd_558946] using wordTrace_append hprefix tailTrace_558946
  have hstable : (prefixWord ++ tailWord_558946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558946).length < 2 ^ (prefixWord ++ tailWord_558946).sum := by decide
  have hdescent : baseEnd_558946 < baseStart_558946 := by decide
  rcases family_descends (prefixWord ++ tailWord_558946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558990 : List Nat := [4, 1, 1, 5, 1, 2, 2, 2, 2]
def baseStart_558990 : Nat := 118140960795 + 558990 * 2 ^ 59
def prefixEnd_558990 : Nat := 4983230072969 + 3 ^ 40 * 558990 * 2
def baseEnd_558990 : Nat := 255138267606109495781563

theorem tailTrace_558990 : CollatzResearch.WordTrace tailWord_558990 prefixEnd_558990 255138267606109495781563 := by
  unfold tailWord_558990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2548505030610271592065303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13592026829921448491014949 2548505030610271592065303)
  ·
    refine ⟨3822757545915407388097955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2548505030610271592065303 3822757545915407388097955)
    ·
      refine ⟨5734136318873111082146933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3822757545915407388097955 5734136318873111082146933)
      ·
        refine ⟨537575279894354163951275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5734136318873111082146933 537575279894354163951275)
        ·
          refine ⟨806362919841531245926913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537575279894354163951275 806362919841531245926913)
          ·
            refine ⟨604772189881148434445185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 806362919841531245926913 604772189881148434445185)
            ·
              refine ⟨453579142410861325833889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 604772189881148434445185 453579142410861325833889)
              ·
                refine ⟨340184356808145994375417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453579142410861325833889 340184356808145994375417)
                ·
                  refine ⟨255138267606109495781563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340184356808145994375417 255138267606109495781563)
                  ·
                    rfl

theorem cell20_558990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_558990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558990 prefixEnd_558990 := by exact prefixLift 558990
  have htrace : WordTrace (prefixWord ++ tailWord_558990) baseStart_558990 baseEnd_558990 := by
    simpa [prefixWord, tailWord_558990, baseEnd_558990] using wordTrace_append hprefix tailTrace_558990
  have hstable : (prefixWord ++ tailWord_558990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558990).length < 2 ^ (prefixWord ++ tailWord_558990).sum := by decide
  have hdescent : baseEnd_558990 < baseStart_558990 := by decide
  rcases family_descends (prefixWord ++ tailWord_558990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558994 : List Nat := [3, 2, 3, 2, 1, 2, 1, 4, 2]
def baseStart_558994 : Nat := 118140960795 + 558994 * 2 ^ 59
def prefixEnd_558994 : Nat := 4983230072969 + 3 ^ 40 * 558994 * 2
def baseEnd_558994 : Nat := 255140093315103259648213

theorem tailTrace_558994 : CollatzResearch.WordTrace tailWord_558994 prefixEnd_558994 255140093315103259648213 := by
  unfold tailWord_558994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5097046534216920354917009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13592124091245120946445357 5097046534216920354917009)
  ·
    refine ⟨3822784900662690266187757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5097046534216920354917009 3822784900662690266187757)
    ·
      refine ⟨1433544337748508849820409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3822784900662690266187757 1433544337748508849820409)
      ·
        refine ⟨1075158253311381637365307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1433544337748508849820409 1075158253311381637365307)
        ·
          refine ⟨1612737379967072456047961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1075158253311381637365307 1612737379967072456047961)
          ·
            refine ⟨1209553034975304342035971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1612737379967072456047961 1209553034975304342035971)
            ·
              refine ⟨1814329552462956513053957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209553034975304342035971 1814329552462956513053957)
              ·
                refine ⟨340186791086804346197617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1814329552462956513053957 340186791086804346197617)
                ·
                  refine ⟨255140093315103259648213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340186791086804346197617 255140093315103259648213)
                  ·
                    rfl

theorem cell20_558994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_558994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558994 prefixEnd_558994 := by exact prefixLift 558994
  have htrace : WordTrace (prefixWord ++ tailWord_558994) baseStart_558994 baseEnd_558994 := by
    simpa [prefixWord, tailWord_558994, baseEnd_558994] using wordTrace_append hprefix tailTrace_558994
  have hstable : (prefixWord ++ tailWord_558994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558994).length < 2 ^ (prefixWord ++ tailWord_558994).sum := by decide
  have hdescent : baseEnd_558994 < baseStart_558994 := by decide
  rcases family_descends (prefixWord ++ tailWord_558994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558995 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 9]
def baseStart_558995 : Nat := 118140960795 + 558995 * 2 ^ 59
def prefixEnd_558995 : Nat := 4983230072969 + 3 ^ 40 * 558995 * 2
def baseEnd_558995 : Nat := 255140549742351700614875

theorem tailTrace_558995 : CollatzResearch.WordTrace tailWord_558995 prefixEnd_558995 255140549742351700614875 := by
  unfold tailWord_558995
  simp only [CollatzResearch.WordTrace]
  refine ⟨20388222609864058590454439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13592148406576039060302959 20388222609864058590454439)
  ·
    refine ⟨30582333914796087885681659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20388222609864058590454439 30582333914796087885681659)
    ·
      refine ⟨45873500872194131828522489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30582333914796087885681659 45873500872194131828522489)
      ·
        refine ⟨34405125654145598871391867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45873500872194131828522489 34405125654145598871391867)
        ·
          refine ⟨51607688481218398307087801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34405125654145598871391867 51607688481218398307087801)
          ·
            refine ⟨38705766360913798730315851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51607688481218398307087801 38705766360913798730315851)
            ·
              refine ⟨58058649541370698095473777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38705766360913798730315851 58058649541370698095473777)
              ·
                refine ⟨43543987156028023571605333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58058649541370698095473777 43543987156028023571605333)
                ·
                  refine ⟨255140549742351700614875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43543987156028023571605333 255140549742351700614875)
                  ·
                    rfl

theorem cell20_558995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_558995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_558995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_558995 prefixEnd_558995 := by exact prefixLift 558995
  have htrace : WordTrace (prefixWord ++ tailWord_558995) baseStart_558995 baseEnd_558995 := by
    simpa [prefixWord, tailWord_558995, baseEnd_558995] using wordTrace_append hprefix tailTrace_558995
  have hstable : (prefixWord ++ tailWord_558995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558995).length < 2 ^ (prefixWord ++ tailWord_558995).sum := by decide
  have hdescent : baseEnd_558995 < baseStart_558995 := by decide
  rcases family_descends (prefixWord ++ tailWord_558995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559005 : List Nat := [1, 4, 2, 1, 2, 2, 3, 5]
def baseStart_559005 : Nat := 118140960795 + 559005 * 2 ^ 59
def prefixEnd_559005 : Nat := 4983230072969 + 3 ^ 40 * 559005 * 2
def baseEnd_559005 : Nat := 85048371338278703427167

theorem tailTrace_559005 : CollatzResearch.WordTrace tailWord_559005 prefixEnd_559005 85048371338278703427167 := by
  unfold tailWord_559005
  simp only [CollatzResearch.WordTrace]
  refine ⟨20388587339827830298318469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13592391559885220198878979 20388587339827830298318469)
  ·
    refine ⟨3822860126217718180934713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20388587339827830298318469 3822860126217718180934713)
    ·
      refine ⟨2867145094663288635701035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3822860126217718180934713 2867145094663288635701035)
      ·
        refine ⟨4300717641994932953551553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2867145094663288635701035 4300717641994932953551553)
        ·
          refine ⟨3225538231496199715163665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4300717641994932953551553 3225538231496199715163665)
          ·
            refine ⟨2419153673622149786372749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3225538231496199715163665 2419153673622149786372749)
            ·
              refine ⟨907182627608306169889781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2419153673622149786372749 907182627608306169889781)
              ·
                refine ⟨85048371338278703427167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 907182627608306169889781 85048371338278703427167)
                ·
                  rfl

theorem cell20_559005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 5].length) (baseStart_559005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559005 prefixEnd_559005 := by exact prefixLift 559005
  have htrace : WordTrace (prefixWord ++ tailWord_559005) baseStart_559005 baseEnd_559005 := by
    simpa [prefixWord, tailWord_559005, baseEnd_559005] using wordTrace_append hprefix tailTrace_559005
  have hstable : (prefixWord ++ tailWord_559005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559005).length < 2 ^ (prefixWord ++ tailWord_559005).sum := by decide
  have hdescent : baseEnd_559005 < baseStart_559005 := by decide
  rcases family_descends (prefixWord ++ tailWord_559005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559026 : List Nat := [3, 2, 1, 1, 1, 1, 1, 10]
def baseStart_559026 : Nat := 118140960795 + 559026 * 2 ^ 59
def prefixEnd_559026 : Nat := 4983230072969 + 3 ^ 40 * 559026 * 2
def baseEnd_559026 : Nat := 85051566329017790193805

theorem tailTrace_559026 : CollatzResearch.WordTrace tailWord_559026 prefixEnd_559026 85051566329017790193805 := by
  unfold tailWord_559026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5097338318187937721208233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13592902181834500589888621 5097338318187937721208233)
  ·
    refine ⟨3823003738640953290906175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5097338318187937721208233 3823003738640953290906175)
    ·
      refine ⟨5734505607961429936359263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3823003738640953290906175 5734505607961429936359263)
      ·
        refine ⟨8601758411942144904538895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5734505607961429936359263 8601758411942144904538895)
        ·
          refine ⟨12902637617913217356808343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8601758411942144904538895 12902637617913217356808343)
          ·
            refine ⟨19353956426869826035212515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12902637617913217356808343 19353956426869826035212515)
            ·
              refine ⟨29030934640304739052818773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19353956426869826035212515 29030934640304739052818773)
              ·
                refine ⟨85051566329017790193805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29030934640304739052818773 85051566329017790193805)
                ·
                  rfl

theorem cell20_559026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_559026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559026 prefixEnd_559026 := by exact prefixLift 559026
  have htrace : WordTrace (prefixWord ++ tailWord_559026) baseStart_559026 baseEnd_559026 := by
    simpa [prefixWord, tailWord_559026, baseEnd_559026] using wordTrace_append hprefix tailTrace_559026
  have hstable : (prefixWord ++ tailWord_559026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559026).length < 2 ^ (prefixWord ++ tailWord_559026).sum := by decide
  have hdescent : baseEnd_559026 < baseStart_559026 := by decide
  rcases family_descends (prefixWord ++ tailWord_559026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559064 : List Nat := [2, 1, 2, 2, 2, 2, 2, 7]
def baseStart_559064 : Nat := 118140960795 + 559064 * 2 ^ 59
def prefixEnd_559064 : Nat := 4983230072969 + 3 ^ 40 * 559064 * 2
def baseEnd_559064 : Nat := 85057347740831375771531

theorem tailTrace_559064 : CollatzResearch.WordTrace tailWord_559064 prefixEnd_559064 85057347740831375771531 := by
  unfold tailWord_559064
  simp only [CollatzResearch.WordTrace]
  refine ⟨10195369623307041687358123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13593826164409388916477497 10195369623307041687358123)
  ·
    refine ⟨15293054434960562531037185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10195369623307041687358123 15293054434960562531037185)
    ·
      refine ⟨11469790826220421898277889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15293054434960562531037185 11469790826220421898277889)
      ·
        refine ⟨8602343119665316423708417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11469790826220421898277889 8602343119665316423708417)
        ·
          refine ⟨6451757339748987317781313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8602343119665316423708417 6451757339748987317781313)
          ·
            refine ⟨4838818004811740488335985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6451757339748987317781313 4838818004811740488335985)
            ·
              refine ⟨3629113503608805366251989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4838818004811740488335985 3629113503608805366251989)
              ·
                refine ⟨85057347740831375771531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3629113503608805366251989 85057347740831375771531)
                ·
                  rfl

theorem cell20_559064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_559064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559064 prefixEnd_559064 := by exact prefixLift 559064
  have htrace : WordTrace (prefixWord ++ tailWord_559064) baseStart_559064 baseEnd_559064 := by
    simpa [prefixWord, tailWord_559064, baseEnd_559064] using wordTrace_append hprefix tailTrace_559064
  have hstable : (prefixWord ++ tailWord_559064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559064).length < 2 ^ (prefixWord ++ tailWord_559064).sum := by decide
  have hdescent : baseEnd_559064 < baseStart_559064 := by decide
  rcases family_descends (prefixWord ++ tailWord_559064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559108 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 4]
def baseStart_559108 : Nat := 118140960795 + 559108 * 2 ^ 59
def prefixEnd_559108 : Nat := 4983230072969 + 3 ^ 40 * 559108 * 2
def baseEnd_559108 : Nat := 255192126021425529847747

theorem tailTrace_559108 : CollatzResearch.WordTrace tailWord_559108 prefixEnd_559108 255192126021425529847747 := by
  unfold tailWord_559108
  simp only [CollatzResearch.WordTrace]
  refine ⟨10196172029227339444658989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13594896038969785926211985 10196172029227339444658989)
  ·
    refine ⟨3823564510960252291747121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10196172029227339444658989 3823564510960252291747121)
    ·
      refine ⟨2867673383220189218810341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3823564510960252291747121 2867673383220189218810341)
      ·
        refine ⟨537688759353785478526939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2867673383220189218810341 537688759353785478526939)
        ·
          refine ⟨806533139030678217790409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537688759353785478526939 806533139030678217790409)
          ·
            refine ⟨604899854273008663342807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 806533139030678217790409 604899854273008663342807)
            ·
              refine ⟨907349781409512995014211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604899854273008663342807 907349781409512995014211)
              ·
                refine ⟨1361024672114269492521317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 907349781409512995014211 1361024672114269492521317)
                ·
                  refine ⟨255192126021425529847747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1361024672114269492521317 255192126021425529847747)
                  ·
                    rfl

theorem cell20_559108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_559108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559108 prefixEnd_559108 := by exact prefixLift 559108
  have htrace : WordTrace (prefixWord ++ tailWord_559108) baseStart_559108 baseEnd_559108 := by
    simpa [prefixWord, tailWord_559108, baseEnd_559108] using wordTrace_append hprefix tailTrace_559108
  have hstable : (prefixWord ++ tailWord_559108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559108).length < 2 ^ (prefixWord ++ tailWord_559108).sum := by decide
  have hdescent : baseEnd_559108 < baseStart_559108 := by decide
  rcases family_descends (prefixWord ++ tailWord_559108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559147 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 5]
def baseStart_559147 : Nat := 118140960795 + 559147 * 2 ^ 59
def prefixEnd_559147 : Nat := 4983230072969 + 3 ^ 40 * 559147 * 2
def baseEnd_559147 : Nat := 255209926684114727547587

theorem tailTrace_559147 : CollatzResearch.WordTrace tailWord_559147 prefixEnd_559147 255209926684114727547587 := by
  unfold tailWord_559147
  simp only [CollatzResearch.WordTrace]
  refine ⟨20393766505313388549987695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13595844336875592366658463 20393766505313388549987695)
  ·
    refine ⟨30590649757970082824981543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20393766505313388549987695 30590649757970082824981543)
    ·
      refine ⟨45885974636955124237472315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30590649757970082824981543 45885974636955124237472315)
      ·
        refine ⟨68828961955432686356208473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45885974636955124237472315 68828961955432686356208473)
        ·
          refine ⟨51621721466574514767156355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68828961955432686356208473 51621721466574514767156355)
          ·
            refine ⟨77432582199861772150734533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51621721466574514767156355 77432582199861772150734533)
            ·
              refine ⟨14518609162474082278262725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77432582199861772150734533 14518609162474082278262725)
              ·
                refine ⟨2722239217963890427174261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14518609162474082278262725 2722239217963890427174261)
                ·
                  refine ⟨255209926684114727547587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2722239217963890427174261 255209926684114727547587)
                  ·
                    rfl

theorem cell20_559147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_559147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559147 prefixEnd_559147 := by exact prefixLift 559147
  have htrace : WordTrace (prefixWord ++ tailWord_559147) baseStart_559147 baseEnd_559147 := by
    simpa [prefixWord, tailWord_559147, baseEnd_559147] using wordTrace_append hprefix tailTrace_559147
  have hstable : (prefixWord ++ tailWord_559147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559147).length < 2 ^ (prefixWord ++ tailWord_559147).sum := by decide
  have hdescent : baseEnd_559147 < baseStart_559147 := by decide
  rcases family_descends (prefixWord ++ tailWord_559147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559167 : List Nat := [1, 1, 2, 2, 3, 1, 6, 2, 2]
def baseStart_559167 : Nat := 118140960795 + 559167 * 2 ^ 59
def prefixEnd_559167 : Nat := 4983230072969 + 3 ^ 40 * 559167 * 2
def baseEnd_559167 : Nat := 255219055229083546880839

theorem tailTrace_559167 : CollatzResearch.WordTrace tailWord_559167 prefixEnd_559167 255219055229083546880839 := by
  unfold tailWord_559167
  simp only [CollatzResearch.WordTrace]
  refine ⟨20394495965240931965715755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13596330643493954643810503 20394495965240931965715755)
  ·
    refine ⟨30591743947861397948573633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20394495965240931965715755 30591743947861397948573633)
    ·
      refine ⟨22943807960896048461430225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30591743947861397948573633 22943807960896048461430225)
      ·
        refine ⟨17207855970672036346072669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22943807960896048461430225 17207855970672036346072669)
        ·
          refine ⟨6452945989002013629777251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17207855970672036346072669 6452945989002013629777251)
          ·
            refine ⟨9679418983503020444665877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6452945989002013629777251 9679418983503020444665877)
            ·
              refine ⟨453722764851704083343713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9679418983503020444665877 453722764851704083343713)
              ·
                refine ⟨340292073638778062507785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453722764851704083343713 340292073638778062507785)
                ·
                  refine ⟨255219055229083546880839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340292073638778062507785 255219055229083546880839)
                  ·
                    rfl

theorem cell20_559167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 2].length) (baseStart_559167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559167 prefixEnd_559167 := by exact prefixLift 559167
  have htrace : WordTrace (prefixWord ++ tailWord_559167) baseStart_559167 baseEnd_559167 := by
    simpa [prefixWord, tailWord_559167, baseEnd_559167] using wordTrace_append hprefix tailTrace_559167
  have hstable : (prefixWord ++ tailWord_559167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559167).length < 2 ^ (prefixWord ++ tailWord_559167).sum := by decide
  have hdescent : baseEnd_559167 < baseStart_559167 := by decide
  rcases family_descends (prefixWord ++ tailWord_559167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559181 : List Nat := [1, 6, 1, 1, 1, 1, 1, 5, 3]
def baseStart_559181 : Nat := 118140960795 + 559181 * 2 ^ 59
def prefixEnd_559181 : Nat := 4983230072969 + 3 ^ 40 * 559181 * 2
def baseEnd_559181 : Nat := 255225445210561720414115

theorem tailTrace_559181 : CollatzResearch.WordTrace tailWord_559181 prefixEnd_559181 255225445210561720414115 := by
  unfold tailWord_559181
  simp only [CollatzResearch.WordTrace]
  refine ⟨20395006587190212356725397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13596671058126808237816931 20395006587190212356725397)
  ·
    refine ⟨956015933774541204221503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20395006587190212356725397 956015933774541204221503)
    ·
      refine ⟨1434023900661811806332255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 956015933774541204221503 1434023900661811806332255)
      ·
        refine ⟨2151035850992717709498383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1434023900661811806332255 2151035850992717709498383)
        ·
          refine ⟨3226553776489076564247575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2151035850992717709498383 3226553776489076564247575)
          ·
            refine ⟨4839830664733614846371363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3226553776489076564247575 4839830664733614846371363)
            ·
              refine ⟨7259745997100422269557045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4839830664733614846371363 7259745997100422269557045)
              ·
                refine ⟨680601187228164587770973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7259745997100422269557045 680601187228164587770973)
                ·
                  refine ⟨255225445210561720414115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680601187228164587770973 255225445210561720414115)
                  ·
                    rfl

theorem cell20_559181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_559181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559181 prefixEnd_559181 := by exact prefixLift 559181
  have htrace : WordTrace (prefixWord ++ tailWord_559181) baseStart_559181 baseEnd_559181 := by
    simpa [prefixWord, tailWord_559181, baseEnd_559181] using wordTrace_append hprefix tailTrace_559181
  have hstable : (prefixWord ++ tailWord_559181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559181).length < 2 ^ (prefixWord ++ tailWord_559181).sum := by decide
  have hdescent : baseEnd_559181 < baseStart_559181 := by decide
  rcases family_descends (prefixWord ++ tailWord_559181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559185 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 7]
def baseStart_559185 : Nat := 118140960795 + 559185 * 2 ^ 59
def prefixEnd_559185 : Nat := 4983230072969 + 3 ^ 40 * 559185 * 2
def baseEnd_559185 : Nat := 255227270919555484280765

theorem tailTrace_559185 : CollatzResearch.WordTrace tailWord_559185 prefixEnd_559185 255227270919555484280765 := by
  unfold tailWord_559185
  simp only [CollatzResearch.WordTrace]
  refine ⟨20395152479175721039871009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13596768319450480693247339 20395152479175721039871009)
  ·
    refine ⟨15296364359381790779903257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20395152479175721039871009 15296364359381790779903257)
    ·
      refine ⟨11472273269536343084927443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15296364359381790779903257 11472273269536343084927443)
      ·
        refine ⟨17208409904304514627391165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11472273269536343084927443 17208409904304514627391165)
        ·
          refine ⟨6453153714114192985271687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17208409904304514627391165 6453153714114192985271687)
          ·
            refine ⟨9679730571171289477907531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6453153714114192985271687 9679730571171289477907531)
            ·
              refine ⟨14519595856756934216861297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9679730571171289477907531 14519595856756934216861297)
              ·
                refine ⟨10889696892567700662645973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14519595856756934216861297 10889696892567700662645973)
                ·
                  refine ⟨255227270919555484280765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10889696892567700662645973 255227270919555484280765)
                  ·
                    rfl

theorem cell20_559185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_559185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559185 prefixEnd_559185 := by exact prefixLift 559185
  have htrace : WordTrace (prefixWord ++ tailWord_559185) baseStart_559185 baseEnd_559185 := by
    simpa [prefixWord, tailWord_559185, baseEnd_559185] using wordTrace_append hprefix tailTrace_559185
  have hstable : (prefixWord ++ tailWord_559185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559185).length < 2 ^ (prefixWord ++ tailWord_559185).sum := by decide
  have hdescent : baseEnd_559185 < baseStart_559185 := by decide
  rcases family_descends (prefixWord ++ tailWord_559185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559205 : List Nat := [1, 3, 1, 3, 2, 3, 2, 3, 2]
def baseStart_559205 : Nat := 118140960795 + 559205 * 2 ^ 59
def prefixEnd_559205 : Nat := 4983230072969 + 3 ^ 40 * 559205 * 2
def baseEnd_559205 : Nat := 255236399464524303614017

theorem tailTrace_559205 : CollatzResearch.WordTrace tailWord_559205 prefixEnd_559205 255236399464524303614017 := by
  unfold tailWord_559205
  simp only [CollatzResearch.WordTrace]
  refine ⟨20395881939103264455599069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13597254626068842970399379 20395881939103264455599069)
  ·
    refine ⟨7648455727163724170849651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20395881939103264455599069 7648455727163724170849651)
    ·
      refine ⟨11472683590745586256274477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7648455727163724170849651 11472683590745586256274477)
      ·
        refine ⟨4302256346529594846102929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11472683590745586256274477 4302256346529594846102929)
        ·
          refine ⟨3226692259897196134577197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4302256346529594846102929 3226692259897196134577197)
          ·
            refine ⟨1210009597461448550466449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3226692259897196134577197 1210009597461448550466449)
            ·
              refine ⟨907507198096086412849837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1210009597461448550466449 907507198096086412849837)
              ·
                refine ⟨340315199286032404818689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 907507198096086412849837 340315199286032404818689)
                ·
                  refine ⟨255236399464524303614017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340315199286032404818689 255236399464524303614017)
                  ·
                    rfl

theorem cell20_559205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_559205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559205 prefixEnd_559205 := by exact prefixLift 559205
  have htrace : WordTrace (prefixWord ++ tailWord_559205) baseStart_559205 baseEnd_559205 := by
    simpa [prefixWord, tailWord_559205, baseEnd_559205] using wordTrace_append hprefix tailTrace_559205
  have hstable : (prefixWord ++ tailWord_559205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559205).length < 2 ^ (prefixWord ++ tailWord_559205).sum := by decide
  have hdescent : baseEnd_559205 < baseStart_559205 := by decide
  rcases family_descends (prefixWord ++ tailWord_559205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559216 : List Nat := [2, 1, 1, 1, 5, 3, 7]
def baseStart_559216 : Nat := 118140960795 + 559216 * 2 ^ 59
def prefixEnd_559216 : Nat := 4983230072969 + 3 ^ 40 * 559216 * 2
def baseEnd_559216 : Nat := 28360157796028572694145

theorem tailTrace_559216 : CollatzResearch.WordTrace tailWord_559216 prefixEnd_559216 28360157796028572694145 := by
  unfold tailWord_559216
  simp only [CollatzResearch.WordTrace]
  refine ⟨10198141571031706667124751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13597522094708942222833001 10198141571031706667124751)
  ·
    refine ⟨15297212356547560000687127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10198141571031706667124751 15297212356547560000687127)
    ·
      refine ⟨22945818534821340001030691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15297212356547560000687127 22945818534821340001030691)
      ·
        refine ⟨34418727802232010001546037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22945818534821340001030691 34418727802232010001546037)
        ·
          refine ⟨3226755731459250937644941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34418727802232010001546037 3226755731459250937644941)
          ·
            refine ⟨1210033399297219101616853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3226755731459250937644941 1210033399297219101616853)
            ·
              refine ⟨28360157796028572694145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1210033399297219101616853 28360157796028572694145)
              ·
                rfl

theorem cell20_559216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 7].length) (baseStart_559216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559216 prefixEnd_559216 := by exact prefixLift 559216
  have htrace : WordTrace (prefixWord ++ tailWord_559216) baseStart_559216 baseEnd_559216 := by
    simpa [prefixWord, tailWord_559216, baseEnd_559216] using wordTrace_append hprefix tailTrace_559216
  have hstable : (prefixWord ++ tailWord_559216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559216).length < 2 ^ (prefixWord ++ tailWord_559216).sum := by decide
  have hdescent : baseEnd_559216 < baseStart_559216 := by decide
  rcases family_descends (prefixWord ++ tailWord_559216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559281 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 4]
def baseStart_559281 : Nat := 118140960795 + 559281 * 2 ^ 59
def prefixEnd_559281 : Nat := 4983230072969 + 3 ^ 40 * 559281 * 2
def baseEnd_559281 : Nat := 255271087935405817080373

theorem tailTrace_559281 : CollatzResearch.WordTrace tailWord_559281 prefixEnd_559281 255271087935405817080373 := by
  unfold tailWord_559281
  simp only [CollatzResearch.WordTrace]
  refine ⟨20398653886827929435365697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13599102591218619623577131 20398653886827929435365697)
  ·
    refine ⟨15298990415120947076524273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20398653886827929435365697 15298990415120947076524273)
    ·
      refine ⟨11474242811340710307393205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15298990415120947076524273 11474242811340710307393205)
      ·
        refine ⟨1075710263563191591318113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11474242811340710307393205 1075710263563191591318113)
        ·
          refine ⟨806782697672393693488585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1075710263563191591318113 806782697672393693488585)
          ·
            refine ⟨605087023254295270116439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 806782697672393693488585 605087023254295270116439)
            ·
              refine ⟨907630534881442905174659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 605087023254295270116439 907630534881442905174659)
              ·
                refine ⟨1361445802322164357761989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 907630534881442905174659 1361445802322164357761989)
                ·
                  refine ⟨255271087935405817080373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1361445802322164357761989 255271087935405817080373)
                  ·
                    rfl

theorem cell20_559281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_559281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559281 prefixEnd_559281 := by exact prefixLift 559281
  have htrace : WordTrace (prefixWord ++ tailWord_559281) baseStart_559281 baseEnd_559281 := by
    simpa [prefixWord, tailWord_559281, baseEnd_559281] using wordTrace_append hprefix tailTrace_559281
  have hstable : (prefixWord ++ tailWord_559281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559281).length < 2 ^ (prefixWord ++ tailWord_559281).sum := by decide
  have hdescent : baseEnd_559281 < baseStart_559281 := by decide
  rcases family_descends (prefixWord ++ tailWord_559281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559284 : List Nat := [2, 5, 3, 1, 1, 1, 2, 5]
def baseStart_559284 : Nat := 118140960795 + 559284 * 2 ^ 59
def prefixEnd_559284 : Nat := 4983230072969 + 3 ^ 40 * 559284 * 2
def baseEnd_559284 : Nat := 85090819072383713326787

theorem tailTrace_559284 : CollatzResearch.WordTrace tailWord_559284 prefixEnd_559284 85090819072383713326787 := by
  unfold tailWord_559284
  simp only [CollatzResearch.WordTrace]
  refine ⟨10199381652908530473862453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13599175537211373965149937 10199381652908530473862453)
  ·
    refine ⟨956192029960174731924605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10199381652908530473862453 956192029960174731924605)
    ·
      refine ⟨358572011235065524471727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 956192029960174731924605 358572011235065524471727)
      ·
        refine ⟨537858016852598286707591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358572011235065524471727 537858016852598286707591)
        ·
          refine ⟨806787025278897430061387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537858016852598286707591 806787025278897430061387)
          ·
            refine ⟨1210180537918346145092081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806787025278897430061387 1210180537918346145092081)
            ·
              refine ⟨907635403438759608819061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1210180537918346145092081 907635403438759608819061)
              ·
                refine ⟨85090819072383713326787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 907635403438759608819061 85090819072383713326787)
                ·
                  rfl

theorem cell20_559284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_559284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559284 prefixEnd_559284 := by exact prefixLift 559284
  have htrace : WordTrace (prefixWord ++ tailWord_559284) baseStart_559284 baseEnd_559284 := by
    simpa [prefixWord, tailWord_559284, baseEnd_559284] using wordTrace_append hprefix tailTrace_559284
  have hstable : (prefixWord ++ tailWord_559284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559284).length < 2 ^ (prefixWord ++ tailWord_559284).sum := by decide
  have hdescent : baseEnd_559284 < baseStart_559284 := by decide
  rcases family_descends (prefixWord ++ tailWord_559284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559333 : List Nat := [1, 3, 1, 4, 2, 2, 2, 2, 3]
def baseStart_559333 : Nat := 118140960795 + 559333 * 2 ^ 59
def prefixEnd_559333 : Nat := 4983230072969 + 3 ^ 40 * 559333 * 2
def baseEnd_559333 : Nat := 255294822152324747346827

theorem tailTrace_559333 : CollatzResearch.WordTrace tailWord_559333 prefixEnd_559333 255294822152324747346827 := by
  unfold tailWord_559333
  simp only [CollatzResearch.WordTrace]
  refine ⟨20400550482639542316258653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13600366988426361544172435 20400550482639542316258653)
  ·
    refine ⟨7650206430989828368596995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20400550482639542316258653 7650206430989828368596995)
    ·
      refine ⟨11475309646484742552895493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7650206430989828368596995 11475309646484742552895493)
      ·
        refine ⟨2151620558715889228667905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11475309646484742552895493 2151620558715889228667905)
        ·
          refine ⟨1613715419036916921500929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2151620558715889228667905 1613715419036916921500929)
          ·
            refine ⟨1210286564277687691125697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1613715419036916921500929 1210286564277687691125697)
            ·
              refine ⟨907714923208265768344273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1210286564277687691125697 907714923208265768344273)
              ·
                refine ⟨680786192406199326258205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 907714923208265768344273 680786192406199326258205)
                ·
                  refine ⟨255294822152324747346827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680786192406199326258205 255294822152324747346827)
                  ·
                    rfl

theorem cell20_559333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_559333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559333 prefixEnd_559333 := by exact prefixLift 559333
  have htrace : WordTrace (prefixWord ++ tailWord_559333) baseStart_559333 baseEnd_559333 := by
    simpa [prefixWord, tailWord_559333, baseEnd_559333] using wordTrace_append hprefix tailTrace_559333
  have hstable : (prefixWord ++ tailWord_559333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559333).length < 2 ^ (prefixWord ++ tailWord_559333).sum := by decide
  have hdescent : baseEnd_559333 < baseStart_559333 := by decide
  rcases family_descends (prefixWord ++ tailWord_559333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559336 : List Nat := [2, 1, 4, 1, 2, 4, 2, 2, 2]
def baseStart_559336 : Nat := 118140960795 + 559336 * 2 ^ 59
def prefixEnd_559336 : Nat := 4983230072969 + 3 ^ 40 * 559336 * 2
def baseEnd_559336 : Nat := 255296191434070070246815

theorem tailTrace_559336 : CollatzResearch.WordTrace tailWord_559336 prefixEnd_559336 255296191434070070246815 := by
  unfold tailWord_559336
  simp only [CollatzResearch.WordTrace]
  refine ⟨10200329950814336914308931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13600439934419115885745241 10200329950814336914308931)
  ·
    refine ⟨15300494926221505371463397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10200329950814336914308931 15300494926221505371463397)
    ·
      refine ⟨2868842798666532257149387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15300494926221505371463397 2868842798666532257149387)
      ·
        refine ⟨4303264197999798385724081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2868842798666532257149387 4303264197999798385724081)
        ·
          refine ⟨3227448148499848789293061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4303264197999798385724081 3227448148499848789293061)
          ·
            refine ⟨605146527843721647992449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3227448148499848789293061 605146527843721647992449)
            ·
              refine ⟨453859895882791235994337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 605146527843721647992449 453859895882791235994337)
              ·
                refine ⟨340394921912093426995753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453859895882791235994337 340394921912093426995753)
                ·
                  refine ⟨255296191434070070246815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340394921912093426995753 255296191434070070246815)
                  ·
                    rfl

theorem cell20_559336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 2].length) (baseStart_559336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559336 prefixEnd_559336 := by exact prefixLift 559336
  have htrace : WordTrace (prefixWord ++ tailWord_559336) baseStart_559336 baseEnd_559336 := by
    simpa [prefixWord, tailWord_559336, baseEnd_559336] using wordTrace_append hprefix tailTrace_559336
  have hstable : (prefixWord ++ tailWord_559336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559336).length < 2 ^ (prefixWord ++ tailWord_559336).sum := by decide
  have hdescent : baseEnd_559336 < baseStart_559336 := by decide
  rcases family_descends (prefixWord ++ tailWord_559336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559340 : List Nat := [2, 2, 1, 1, 2, 3, 3, 4, 2]
def baseStart_559340 : Nat := 118140960795 + 559340 * 2 ^ 59
def prefixEnd_559340 : Nat := 4983230072969 + 3 ^ 40 * 559340 * 2
def baseEnd_559340 : Nat := 255298017143063834113465

theorem tailTrace_559340 : CollatzResearch.WordTrace tailWord_559340 prefixEnd_559340 255298017143063834113465 := by
  unfold tailWord_559340
  simp only [CollatzResearch.WordTrace]
  refine ⟨10200402896807091255881737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13600537195742788341175649 10200402896807091255881737)
  ·
    refine ⟨7650302172605318441911303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10200402896807091255881737 7650302172605318441911303)
    ·
      refine ⟨11475453258907977662866955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7650302172605318441911303 11475453258907977662866955)
      ·
        refine ⟨17213179888361966494300433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11475453258907977662866955 17213179888361966494300433)
        ·
          refine ⟨12909884916271474870725325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17213179888361966494300433 12909884916271474870725325)
          ·
            refine ⟨4841206843601803076521997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12909884916271474870725325 4841206843601803076521997)
            ·
              refine ⟨1815452566350676153695749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4841206843601803076521997 1815452566350676153695749)
              ·
                refine ⟨340397356190751778817953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1815452566350676153695749 340397356190751778817953)
                ·
                  refine ⟨255298017143063834113465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340397356190751778817953 255298017143063834113465)
                  ·
                    rfl

theorem cell20_559340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_559340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559340 prefixEnd_559340 := by exact prefixLift 559340
  have htrace : WordTrace (prefixWord ++ tailWord_559340) baseStart_559340 baseEnd_559340 := by
    simpa [prefixWord, tailWord_559340, baseEnd_559340] using wordTrace_append hprefix tailTrace_559340
  have hstable : (prefixWord ++ tailWord_559340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559340).length < 2 ^ (prefixWord ++ tailWord_559340).sum := by decide
  have hdescent : baseEnd_559340 < baseStart_559340 := by decide
  rcases family_descends (prefixWord ++ tailWord_559340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559344 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 8]
def baseStart_559344 : Nat := 118140960795 + 559344 * 2 ^ 59
def prefixEnd_559344 : Nat := 4983230072969 + 3 ^ 40 * 559344 * 2
def baseEnd_559344 : Nat := 255299842852057597980115

theorem tailTrace_559344 : CollatzResearch.WordTrace tailWord_559344 prefixEnd_559344 255299842852057597980115 := by
  unfold tailWord_559344
  simp only [CollatzResearch.WordTrace]
  refine ⟨10200475842799845597454543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13600634457066460796606057 10200475842799845597454543)
  ·
    refine ⟨15300713764199768396181815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10200475842799845597454543 15300713764199768396181815)
    ·
      refine ⟨22951070646299652594272723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15300713764199768396181815 22951070646299652594272723)
      ·
        refine ⟨34426605969449478891409085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22951070646299652594272723 34426605969449478891409085)
        ·
          refine ⟨12909977238543554584278407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34426605969449478891409085 12909977238543554584278407)
          ·
            refine ⟨19364965857815331876417611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12909977238543554584278407 19364965857815331876417611)
            ·
              refine ⟨29047448786722997814626417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19364965857815331876417611 29047448786722997814626417)
              ·
                refine ⟨21785586590042248360969813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29047448786722997814626417 21785586590042248360969813)
                ·
                  refine ⟨255299842852057597980115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21785586590042248360969813 255299842852057597980115)
                  ·
                    rfl

theorem cell20_559344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_559344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559344 prefixEnd_559344 := by exact prefixLift 559344
  have htrace : WordTrace (prefixWord ++ tailWord_559344) baseStart_559344 baseEnd_559344 := by
    simpa [prefixWord, tailWord_559344, baseEnd_559344] using wordTrace_append hprefix tailTrace_559344
  have hstable : (prefixWord ++ tailWord_559344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559344).length < 2 ^ (prefixWord ++ tailWord_559344).sum := by decide
  have hdescent : baseEnd_559344 < baseStart_559344 := by decide
  rcases family_descends (prefixWord ++ tailWord_559344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559354 : List Nat := [3, 1, 1, 1, 1, 5, 2, 3, 3]
def baseStart_559354 : Nat := 118140960795 + 559354 * 2 ^ 59
def prefixEnd_559354 : Nat := 4983230072969 + 3 ^ 40 * 559354 * 2
def baseEnd_559354 : Nat := 255304407124542007646741

theorem tailTrace_559354 : CollatzResearch.WordTrace tailWord_559354 prefixEnd_559354 255304407124542007646741 := by
  unfold tailWord_559354
  simp only [CollatzResearch.WordTrace]
  refine ⟨5100329103890865725693279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13600877610375641935182077 5100329103890865725693279)
  ·
    refine ⟨7650493655836298588539919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5100329103890865725693279 7650493655836298588539919)
    ·
      refine ⟨11475740483754447882809879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7650493655836298588539919 11475740483754447882809879)
      ·
        refine ⟨17213610725631671824214819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11475740483754447882809879 17213610725631671824214819)
        ·
          refine ⟨25820416088447507736322229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17213610725631671824214819 25820416088447507736322229)
          ·
            refine ⟨2420664008291953850280209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25820416088447507736322229 2420664008291953850280209)
            ·
              refine ⟨1815498006218965387710157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2420664008291953850280209 1815498006218965387710157)
              ·
                refine ⟨680811752332112020391309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1815498006218965387710157 680811752332112020391309)
                ·
                  refine ⟨255304407124542007646741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680811752332112020391309 255304407124542007646741)
                  ·
                    rfl

theorem cell20_559354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_559354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559354 prefixEnd_559354 := by exact prefixLift 559354
  have htrace : WordTrace (prefixWord ++ tailWord_559354) baseStart_559354 baseEnd_559354 := by
    simpa [prefixWord, tailWord_559354, baseEnd_559354] using wordTrace_append hprefix tailTrace_559354
  have hstable : (prefixWord ++ tailWord_559354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559354).length < 2 ^ (prefixWord ++ tailWord_559354).sum := by decide
  have hdescent : baseEnd_559354 < baseStart_559354 := by decide
  rcases family_descends (prefixWord ++ tailWord_559354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559361 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 4]
def baseStart_559361 : Nat := 118140960795 + 559361 * 2 ^ 59
def prefixEnd_559361 : Nat := 4983230072969 + 3 ^ 40 * 559361 * 2
def baseEnd_559361 : Nat := 255307602115281094413379

theorem tailTrace_559361 : CollatzResearch.WordTrace tailWord_559361 prefixEnd_559361 255307602115281094413379 := by
  unfold tailWord_559361
  simp only [CollatzResearch.WordTrace]
  refine ⟨20401571726538103098277937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13601047817692068732185291 20401571726538103098277937)
  ·
    refine ⟨15301178794903577323708453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20401571726538103098277937 15301178794903577323708453)
    ·
      refine ⟨2868971024044420748195335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15301178794903577323708453 2868971024044420748195335)
      ·
        refine ⟨4303456536066631122293003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2868971024044420748195335 4303456536066631122293003)
        ·
          refine ⟨6455184804099946683439505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4303456536066631122293003 6455184804099946683439505)
          ·
            refine ⟨4841388603074960012579629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6455184804099946683439505 4841388603074960012579629)
            ·
              refine ⟨1815520726153110004717361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4841388603074960012579629 1815520726153110004717361)
              ·
                refine ⟨1361640544614832503538021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1815520726153110004717361 1361640544614832503538021)
                ·
                  refine ⟨255307602115281094413379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1361640544614832503538021 255307602115281094413379)
                  ·
                    rfl

theorem cell20_559361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_559361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559361 prefixEnd_559361 := by exact prefixLift 559361
  have htrace : WordTrace (prefixWord ++ tailWord_559361) baseStart_559361 baseEnd_559361 := by
    simpa [prefixWord, tailWord_559361, baseEnd_559361] using wordTrace_append hprefix tailTrace_559361
  have hstable : (prefixWord ++ tailWord_559361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559361).length < 2 ^ (prefixWord ++ tailWord_559361).sum := by decide
  have hdescent : baseEnd_559361 < baseStart_559361 := by decide
  rcases family_descends (prefixWord ++ tailWord_559361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559364 : List Nat := [2, 3, 2, 2, 3, 1, 3, 4]
def baseStart_559364 : Nat := 118140960795 + 559364 * 2 ^ 59
def prefixEnd_559364 : Nat := 4983230072969 + 3 ^ 40 * 559364 * 2
def baseEnd_559364 : Nat := 85102990465675472437789

theorem tailTrace_559364 : CollatzResearch.WordTrace tailWord_559364 prefixEnd_559364 85102990465675472437789 := by
  unfold tailWord_559364
  simp only [CollatzResearch.WordTrace]
  refine ⟨10200840572763617305318573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13601120763684823073758097 10200840572763617305318573)
  ·
    refine ⟨3825315214786356489494465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10200840572763617305318573 3825315214786356489494465)
    ·
      refine ⟨2868986411089767367120849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3825315214786356489494465 2868986411089767367120849)
      ·
        refine ⟨2151739808317325525340637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2868986411089767367120849 2151739808317325525340637)
        ·
          refine ⟨806902428118997072002739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2151739808317325525340637 806902428118997072002739)
          ·
            refine ⟨1210353642178495608004109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806902428118997072002739 1210353642178495608004109)
            ·
              refine ⟨453882615816935853001541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1210353642178495608004109 453882615816935853001541)
              ·
                refine ⟨85102990465675472437789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 453882615816935853001541 85102990465675472437789)
                ·
                  rfl

theorem cell20_559364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_559364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559364 prefixEnd_559364 := by exact prefixLift 559364
  have htrace : WordTrace (prefixWord ++ tailWord_559364) baseStart_559364 baseEnd_559364 := by
    simpa [prefixWord, tailWord_559364, baseEnd_559364] using wordTrace_append hprefix tailTrace_559364
  have hstable : (prefixWord ++ tailWord_559364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559364).length < 2 ^ (prefixWord ++ tailWord_559364).sum := by decide
  have hdescent : baseEnd_559364 < baseStart_559364 := by decide
  rcases family_descends (prefixWord ++ tailWord_559364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559392 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 5]
def baseStart_559392 : Nat := 118140960795 + 559392 * 2 ^ 59
def prefixEnd_559392 : Nat := 4983230072969 + 3 ^ 40 * 559392 * 2
def baseEnd_559392 : Nat := 255321751359982764379919

theorem tailTrace_559392 : CollatzResearch.WordTrace tailWord_559392 prefixEnd_559392 255321751359982764379919 := by
  unfold tailWord_559392
  simp only [CollatzResearch.WordTrace]
  refine ⟨10201351194712897696328215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13601801592950530261770953 10201351194712897696328215)
  ·
    refine ⟨15302026792069346544492323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10201351194712897696328215 15302026792069346544492323)
    ·
      refine ⟨22953040188104019816738485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15302026792069346544492323 22953040188104019816738485)
      ·
        refine ⟨2151847517634751857819233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22953040188104019816738485 2151847517634751857819233)
        ·
          refine ⟨1613885638226063893364425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2151847517634751857819233 1613885638226063893364425)
          ·
            refine ⟨1210414228669547920023319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1613885638226063893364425 1210414228669547920023319)
            ·
              refine ⟨1815621343004321880034979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1210414228669547920023319 1815621343004321880034979)
              ·
                refine ⟨2723432014506482820052469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1815621343004321880034979 2723432014506482820052469)
                ·
                  refine ⟨255321751359982764379919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2723432014506482820052469 255321751359982764379919)
                  ·
                    rfl

theorem cell20_559392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_559392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559392 prefixEnd_559392 := by exact prefixLift 559392
  have htrace : WordTrace (prefixWord ++ tailWord_559392) baseStart_559392 baseEnd_559392 := by
    simpa [prefixWord, tailWord_559392, baseEnd_559392] using wordTrace_append hprefix tailTrace_559392
  have hstable : (prefixWord ++ tailWord_559392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559392).length < 2 ^ (prefixWord ++ tailWord_559392).sum := by decide
  have hdescent : baseEnd_559392 < baseStart_559392 := by decide
  rcases family_descends (prefixWord ++ tailWord_559392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559405 : List Nat := [1, 5, 3, 1, 2, 1, 3, 1, 3]
def baseStart_559405 : Nat := 118140960795 + 559405 * 2 ^ 59
def prefixEnd_559405 : Nat := 4983230072969 + 3 ^ 40 * 559405 * 2
def baseEnd_559405 : Nat := 255327684914212496946533

theorem tailTrace_559405 : CollatzResearch.WordTrace tailWord_559405 prefixEnd_559405 255327684914212496946533 := by
  unfold tailWord_559405
  simp only [CollatzResearch.WordTrace]
  refine ⟨20403176538378698612879669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13602117692252465741919779 20403176538378698612879669)
  ·
    refine ⟨1912797800473002994957469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20403176538378698612879669 1912797800473002994957469)
    ·
      refine ⟨717299175177376123109051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1912797800473002994957469 717299175177376123109051)
      ·
        refine ⟨1075948762766064184663577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 717299175177376123109051 1075948762766064184663577)
        ·
          refine ⟨806961572074548138497683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1075948762766064184663577 806961572074548138497683)
          ·
            refine ⟨1210442358111822207746525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806961572074548138497683 1210442358111822207746525)
            ·
              refine ⟨453915884291933327904947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1210442358111822207746525 453915884291933327904947)
              ·
                refine ⟨680873826437899991857421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453915884291933327904947 680873826437899991857421)
                ·
                  refine ⟨255327684914212496946533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680873826437899991857421 255327684914212496946533)
                  ·
                    rfl

theorem cell20_559405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_559405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559405 prefixEnd_559405 := by exact prefixLift 559405
  have htrace : WordTrace (prefixWord ++ tailWord_559405) baseStart_559405 baseEnd_559405 := by
    simpa [prefixWord, tailWord_559405, baseEnd_559405] using wordTrace_append hprefix tailTrace_559405
  have hstable : (prefixWord ++ tailWord_559405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559405).length < 2 ^ (prefixWord ++ tailWord_559405).sum := by decide
  have hdescent : baseEnd_559405 < baseStart_559405 := by decide
  rcases family_descends (prefixWord ++ tailWord_559405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559444 : List Nat := [2, 4, 1, 1, 2, 2, 8]
def baseStart_559444 : Nat := 118140960795 + 559444 * 2 ^ 59
def prefixEnd_559444 : Nat := 4983230072969 + 3 ^ 40 * 559444 * 2
def baseEnd_559444 : Nat := 28371720619655743849597

theorem tailTrace_559444 : CollatzResearch.WordTrace tailWord_559444 prefixEnd_559444 28371720619655743849597 := by
  unfold tailWord_559444
  simp only [CollatzResearch.WordTrace]
  refine ⟨10202299492618704136774693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13603065990158272182366257 10202299492618704136774693)
  ·
    refine ⟨1912931154866007025645255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10202299492618704136774693 1912931154866007025645255)
    ·
      refine ⟨2869396732299010538467883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1912931154866007025645255 2869396732299010538467883)
      ·
        refine ⟨4304095098448515807701825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2869396732299010538467883 4304095098448515807701825)
        ·
          refine ⟨3228071323836386855776369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4304095098448515807701825 3228071323836386855776369)
          ·
            refine ⟨2421053492877290141832277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3228071323836386855776369 2421053492877290141832277)
            ·
              refine ⟨28371720619655743849597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2421053492877290141832277 28371720619655743849597)
              ·
                rfl

theorem cell20_559444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 8].length) (baseStart_559444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559444 prefixEnd_559444 := by exact prefixLift 559444
  have htrace : WordTrace (prefixWord ++ tailWord_559444) baseStart_559444 baseEnd_559444 := by
    simpa [prefixWord, tailWord_559444, baseEnd_559444] using wordTrace_append hprefix tailTrace_559444
  have hstable : (prefixWord ++ tailWord_559444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559444).length < 2 ^ (prefixWord ++ tailWord_559444).sum := by decide
  have hdescent : baseEnd_559444 < baseStart_559444 := by decide
  rcases family_descends (prefixWord ++ tailWord_559444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559464 : List Nat := [2, 1, 4, 2, 2, 3, 2, 1, 3]
def baseStart_559464 : Nat := 118140960795 + 559464 * 2 ^ 59
def prefixEnd_559464 : Nat := 4983230072969 + 3 ^ 40 * 559464 * 2
def baseEnd_559464 : Nat := 255354614121870513979625

theorem tailTrace_559464 : CollatzResearch.WordTrace tailWord_559464 prefixEnd_559464 255354614121870513979625 := by
  unfold tailWord_559464
  simp only [CollatzResearch.WordTrace]
  refine ⟨10202664222582475844638723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13603552296776634459518297 10202664222582475844638723)
  ·
    refine ⟨15303996333873713766958085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10202664222582475844638723 15303996333873713766958085)
    ·
      refine ⟨2869499312601321331304641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15303996333873713766958085 2869499312601321331304641)
      ·
        refine ⟨2152124484450990998478481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2869499312601321331304641 2152124484450990998478481)
        ·
          refine ⟨1614093363338243248858861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2152124484450990998478481 1614093363338243248858861)
          ·
            refine ⟨605285011251841218322073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1614093363338243248858861 605285011251841218322073)
            ·
              refine ⟨453963758438880913741555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 605285011251841218322073 453963758438880913741555)
              ·
                refine ⟨680945637658321370612333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453963758438880913741555 680945637658321370612333)
                ·
                  refine ⟨255354614121870513979625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680945637658321370612333 255354614121870513979625)
                  ·
                    rfl

theorem cell20_559464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_559464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559464 prefixEnd_559464 := by exact prefixLift 559464
  have htrace : WordTrace (prefixWord ++ tailWord_559464) baseStart_559464 baseEnd_559464 := by
    simpa [prefixWord, tailWord_559464, baseEnd_559464] using wordTrace_append hprefix tailTrace_559464
  have hstable : (prefixWord ++ tailWord_559464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559464).length < 2 ^ (prefixWord ++ tailWord_559464).sum := by decide
  have hdescent : baseEnd_559464 < baseStart_559464 := by decide
  rcases family_descends (prefixWord ++ tailWord_559464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559492 : List Nat := [2, 3, 2, 1, 1, 2, 2, 5, 2]
def baseStart_559492 : Nat := 118140960795 + 559492 * 2 ^ 59
def prefixEnd_559492 : Nat := 4983230072969 + 3 ^ 40 * 559492 * 2
def baseEnd_559492 : Nat := 255367394084826861046177

theorem tailTrace_559492 : CollatzResearch.WordTrace tailWord_559492 prefixEnd_559492 255367394084826861046177 := by
  unfold tailWord_559492
  simp only [CollatzResearch.WordTrace]
  refine ⟨10203174844531756235648365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13604233126042341647531153 10203174844531756235648365)
  ·
    refine ⟨3826190566699408588368137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10203174844531756235648365 3826190566699408588368137)
    ·
      refine ⟨2869642925024556441276103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3826190566699408588368137 2869642925024556441276103)
      ·
        refine ⟨4304464387536834661914155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2869642925024556441276103 4304464387536834661914155)
        ·
          refine ⟨6456696581305251992871233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4304464387536834661914155 6456696581305251992871233)
          ·
            refine ⟨4842522435978938994653425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6456696581305251992871233 4842522435978938994653425)
            ·
              refine ⟨3631891826984204245990069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4842522435978938994653425 3631891826984204245990069)
              ·
                refine ⟨340489858779769148061569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3631891826984204245990069 340489858779769148061569)
                ·
                  refine ⟨255367394084826861046177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340489858779769148061569 255367394084826861046177)
                  ·
                    rfl

theorem cell20_559492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_559492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559492 prefixEnd_559492 := by exact prefixLift 559492
  have htrace : WordTrace (prefixWord ++ tailWord_559492) baseStart_559492 baseEnd_559492 := by
    simpa [prefixWord, tailWord_559492, baseEnd_559492] using wordTrace_append hprefix tailTrace_559492
  have hstable : (prefixWord ++ tailWord_559492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559492).length < 2 ^ (prefixWord ++ tailWord_559492).sum := by decide
  have hdescent : baseEnd_559492 < baseStart_559492 := by decide
  rcases family_descends (prefixWord ++ tailWord_559492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559520 : List Nat := [2, 1, 1, 4, 1, 3, 3, 5]
def baseStart_559520 : Nat := 118140960795 + 559520 * 2 ^ 59
def prefixEnd_559520 : Nat := 4983230072969 + 3 ^ 40 * 559520 * 2
def baseEnd_559520 : Nat := 85126724682594402704243

theorem tailTrace_559520 : CollatzResearch.WordTrace tailWord_559520 prefixEnd_559520 85126724682594402704243 := by
  unfold tailWord_559520
  simp only [CollatzResearch.WordTrace]
  refine ⟨10203685466481036626658007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13604913955308048835544009 10203685466481036626658007)
  ·
    refine ⟨15305528199721554939987011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10203685466481036626658007 15305528199721554939987011)
    ·
      refine ⟨22958292299582332409980517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15305528199721554939987011 22958292299582332409980517)
      ·
        refine ⟨4304679806171687326871347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22958292299582332409980517 4304679806171687326871347)
        ·
          refine ⟨6457019709257530990307021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4304679806171687326871347 6457019709257530990307021)
          ·
            refine ⟨2421382390971574121365133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6457019709257530990307021 2421382390971574121365133)
            ·
              refine ⟨908018396614340295511925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2421382390971574121365133 908018396614340295511925)
              ·
                refine ⟨85126724682594402704243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 908018396614340295511925 85126724682594402704243)
                ·
                  rfl

theorem cell20_559520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_559520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559520 prefixEnd_559520 := by exact prefixLift 559520
  have htrace : WordTrace (prefixWord ++ tailWord_559520) baseStart_559520 baseEnd_559520 := by
    simpa [prefixWord, tailWord_559520, baseEnd_559520] using wordTrace_append hprefix tailTrace_559520
  have hstable : (prefixWord ++ tailWord_559520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559520).length < 2 ^ (prefixWord ++ tailWord_559520).sum := by decide
  have hdescent : baseEnd_559520 < baseStart_559520 := by decide
  rcases family_descends (prefixWord ++ tailWord_559520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559537 : List Nat := [1, 2, 2, 4, 1, 3, 3, 4]
def baseStart_559537 : Nat := 118140960795 + 559537 * 2 ^ 59
def prefixEnd_559537 : Nat := 4983230072969 + 3 ^ 40 * 559537 * 2
def baseEnd_559537 : Nat := 85129311103668901515331

theorem tailTrace_559537 : CollatzResearch.WordTrace tailWord_559537 prefixEnd_559537 85129311103668901515331 := by
  unfold tailWord_559537
  simp only [CollatzResearch.WordTrace]
  refine ⟨20407990973900485156684865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13605327315933656771123243 20407990973900485156684865)
  ·
    refine ⟨15305993230425363867513649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20407990973900485156684865 15305993230425363867513649)
    ·
      refine ⟨11479494922819022900635237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15305993230425363867513649 11479494922819022900635237)
      ·
        refine ⟨2152405298028566793869107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11479494922819022900635237 2152405298028566793869107)
        ·
          refine ⟨3228607947042850190803661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2152405298028566793869107 3228607947042850190803661)
          ·
            refine ⟨1210727980141068821551373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3228607947042850190803661 1210727980141068821551373)
            ·
              refine ⟨454022992552900808081765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1210727980141068821551373 454022992552900808081765)
              ·
                refine ⟨85129311103668901515331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 454022992552900808081765 85129311103668901515331)
                ·
                  rfl

theorem cell20_559537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 4].length) (baseStart_559537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559537 prefixEnd_559537 := by exact prefixLift 559537
  have htrace : WordTrace (prefixWord ++ tailWord_559537) baseStart_559537 baseEnd_559537 := by
    simpa [prefixWord, tailWord_559537, baseEnd_559537] using wordTrace_append hprefix tailTrace_559537
  have hstable : (prefixWord ++ tailWord_559537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559537).length < 2 ^ (prefixWord ++ tailWord_559537).sum := by decide
  have hdescent : baseEnd_559537 < baseStart_559537 := by decide
  rcases family_descends (prefixWord ++ tailWord_559537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559602 : List Nat := [3, 2, 1, 4, 2, 2, 1, 3, 2]
def baseStart_559602 : Nat := 118140960795 + 559602 * 2 ^ 59
def prefixEnd_559602 : Nat := 4983230072969 + 3 ^ 40 * 559602 * 2
def baseEnd_559602 : Nat := 255417601082155367379061

theorem tailTrace_559602 : CollatzResearch.WordTrace tailWord_559602 prefixEnd_559602 255417601082155367379061 := by
  unfold tailWord_559602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5102590429666250314450265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13606907812443334171867373 5102590429666250314450265)
  ·
    refine ⟨3826942822249687735837699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5102590429666250314450265 3826942822249687735837699)
    ·
      refine ⟨5740414233374531603756549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3826942822249687735837699 5740414233374531603756549)
      ·
        refine ⟨1076327668757724675704353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5740414233374531603756549 1076327668757724675704353)
        ·
          refine ⟨807245751568293506778265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1076327668757724675704353 807245751568293506778265)
          ·
            refine ⟨605434313676220130083699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 807245751568293506778265 605434313676220130083699)
            ·
              refine ⟨908151470514330195125549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 605434313676220130083699 908151470514330195125549)
              ·
                refine ⟨340556801442873823172081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 908151470514330195125549 340556801442873823172081)
                ·
                  refine ⟨255417601082155367379061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340556801442873823172081 255417601082155367379061)
                  ·
                    rfl

theorem cell20_559602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_559602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559602 prefixEnd_559602 := by exact prefixLift 559602
  have htrace : WordTrace (prefixWord ++ tailWord_559602) baseStart_559602 baseEnd_559602 := by
    simpa [prefixWord, tailWord_559602, baseEnd_559602] using wordTrace_append hprefix tailTrace_559602
  have hstable : (prefixWord ++ tailWord_559602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559602).length < 2 ^ (prefixWord ++ tailWord_559602).sum := by decide
  have hdescent : baseEnd_559602 < baseStart_559602 := by decide
  rcases family_descends (prefixWord ++ tailWord_559602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559620 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 5]
def baseStart_559620 : Nat := 118140960795 + 559620 * 2 ^ 59
def prefixEnd_559620 : Nat := 4983230072969 + 3 ^ 40 * 559620 * 2
def baseEnd_559620 : Nat := 255425816772627304778987

theorem tailTrace_559620 : CollatzResearch.WordTrace tailWord_559620 prefixEnd_559620 255425816772627304778987 := by
  unfold tailWord_559620
  simp only [CollatzResearch.WordTrace]
  refine ⟨10205509116299895165978157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13607345488399860221304209 10205509116299895165978157)
  ·
    refine ⟨3827065918612460687241809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10205509116299895165978157 3827065918612460687241809)
    ·
      refine ⟨2870299438959345515431357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3827065918612460687241809 2870299438959345515431357)
      ·
        refine ⟨1076362289609754568286759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2870299438959345515431357 1076362289609754568286759)
        ·
          refine ⟨1614543434414631852430139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1076362289609754568286759 1614543434414631852430139)
          ·
            refine ⟨2421815151621947778645209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1614543434414631852430139 2421815151621947778645209)
            ·
              refine ⟨1816361363716460833983907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2421815151621947778645209 1816361363716460833983907)
              ·
                refine ⟨2724542045574691250975861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1816361363716460833983907 2724542045574691250975861)
                ·
                  refine ⟨255425816772627304778987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2724542045574691250975861 255425816772627304778987)
                  ·
                    rfl

theorem cell20_559620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_559620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559620 prefixEnd_559620 := by exact prefixLift 559620
  have htrace : WordTrace (prefixWord ++ tailWord_559620) baseStart_559620 baseEnd_559620 := by
    simpa [prefixWord, tailWord_559620, baseEnd_559620] using wordTrace_append hprefix tailTrace_559620
  have hstable : (prefixWord ++ tailWord_559620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559620).length < 2 ^ (prefixWord ++ tailWord_559620).sum := by decide
  have hdescent : baseEnd_559620 < baseStart_559620 := by decide
  rcases family_descends (prefixWord ++ tailWord_559620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559623 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 4]
def baseStart_559623 : Nat := 118140960795 + 559623 * 2 ^ 59
def prefixEnd_559623 : Nat := 4983230072969 + 3 ^ 40 * 559623 * 2
def baseEnd_559623 : Nat := 255427186054372627678975

theorem tailTrace_559623 : CollatzResearch.WordTrace tailWord_559623 prefixEnd_559623 255427186054372627678975 := by
  unfold tailWord_559623
  simp only [CollatzResearch.WordTrace]
  refine ⟨20411127651588921844315523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13607418434392614562877015 20411127651588921844315523)
  ·
    refine ⟨30616691477383382766473285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20411127651588921844315523 30616691477383382766473285)
    ·
      refine ⟨5740629652009384268713741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30616691477383382766473285 5740629652009384268713741)
      ·
        refine ⟨2152736119503519100767653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5740629652009384268713741 2152736119503519100767653)
        ·
          refine ⟨403638022406909831393935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2152736119503519100767653 403638022406909831393935)
          ·
            refine ⟨605457033610364747090903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403638022406909831393935 605457033610364747090903)
            ·
              refine ⟨908185550415547120636355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 605457033610364747090903 908185550415547120636355)
              ·
                refine ⟨1362278325623320680954533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 908185550415547120636355 1362278325623320680954533)
                ·
                  refine ⟨255427186054372627678975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1362278325623320680954533 255427186054372627678975)
                  ·
                    rfl

theorem cell20_559623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 4].length) (baseStart_559623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559623 prefixEnd_559623 := by exact prefixLift 559623
  have htrace : WordTrace (prefixWord ++ tailWord_559623) baseStart_559623 baseEnd_559623 := by
    simpa [prefixWord, tailWord_559623, baseEnd_559623] using wordTrace_append hprefix tailTrace_559623
  have hstable : (prefixWord ++ tailWord_559623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559623).length < 2 ^ (prefixWord ++ tailWord_559623).sum := by decide
  have hdescent : baseEnd_559623 < baseStart_559623 := by decide
  rcases family_descends (prefixWord ++ tailWord_559623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559627 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 4]
def baseStart_559627 : Nat := 118140960795 + 559627 * 2 ^ 59
def prefixEnd_559627 : Nat := 4983230072969 + 3 ^ 40 * 559627 * 2
def baseEnd_559627 : Nat := 255429011763366391545625

theorem tailTrace_559627 : CollatzResearch.WordTrace tailWord_559627 prefixEnd_559627 255429011763366391545625 := by
  unfold tailWord_559627
  simp only [CollatzResearch.WordTrace]
  refine ⟨20411273543574430527461135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13607515695716287018307423 20411273543574430527461135)
  ·
    refine ⟨30616910315361645791191703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20411273543574430527461135 30616910315361645791191703)
    ·
      refine ⟨45925365473042468686787555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30616910315361645791191703 45925365473042468686787555)
      ·
        refine ⟨68888048209563703030181333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45925365473042468686787555 68888048209563703030181333)
        ·
          refine ⟨1614563629911649289769875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 68888048209563703030181333 1614563629911649289769875)
          ·
            refine ⟨2421845444867473934654813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1614563629911649289769875 2421845444867473934654813)
            ·
              refine ⟨908192041825302725495555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2421845444867473934654813 908192041825302725495555)
              ·
                refine ⟨1362288062737954088243333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 908192041825302725495555 1362288062737954088243333)
                ·
                  refine ⟨255429011763366391545625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1362288062737954088243333 255429011763366391545625)
                  ·
                    rfl

theorem cell20_559627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 4].length) (baseStart_559627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559627 prefixEnd_559627 := by exact prefixLift 559627
  have htrace : WordTrace (prefixWord ++ tailWord_559627) baseStart_559627 baseEnd_559627 := by
    simpa [prefixWord, tailWord_559627, baseEnd_559627] using wordTrace_append hprefix tailTrace_559627
  have hstable : (prefixWord ++ tailWord_559627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559627).length < 2 ^ (prefixWord ++ tailWord_559627).sum := by decide
  have hdescent : baseEnd_559627 < baseStart_559627 := by decide
  rcases family_descends (prefixWord ++ tailWord_559627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559641 : List Nat := [1, 2, 1, 2, 1, 1, 2, 7, 3]
def baseStart_559641 : Nat := 118140960795 + 559641 * 2 ^ 59
def prefixEnd_559641 : Nat := 4983230072969 + 3 ^ 40 * 559641 * 2
def baseEnd_559641 : Nat := 255435401744844565078901

theorem tailTrace_559641 : CollatzResearch.WordTrace tailWord_559641 prefixEnd_559641 255435401744844565078901 := by
  unfold tailWord_559641
  simp only [CollatzResearch.WordTrace]
  refine ⟨20411784165523710918470777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13607856110349140612313851 20411784165523710918470777)
  ·
    refine ⟨15308838124142783188853083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20411784165523710918470777 15308838124142783188853083)
    ·
      refine ⟨22963257186214174783279625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15308838124142783188853083 22963257186214174783279625)
      ·
        refine ⟨17222442889660631087459719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22963257186214174783279625 17222442889660631087459719)
        ·
          refine ⟨25833664334490946631189579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17222442889660631087459719 25833664334490946631189579)
          ·
            refine ⟨38750496501736419946784369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25833664334490946631189579 38750496501736419946784369)
            ·
              refine ⟨29062872376302314960088277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38750496501736419946784369 29062872376302314960088277)
              ·
                refine ⟨681161071319585506877069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29062872376302314960088277 681161071319585506877069)
                ·
                  refine ⟨255435401744844565078901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681161071319585506877069 255435401744844565078901)
                  ·
                    rfl

theorem cell20_559641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_559641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559641 prefixEnd_559641 := by exact prefixLift 559641
  have htrace : WordTrace (prefixWord ++ tailWord_559641) baseStart_559641 baseEnd_559641 := by
    simpa [prefixWord, tailWord_559641, baseEnd_559641] using wordTrace_append hprefix tailTrace_559641
  have hstable : (prefixWord ++ tailWord_559641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559641).length < 2 ^ (prefixWord ++ tailWord_559641).sum := by decide
  have hdescent : baseEnd_559641 < baseStart_559641 := by decide
  rcases family_descends (prefixWord ++ tailWord_559641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559668 : List Nat := [2, 5, 1, 3, 2, 7]
def baseStart_559668 : Nat := 118140960795 + 559668 * 2 ^ 59
def prefixEnd_559668 : Nat := 4983230072969 + 3 ^ 40 * 559668 * 2
def baseEnd_559668 : Nat := 9461026862242684117733

theorem tailTrace_559668 : CollatzResearch.WordTrace tailWord_559668 prefixEnd_559668 9461026862242684117733 := by
  unfold tailWord_559668
  simp only [CollatzResearch.WordTrace]
  refine ⟨10206384468212947264851829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13608512624283929686469105 10206384468212947264851829)
  ·
    refine ⟨956848543894963806079859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10206384468212947264851829 956848543894963806079859)
    ·
      refine ⟨1435272815842445709119789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 956848543894963806079859 1435272815842445709119789)
      ·
        refine ⟨538227305940917140919921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1435272815842445709119789 538227305940917140919921)
        ·
          refine ⟨403670479455687855689941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 538227305940917140919921 403670479455687855689941)
          ·
            refine ⟨9461026862242684117733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 403670479455687855689941 9461026862242684117733)
            ·
              rfl

theorem cell20_559668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 7].length) (baseStart_559668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559668 prefixEnd_559668 := by exact prefixLift 559668
  have htrace : WordTrace (prefixWord ++ tailWord_559668) baseStart_559668 baseEnd_559668 := by
    simpa [prefixWord, tailWord_559668, baseEnd_559668] using wordTrace_append hprefix tailTrace_559668
  have hstable : (prefixWord ++ tailWord_559668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559668).length < 2 ^ (prefixWord ++ tailWord_559668).sum := by decide
  have hdescent : baseEnd_559668 < baseStart_559668 := by decide
  rcases family_descends (prefixWord ++ tailWord_559668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559678 : List Nat := [4, 2, 1, 4, 1, 1, 1, 4, 2]
def baseStart_559678 : Nat := 118140960795 + 559678 * 2 ^ 59
def prefixEnd_559678 : Nat := 4983230072969 + 3 ^ 40 * 559678 * 2
def baseEnd_559678 : Nat := 255452289553036880845417

theorem tailTrace_559678 : CollatzResearch.WordTrace tailWord_559678 prefixEnd_559678 255452289553036880845417 := by
  unfold tailWord_559678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2551641708298708279695961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13608755777593110825045125 2551641708298708279695961)
  ·
    refine ⟨1913731281224031209771971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2551641708298708279695961 1913731281224031209771971)
    ·
      refine ⟨2870596921836046814657957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1913731281224031209771971 2870596921836046814657957)
      ·
        refine ⟨538236922844258777748367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2870596921836046814657957 538236922844258777748367)
        ·
          refine ⟨807355384266388166622551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 538236922844258777748367 807355384266388166622551)
          ·
            refine ⟨1211033076399582249933827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807355384266388166622551 1211033076399582249933827)
            ·
              refine ⟨1816549614599373374900741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211033076399582249933827 1816549614599373374900741)
              ·
                refine ⟨340603052737382507793889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1816549614599373374900741 340603052737382507793889)
                ·
                  refine ⟨255452289553036880845417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340603052737382507793889 255452289553036880845417)
                  ·
                    rfl

theorem cell20_559678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_559678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559678 prefixEnd_559678 := by exact prefixLift 559678
  have htrace : WordTrace (prefixWord ++ tailWord_559678) baseStart_559678 baseEnd_559678 := by
    simpa [prefixWord, tailWord_559678, baseEnd_559678] using wordTrace_append hprefix tailTrace_559678
  have hstable : (prefixWord ++ tailWord_559678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559678).length < 2 ^ (prefixWord ++ tailWord_559678).sum := by decide
  have hdescent : baseEnd_559678 < baseStart_559678 := by decide
  rcases family_descends (prefixWord ++ tailWord_559678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559730 : List Nat := [3, 2, 1, 2, 5, 1, 1, 2, 3]
def baseStart_559730 : Nat := 118140960795 + 559730 * 2 ^ 59
def prefixEnd_559730 : Nat := 4983230072969 + 3 ^ 40 * 559730 * 2
def baseEnd_559730 : Nat := 255476023769955811111871

theorem tailTrace_559730 : CollatzResearch.WordTrace tailWord_559730 prefixEnd_559730 255476023769955811111871 := by
  unfold tailWord_559730
  simp only [CollatzResearch.WordTrace]
  refine ⟨5103757565550319779615161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13610020174800852745640429 5103757565550319779615161)
  ·
    refine ⟨3827818174162739834711371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5103757565550319779615161 3827818174162739834711371)
    ·
      refine ⟨5741727261244109752067057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3827818174162739834711371 5741727261244109752067057)
      ·
        refine ⟨4306295445933082314050293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5741727261244109752067057 4306295445933082314050293)
        ·
          refine ⟨403715198056226466942215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4306295445933082314050293 403715198056226466942215)
          ·
            refine ⟨605572797084339700413323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403715198056226466942215 605572797084339700413323)
            ·
              refine ⟨908359195626509550619985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 605572797084339700413323 908359195626509550619985)
              ·
                refine ⟨681269396719882162964989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 908359195626509550619985 681269396719882162964989)
                ·
                  refine ⟨255476023769955811111871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681269396719882162964989 255476023769955811111871)
                  ·
                    rfl

theorem cell20_559730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_559730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559730 prefixEnd_559730 := by exact prefixLift 559730
  have htrace : WordTrace (prefixWord ++ tailWord_559730) baseStart_559730 baseEnd_559730 := by
    simpa [prefixWord, tailWord_559730, baseEnd_559730] using wordTrace_append hprefix tailTrace_559730
  have hstable : (prefixWord ++ tailWord_559730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559730).length < 2 ^ (prefixWord ++ tailWord_559730).sum := by decide
  have hdescent : baseEnd_559730 < baseStart_559730 := by decide
  rcases family_descends (prefixWord ++ tailWord_559730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559769 : List Nat := [1, 2, 1, 2, 1, 2, 5, 6]
def baseStart_559769 : Nat := 118140960795 + 559769 * 2 ^ 59
def prefixEnd_559769 : Nat := 4983230072969 + 3 ^ 40 * 559769 * 2
def baseEnd_559769 : Nat := 85164608144215002937237

theorem tailTrace_559769 : CollatzResearch.WordTrace tailWord_559769 prefixEnd_559769 85164608144215002937237 := by
  unfold tailWord_559769
  simp only [CollatzResearch.WordTrace]
  refine ⟨20416452709059988779130361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13610968472706659186086907 20416452709059988779130361)
  ·
    refine ⟨15312339531794991584347771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20416452709059988779130361 15312339531794991584347771)
    ·
      refine ⟨22968509297692487376521657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15312339531794991584347771 22968509297692487376521657)
      ·
        refine ⟨17226381973269365532391243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22968509297692487376521657 17226381973269365532391243)
        ·
          refine ⟨25839572959904048298586865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17226381973269365532391243 25839572959904048298586865)
          ·
            refine ⟨19379679719928036223940149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25839572959904048298586865 19379679719928036223940149)
            ·
              refine ⟨1816844973743253395994389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19379679719928036223940149 1816844973743253395994389)
              ·
                refine ⟨85164608144215002937237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1816844973743253395994389 85164608144215002937237)
                ·
                  rfl

theorem cell20_559769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 6].length) (baseStart_559769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559769 prefixEnd_559769 := by exact prefixLift 559769
  have htrace : WordTrace (prefixWord ++ tailWord_559769) baseStart_559769 baseEnd_559769 := by
    simpa [prefixWord, tailWord_559769, baseEnd_559769] using wordTrace_append hprefix tailTrace_559769
  have hstable : (prefixWord ++ tailWord_559769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559769).length < 2 ^ (prefixWord ++ tailWord_559769).sum := by decide
  have hdescent : baseEnd_559769 < baseStart_559769 := by decide
  rcases family_descends (prefixWord ++ tailWord_559769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559779 : List Nat := [1, 1, 1, 4, 1, 1, 2, 7, 2]
def baseStart_559779 : Nat := 118140960795 + 559779 * 2 ^ 59
def prefixEnd_559779 : Nat := 4983230072969 + 3 ^ 40 * 559779 * 2
def baseEnd_559779 : Nat := 255498388705129418478337

theorem tailTrace_559779 : CollatzResearch.WordTrace tailWord_559779 prefixEnd_559779 255498388705129418478337 := by
  unfold tailWord_559779
  simp only [CollatzResearch.WordTrace]
  refine ⟨20416817439023760486994391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13611211626015840324662927 20416817439023760486994391)
  ·
    refine ⟨30625226158535640730491587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20416817439023760486994391 30625226158535640730491587)
    ·
      refine ⟨45937839237803461095737381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30625226158535640730491587 45937839237803461095737381)
      ·
        refine ⟨8613344857088148955450759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45937839237803461095737381 8613344857088148955450759)
        ·
          refine ⟨12920017285632223433176139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8613344857088148955450759 12920017285632223433176139)
          ·
            refine ⟨19380025928448335149764209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12920017285632223433176139 19380025928448335149764209)
            ·
              refine ⟨14535019446336251362323157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19380025928448335149764209 14535019446336251362323157)
              ·
                refine ⟨340664518273505891304449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14535019446336251362323157 340664518273505891304449)
                ·
                  refine ⟨255498388705129418478337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340664518273505891304449 255498388705129418478337)
                  ·
                    rfl

theorem cell20_559779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 2].length) (baseStart_559779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559779 prefixEnd_559779 := by exact prefixLift 559779
  have htrace : WordTrace (prefixWord ++ tailWord_559779) baseStart_559779 baseEnd_559779 := by
    simpa [prefixWord, tailWord_559779, baseEnd_559779] using wordTrace_append hprefix tailTrace_559779
  have hstable : (prefixWord ++ tailWord_559779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559779).length < 2 ^ (prefixWord ++ tailWord_559779).sum := by decide
  have hdescent : baseEnd_559779 < baseStart_559779 := by decide
  rcases family_descends (prefixWord ++ tailWord_559779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559807 : List Nat := [1, 1, 2, 2, 2, 4, 1, 7]
def baseStart_559807 : Nat := 118140960795 + 559807 * 2 ^ 59
def prefixEnd_559807 : Nat := 4983230072969 + 3 ^ 40 * 559807 * 2
def baseEnd_559807 : Nat := 85170389556028588514963

theorem tailTrace_559807 : CollatzResearch.WordTrace tailWord_559807 prefixEnd_559807 85170389556028588514963 := by
  unfold tailWord_559807
  simp only [CollatzResearch.WordTrace]
  refine ⟨20417838682922321269013675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13611892455281547512675783 20417838682922321269013675)
  ·
    refine ⟨30626758024383481903520513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20417838682922321269013675 30626758024383481903520513)
    ·
      refine ⟨22970068518287611427640385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30626758024383481903520513 22970068518287611427640385)
      ·
        refine ⟨17227551388715708570730289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22970068518287611427640385 17227551388715708570730289)
        ·
          refine ⟨12920663541536781428047717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17227551388715708570730289 12920663541536781428047717)
          ·
            refine ⟨2422624414038146517758947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12920663541536781428047717 2422624414038146517758947)
            ·
              refine ⟨3633936621057219776638421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2422624414038146517758947 3633936621057219776638421)
              ·
                refine ⟨85170389556028588514963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3633936621057219776638421 85170389556028588514963)
                ·
                  rfl

theorem cell20_559807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 7].length) (baseStart_559807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559807 prefixEnd_559807 := by exact prefixLift 559807
  have htrace : WordTrace (prefixWord ++ tailWord_559807) baseStart_559807 baseEnd_559807 := by
    simpa [prefixWord, tailWord_559807, baseEnd_559807] using wordTrace_append hprefix tailTrace_559807
  have hstable : (prefixWord ++ tailWord_559807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559807).length < 2 ^ (prefixWord ++ tailWord_559807).sum := by decide
  have hdescent : baseEnd_559807 < baseStart_559807 := by decide
  rcases family_descends (prefixWord ++ tailWord_559807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559845 : List Nat := [1, 3, 1, 4, 1, 10]
def baseStart_559845 : Nat := 118140960795 + 559845 * 2 ^ 59
def prefixEnd_559845 : Nat := 4983230072969 + 3 ^ 40 * 559845 * 2
def baseEnd_559845 : Nat := 9464018996426908232521

theorem tailTrace_559845 : CollatzResearch.WordTrace tailWord_559845 prefixEnd_559845 9464018996426908232521 := by
  unfold tailWord_559845
  simp only [CollatzResearch.WordTrace]
  refine ⟨20419224656784653758896989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13612816437856435839264659 20419224656784653758896989)
  ·
    refine ⟨7657209246294245159586371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20419224656784653758896989 7657209246294245159586371)
    ·
      refine ⟨11485813869441367739379557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7657209246294245159586371 11485813869441367739379557)
      ·
        refine ⟨2153590100520256451133667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11485813869441367739379557 2153590100520256451133667)
        ·
          refine ⟨3230385150780384676700501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2153590100520256451133667 3230385150780384676700501)
          ·
            refine ⟨9464018996426908232521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3230385150780384676700501 9464018996426908232521)
            ·
              rfl

theorem cell20_559845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 10].length) (baseStart_559845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559845 prefixEnd_559845 := by exact prefixLift 559845
  have htrace : WordTrace (prefixWord ++ tailWord_559845) baseStart_559845 baseEnd_559845 := by
    simpa [prefixWord, tailWord_559845, baseEnd_559845] using wordTrace_append hprefix tailTrace_559845
  have hstable : (prefixWord ++ tailWord_559845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559845).length < 2 ^ (prefixWord ++ tailWord_559845).sum := by decide
  have hdescent : baseEnd_559845 < baseStart_559845 := by decide
  rcases family_descends (prefixWord ++ tailWord_559845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559869 : List Nat := [1, 4, 1, 1, 1, 1, 3, 5, 3]
def baseStart_559869 : Nat := 118140960795 + 559869 * 2 ^ 59
def prefixEnd_559869 : Nat := 4983230072969 + 3 ^ 40 * 559869 * 2
def baseEnd_559869 : Nat := 255539467157489105477969

theorem tailTrace_559869 : CollatzResearch.WordTrace tailWord_559869 prefixEnd_559869 255539467157489105477969 := by
  unfold tailWord_559869
  simp only [CollatzResearch.WordTrace]
  refine ⟨20420100008697705857770661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13613400005798470571847107 20420100008697705857770661)
  ·
    refine ⟨3828768751630819848331999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20420100008697705857770661 3828768751630819848331999)
    ·
      refine ⟨5743153127446229772497999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3828768751630819848331999 5743153127446229772497999)
      ·
        refine ⟨8614729691169344658746999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5743153127446229772497999 8614729691169344658746999)
        ·
          refine ⟨12922094536754016988120499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8614729691169344658746999 12922094536754016988120499)
          ·
            refine ⟨19383141805131025482180749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12922094536754016988120499 19383141805131025482180749)
            ·
              refine ⟨7268678176924134555817781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19383141805131025482180749 7268678176924134555817781)
              ·
                refine ⟨681438579086637614607917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7268678176924134555817781 681438579086637614607917)
                ·
                  refine ⟨255539467157489105477969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681438579086637614607917 255539467157489105477969)
                  ·
                    rfl

theorem cell20_559869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_559869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559869 prefixEnd_559869 := by exact prefixLift 559869
  have htrace : WordTrace (prefixWord ++ tailWord_559869) baseStart_559869 baseEnd_559869 := by
    simpa [prefixWord, tailWord_559869, baseEnd_559869] using wordTrace_append hprefix tailTrace_559869
  have hstable : (prefixWord ++ tailWord_559869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559869).length < 2 ^ (prefixWord ++ tailWord_559869).sum := by decide
  have hdescent : baseEnd_559869 < baseStart_559869 := by decide
  rcases family_descends (prefixWord ++ tailWord_559869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559879 : List Nat := [1, 1, 4, 4, 1, 2, 3, 4]
def baseStart_559879 : Nat := 118140960795 + 559879 * 2 ^ 59
def prefixEnd_559879 : Nat := 4983230072969 + 3 ^ 40 * 559879 * 2
def baseEnd_559879 : Nat := 85181343809991171714865

theorem tailTrace_559879 : CollatzResearch.WordTrace tailWord_559879 prefixEnd_559879 85181343809991171714865 := by
  unfold tailWord_559879
  simp only [CollatzResearch.WordTrace]
  refine ⟨20420464738661477565634691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13613643159107651710423127 20420464738661477565634691)
  ·
    refine ⟨30630697107992216348452037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20420464738661477565634691 30630697107992216348452037)
    ·
      refine ⟨5743255707748540565334757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30630697107992216348452037 5743255707748540565334757)
      ·
        refine ⟨1076860445202851356000267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5743255707748540565334757 1076860445202851356000267)
        ·
          refine ⟨1615290667804277034000401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1076860445202851356000267 1615290667804277034000401)
          ·
            refine ⟨1211468000853207775500301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1615290667804277034000401 1211468000853207775500301)
            ·
              refine ⟨454300500319952915812613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1211468000853207775500301 454300500319952915812613)
              ·
                refine ⟨85181343809991171714865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 454300500319952915812613 85181343809991171714865)
                ·
                  rfl

theorem cell20_559879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 4].length) (baseStart_559879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559879 prefixEnd_559879 := by exact prefixLift 559879
  have htrace : WordTrace (prefixWord ++ tailWord_559879) baseStart_559879 baseEnd_559879 := by
    simpa [prefixWord, tailWord_559879, baseEnd_559879] using wordTrace_append hprefix tailTrace_559879
  have hstable : (prefixWord ++ tailWord_559879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559879).length < 2 ^ (prefixWord ++ tailWord_559879).sum := by decide
  have hdescent : baseEnd_559879 < baseStart_559879 := by decide
  rcases family_descends (prefixWord ++ tailWord_559879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559921 : List Nat := [1, 2, 2, 3, 2, 1, 2, 7]
def baseStart_559921 : Nat := 118140960795 + 559921 * 2 ^ 59
def prefixEnd_559921 : Nat := 4983230072969 + 3 ^ 40 * 559921 * 2
def baseEnd_559921 : Nat := 85187733791469345248141

theorem tailTrace_559921 : CollatzResearch.WordTrace tailWord_559921 prefixEnd_559921 85187733791469345248141 := by
  unfold tailWord_559921
  simp only [CollatzResearch.WordTrace]
  refine ⟨20421996604509318738663617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13614664403006212492442411 20421996604509318738663617)
  ·
    refine ⟨15316497453381989053997713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20421996604509318738663617 15316497453381989053997713)
    ·
      refine ⟨11487373090036491790498285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15316497453381989053997713 11487373090036491790498285)
      ·
        refine ⟨4307764908763684421436857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11487373090036491790498285 4307764908763684421436857)
        ·
          refine ⟨3230823681572763316077643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4307764908763684421436857 3230823681572763316077643)
          ·
            refine ⟨4846235522359144974116465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3230823681572763316077643 4846235522359144974116465)
            ·
              refine ⟨3634676641769358730587349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4846235522359144974116465 3634676641769358730587349)
              ·
                refine ⟨85187733791469345248141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3634676641769358730587349 85187733791469345248141)
                ·
                  rfl

theorem cell20_559921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 7].length) (baseStart_559921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559921 prefixEnd_559921 := by exact prefixLift 559921
  have htrace : WordTrace (prefixWord ++ tailWord_559921) baseStart_559921 baseEnd_559921 := by
    simpa [prefixWord, tailWord_559921, baseEnd_559921] using wordTrace_append hprefix tailTrace_559921
  have hstable : (prefixWord ++ tailWord_559921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559921).length < 2 ^ (prefixWord ++ tailWord_559921).sum := by decide
  have hdescent : baseEnd_559921 < baseStart_559921 := by decide
  rcases family_descends (prefixWord ++ tailWord_559921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559934 : List Nat := [4, 2, 1, 2, 3, 2, 2, 4]
def baseStart_559934 : Nat := 118140960795 + 559934 * 2 ^ 59
def prefixEnd_559934 : Nat := 4983230072969 + 3 ^ 40 * 559934 * 2
def baseEnd_559934 : Nat := 85189711642879256103679

theorem tailTrace_559934 : CollatzResearch.WordTrace tailWord_559934 prefixEnd_559934 85189711642879256103679 := by
  unfold tailWord_559934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2552808844182777744860857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13614980502308147972591237 2552808844182777744860857)
  ·
    refine ⟨1914606633137083308645643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2552808844182777744860857 1914606633137083308645643)
    ·
      refine ⟨2871909949705624962968465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1914606633137083308645643 2871909949705624962968465)
      ·
        refine ⟨2153932462279218722226349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2871909949705624962968465 2153932462279218722226349)
        ·
          refine ⟨807724673354707020834881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2153932462279218722226349 807724673354707020834881)
          ·
            refine ⟨605793505016030265626161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 807724673354707020834881 605793505016030265626161)
            ·
              refine ⟨454345128762022699219621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 605793505016030265626161 454345128762022699219621)
              ·
                refine ⟨85189711642879256103679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 454345128762022699219621 85189711642879256103679)
                ·
                  rfl

theorem cell20_559934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_559934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559934 prefixEnd_559934 := by exact prefixLift 559934
  have htrace : WordTrace (prefixWord ++ tailWord_559934) baseStart_559934 baseEnd_559934 := by
    simpa [prefixWord, tailWord_559934, baseEnd_559934] using wordTrace_append hprefix tailTrace_559934
  have hstable : (prefixWord ++ tailWord_559934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559934).length < 2 ^ (prefixWord ++ tailWord_559934).sum := by decide
  have hdescent : baseEnd_559934 < baseStart_559934 := by decide
  rcases family_descends (prefixWord ++ tailWord_559934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559948 : List Nat := [2, 2, 1, 3, 3, 1, 3, 3, 2]
def baseStart_559948 : Nat := 118140960795 + 559948 * 2 ^ 59
def prefixEnd_559948 : Nat := 4983230072969 + 3 ^ 40 * 559948 * 2
def baseEnd_559948 : Nat := 255575524910115941844313

theorem tailTrace_559948 : CollatzResearch.WordTrace tailWord_559948 prefixEnd_559948 255575524910115941844313 := by
  unfold tailWord_559948
  simp only [CollatzResearch.WordTrace]
  refine ⟨10211490687705751174948249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13615320916941001566597665 10211490687705751174948249)
  ·
    refine ⟨7658618015779313381211187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10211490687705751174948249 7658618015779313381211187)
    ·
      refine ⟨11487927023668970071816781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7658618015779313381211187 11487927023668970071816781)
      ·
        refine ⟨4307972633875863776931293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11487927023668970071816781 4307972633875863776931293)
        ·
          refine ⟨1615489737703448916349235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4307972633875863776931293 1615489737703448916349235)
          ·
            refine ⟨2423234606555173374523853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1615489737703448916349235 2423234606555173374523853)
            ·
              refine ⟨908712977458190015446445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2423234606555173374523853 908712977458190015446445)
              ·
                refine ⟨340767366546821255792417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 908712977458190015446445 340767366546821255792417)
                ·
                  refine ⟨255575524910115941844313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340767366546821255792417 255575524910115941844313)
                  ·
                    rfl

theorem cell20_559948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_559948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559948 prefixEnd_559948 := by exact prefixLift 559948
  have htrace : WordTrace (prefixWord ++ tailWord_559948) baseStart_559948 baseEnd_559948 := by
    simpa [prefixWord, tailWord_559948, baseEnd_559948] using wordTrace_append hprefix tailTrace_559948
  have hstable : (prefixWord ++ tailWord_559948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559948).length < 2 ^ (prefixWord ++ tailWord_559948).sum := by decide
  have hdescent : baseEnd_559948 < baseStart_559948 := by decide
  rcases family_descends (prefixWord ++ tailWord_559948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559959 : List Nat := [1, 1, 3, 2, 4, 1, 8]
def baseStart_559959 : Nat := 118140960795 + 559959 * 2 ^ 59
def prefixEnd_559959 : Nat := 4983230072969 + 3 ^ 40 * 559959 * 2
def baseEnd_559959 : Nat := 28397838401094310275289

theorem tailTrace_559959 : CollatzResearch.WordTrace tailWord_559959 prefixEnd_559959 28397838401094310275289 := by
  unfold tailWord_559959
  simp only [CollatzResearch.WordTrace]
  refine ⟨20423382578371651228546931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13615588385581100819031287 20423382578371651228546931)
  ·
    refine ⟨30635073867557476842820397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20423382578371651228546931 30635073867557476842820397)
    ·
      refine ⟨11488152700334053816057649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30635073867557476842820397 11488152700334053816057649)
      ·
        refine ⟨8616114525250540362043237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11488152700334053816057649 8616114525250540362043237)
        ·
          refine ⟨1615521473484476317883107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8616114525250540362043237 1615521473484476317883107)
          ·
            refine ⟨2423282210226714476824661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1615521473484476317883107 2423282210226714476824661)
            ·
              refine ⟨28397838401094310275289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2423282210226714476824661 28397838401094310275289)
              ·
                rfl

theorem cell20_559959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 8].length) (baseStart_559959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559959 prefixEnd_559959 := by exact prefixLift 559959
  have htrace : WordTrace (prefixWord ++ tailWord_559959) baseStart_559959 baseEnd_559959 := by
    simpa [prefixWord, tailWord_559959, baseEnd_559959] using wordTrace_append hprefix tailTrace_559959
  have hstable : (prefixWord ++ tailWord_559959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559959).length < 2 ^ (prefixWord ++ tailWord_559959).sum := by decide
  have hdescent : baseEnd_559959 < baseStart_559959 := by decide
  rcases family_descends (prefixWord ++ tailWord_559959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559976 : List Nat := [2, 1, 4, 2, 1, 3, 2, 5]
def baseStart_559976 : Nat := 118140960795 + 559976 * 2 ^ 59
def prefixEnd_559976 : Nat := 4983230072969 + 3 ^ 40 * 559976 * 2
def baseEnd_559976 : Nat := 85196101624357429636955

theorem tailTrace_559976 : CollatzResearch.WordTrace tailWord_559976 prefixEnd_559976 85196101624357429636955 := by
  unfold tailWord_559976
  simp only [CollatzResearch.WordTrace]
  refine ⟨10212001309655031565957891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13616001746206708754610521 10212001309655031565957891)
  ·
    refine ⟨15318001964482547348936837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10212001309655031565957891 15318001964482547348936837)
    ·
      refine ⟨2872125368340477627925657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15318001964482547348936837 2872125368340477627925657)
      ·
        refine ⟨2154094026255358220944243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2872125368340477627925657 2154094026255358220944243)
        ·
          refine ⟨3231141039383037331416365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2154094026255358220944243 3231141039383037331416365)
          ·
            refine ⟨1211677889768638999281137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3231141039383037331416365 1211677889768638999281137)
            ·
              refine ⟨908758417326479249460853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1211677889768638999281137 908758417326479249460853)
              ·
                refine ⟨85196101624357429636955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 908758417326479249460853 85196101624357429636955)
                ·
                  rfl

theorem cell20_559976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_559976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559976 prefixEnd_559976 := by exact prefixLift 559976
  have htrace : WordTrace (prefixWord ++ tailWord_559976) baseStart_559976 baseEnd_559976 := by
    simpa [prefixWord, tailWord_559976, baseEnd_559976] using wordTrace_append hprefix tailTrace_559976
  have hstable : (prefixWord ++ tailWord_559976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559976).length < 2 ^ (prefixWord ++ tailWord_559976).sum := by decide
  have hdescent : baseEnd_559976 < baseStart_559976 := by decide
  rcases family_descends (prefixWord ++ tailWord_559976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559997 : List Nat := [1, 4, 1, 1, 2, 1, 4, 6]
def baseStart_559997 : Nat := 118140960795 + 559997 * 2 ^ 59
def prefixEnd_559997 : Nat := 4983230072969 + 3 ^ 40 * 559997 * 2
def baseEnd_559997 : Nat := 85199296615096516403593

theorem tailTrace_559997 : CollatzResearch.WordTrace tailWord_559997 prefixEnd_559997 85199296615096516403593 := by
  unfold tailWord_559997
  simp only [CollatzResearch.WordTrace]
  refine ⟨20424768552233983718430245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13616512368155989145620163 20424768552233983718430245)
  ·
    refine ⟨3829644103543871947205671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20424768552233983718430245 3829644103543871947205671)
    ·
      refine ⟨5744466155315807920808507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3829644103543871947205671 5744466155315807920808507)
      ·
        refine ⟨8616699232973711881212761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5744466155315807920808507 8616699232973711881212761)
        ·
          refine ⟨6462524424730283910909571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8616699232973711881212761 6462524424730283910909571)
          ·
            refine ⟨9693786637095425866364357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6462524424730283910909571 9693786637095425866364357)
            ·
              refine ⟨1817584994455392349943317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9693786637095425866364357 1817584994455392349943317)
              ·
                refine ⟨85199296615096516403593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1817584994455392349943317 85199296615096516403593)
                ·
                  rfl

theorem cell20_559997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 6].length) (baseStart_559997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_559997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_559997 prefixEnd_559997 := by exact prefixLift 559997
  have htrace : WordTrace (prefixWord ++ tailWord_559997) baseStart_559997 baseEnd_559997 := by
    simpa [prefixWord, tailWord_559997, baseEnd_559997] using wordTrace_append hprefix tailTrace_559997
  have hstable : (prefixWord ++ tailWord_559997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559997).length < 2 ^ (prefixWord ++ tailWord_559997).sum := by decide
  have hdescent : baseEnd_559997 < baseStart_559997 := by decide
  rcases family_descends (prefixWord ++ tailWord_559997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560021 : List Nat := [1, 3, 2, 1, 1, 4, 1, 4, 3]
def baseStart_560021 : Nat := 118140960795 + 560021 * 2 ^ 59
def prefixEnd_560021 : Nat := 4983230072969 + 3 ^ 40 * 560021 * 2
def baseEnd_560021 : Nat := 255608844099252132410681

theorem tailTrace_560021 : CollatzResearch.WordTrace tailWord_560021 prefixEnd_560021 255608844099252132410681 := by
  unfold tailWord_560021
  simp only [CollatzResearch.WordTrace]
  refine ⟨20425643904147035817303917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13617095936098023878202611 20425643904147035817303917)
  ·
    refine ⟨7659616464055138431488969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20425643904147035817303917 7659616464055138431488969)
    ·
      refine ⟨5744712348041353823616727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7659616464055138431488969 5744712348041353823616727)
      ·
        refine ⟨8617068522062030735425091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5744712348041353823616727 8617068522062030735425091)
        ·
          refine ⟨12925602783093046103137637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8617068522062030735425091 12925602783093046103137637)
          ·
            refine ⟨2423550521829946144338307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12925602783093046103137637 2423550521829946144338307)
            ·
              refine ⟨3635325782744919216507461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2423550521829946144338307 3635325782744919216507461)
              ·
                refine ⟨681623584264672353095149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3635325782744919216507461 681623584264672353095149)
                ·
                  refine ⟨255608844099252132410681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681623584264672353095149 255608844099252132410681)
                  ·
                    rfl

theorem cell20_560021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_560021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560021 prefixEnd_560021 := by exact prefixLift 560021
  have htrace : WordTrace (prefixWord ++ tailWord_560021) baseStart_560021 baseEnd_560021 := by
    simpa [prefixWord, tailWord_560021, baseEnd_560021] using wordTrace_append hprefix tailTrace_560021
  have hstable : (prefixWord ++ tailWord_560021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560021).length < 2 ^ (prefixWord ++ tailWord_560021).sum := by decide
  have hdescent : baseEnd_560021 < baseStart_560021 := by decide
  rcases family_descends (prefixWord ++ tailWord_560021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560035 : List Nat := [1, 1, 1, 4, 1, 2, 5, 5]
def baseStart_560035 : Nat := 118140960795 + 560035 * 2 ^ 59
def prefixEnd_560035 : Nat := 4983230072969 + 3 ^ 40 * 560035 * 2
def baseEnd_560035 : Nat := 85205078026910101981319

theorem tailTrace_560035 : CollatzResearch.WordTrace tailWord_560035 prefixEnd_560035 85205078026910101981319 := by
  unfold tailWord_560035
  simp only [CollatzResearch.WordTrace]
  refine ⟨20426154526096316208313559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13617436350730877472209039 20426154526096316208313559)
  ·
    refine ⟨30639231789144474312470339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20426154526096316208313559 30639231789144474312470339)
    ·
      refine ⟨45958847683716711468705509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30639231789144474312470339 45958847683716711468705509)
      ·
        refine ⟨8617283940696883400382283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45958847683716711468705509 8617283940696883400382283)
        ·
          refine ⟨12925925911045325100573425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8617283940696883400382283 12925925911045325100573425)
          ·
            refine ⟨9694444433283993825430069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12925925911045325100573425 9694444433283993825430069)
            ·
              refine ⟨908854165620374421134069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9694444433283993825430069 908854165620374421134069)
              ·
                refine ⟨85205078026910101981319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 908854165620374421134069 85205078026910101981319)
                ·
                  rfl

theorem cell20_560035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 5].length) (baseStart_560035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560035 prefixEnd_560035 := by exact prefixLift 560035
  have htrace : WordTrace (prefixWord ++ tailWord_560035) baseStart_560035 baseEnd_560035 := by
    simpa [prefixWord, tailWord_560035, baseEnd_560035] using wordTrace_append hprefix tailTrace_560035
  have hstable : (prefixWord ++ tailWord_560035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560035).length < 2 ^ (prefixWord ++ tailWord_560035).sum := by decide
  have hdescent : baseEnd_560035 < baseStart_560035 := by decide
  rcases family_descends (prefixWord ++ tailWord_560035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560062 : List Nat := [4, 2, 1, 1, 1, 2, 4, 3, 2]
def baseStart_560062 : Nat := 118140960795 + 560062 * 2 ^ 59
def prefixEnd_560062 : Nat := 4983230072969 + 3 ^ 40 * 560062 * 2
def baseEnd_560062 : Nat := 255627557616438212043847

theorem tailTrace_560062 : CollatzResearch.WordTrace tailWord_560062 prefixEnd_560062 255627557616438212043847 := by
  unfold tailWord_560062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2553392412124812477443305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13618092864665666546364293 2553392412124812477443305)
  ·
    refine ⟨1915044309093609358082479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2553392412124812477443305 1915044309093609358082479)
    ·
      refine ⟨2872566463640414037123719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1915044309093609358082479 2872566463640414037123719)
      ·
        refine ⟨4308849695460621055685579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2872566463640414037123719 4308849695460621055685579)
        ·
          refine ⟨6463274543190931583528369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4308849695460621055685579 6463274543190931583528369)
          ·
            refine ⟨4847455907393198687646277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6463274543190931583528369 4847455907393198687646277)
            ·
              refine ⟨908897982636224753933677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4847455907393198687646277 908897982636224753933677)
              ·
                refine ⟨340836743488584282725129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 908897982636224753933677 340836743488584282725129)
                ·
                  refine ⟨255627557616438212043847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340836743488584282725129 255627557616438212043847)
                  ·
                    rfl

theorem cell20_560062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_560062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560062 prefixEnd_560062 := by exact prefixLift 560062
  have htrace : WordTrace (prefixWord ++ tailWord_560062) baseStart_560062 baseEnd_560062 := by
    simpa [prefixWord, tailWord_560062, baseEnd_560062] using wordTrace_append hprefix tailTrace_560062
  have hstable : (prefixWord ++ tailWord_560062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560062).length < 2 ^ (prefixWord ++ tailWord_560062).sum := by decide
  have hdescent : baseEnd_560062 < baseStart_560062 := by decide
  rcases family_descends (prefixWord ++ tailWord_560062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560093 : List Nat := [1, 4, 3, 1, 2, 2, 3, 1, 3]
def baseStart_560093 : Nat := 118140960795 + 560093 * 2 ^ 59
def prefixEnd_560093 : Nat := 4983230072969 + 3 ^ 40 * 560093 * 2
def baseEnd_560093 : Nat := 255641706861139882010387

theorem tailTrace_560093 : CollatzResearch.WordTrace tailWord_560093 prefixEnd_560093 255641706861139882010387 := by
  unfold tailWord_560093
  simp only [CollatzResearch.WordTrace]
  refine ⟨20428269959886192113924933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13618846639924128075949955 20428269959886192113924933)
  ·
    refine ⟨3830300617478661021360925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20428269959886192113924933 3830300617478661021360925)
    ·
      refine ⟨1436362731554497883010347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3830300617478661021360925 1436362731554497883010347)
      ·
        refine ⟨2154544097331746824515521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1436362731554497883010347 2154544097331746824515521)
        ·
          refine ⟨1615908072998810118386641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2154544097331746824515521 1615908072998810118386641)
          ·
            refine ⟨1211931054749107588789981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1615908072998810118386641 1211931054749107588789981)
            ·
              refine ⟨454474145530915345796243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1211931054749107588789981 454474145530915345796243)
              ·
                refine ⟨681711218296373018694365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454474145530915345796243 681711218296373018694365)
                ·
                  refine ⟨255641706861139882010387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681711218296373018694365 255641706861139882010387)
                  ·
                    rfl

theorem cell20_560093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_560093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560093 prefixEnd_560093 := by exact prefixLift 560093
  have htrace : WordTrace (prefixWord ++ tailWord_560093) baseStart_560093 baseEnd_560093 := by
    simpa [prefixWord, tailWord_560093, baseEnd_560093] using wordTrace_append hprefix tailTrace_560093
  have hstable : (prefixWord ++ tailWord_560093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560093).length < 2 ^ (prefixWord ++ tailWord_560093).sum := by decide
  have hdescent : baseEnd_560093 < baseStart_560093 := by decide
  rcases family_descends (prefixWord ++ tailWord_560093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560104 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 4]
def baseStart_560104 : Nat := 118140960795 + 560104 * 2 ^ 59
def prefixEnd_560104 : Nat := 4983230072969 + 3 ^ 40 * 560104 * 2
def baseEnd_560104 : Nat := 255646727560872732643675

theorem tailTrace_560104 : CollatzResearch.WordTrace tailWord_560104 prefixEnd_560104 255646727560872732643675 := by
  unfold tailWord_560104
  simp only [CollatzResearch.WordTrace]
  refine ⟨10214335581423170496287683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13619114108564227328383577 10214335581423170496287683)
  ·
    refine ⟨15321503372134755744431525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10214335581423170496287683 15321503372134755744431525)
    ·
      refine ⟨2872781882275266702080911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15321503372134755744431525 2872781882275266702080911)
      ·
        refine ⟨4309172823412900053121367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2872781882275266702080911 4309172823412900053121367)
        ·
          refine ⟨6463759235119350079682051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4309172823412900053121367 6463759235119350079682051)
          ·
            refine ⟨9695638852679025119523077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6463759235119350079682051 9695638852679025119523077)
            ·
              refine ⟨1817932284877317209910577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9695638852679025119523077 1817932284877317209910577)
              ·
                refine ⟨1363449213657987907432933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1817932284877317209910577 1363449213657987907432933)
                ·
                  refine ⟨255646727560872732643675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1363449213657987907432933 255646727560872732643675)
                  ·
                    rfl

theorem cell20_560104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_560104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560104 prefixEnd_560104 := by exact prefixLift 560104
  have htrace : WordTrace (prefixWord ++ tailWord_560104) baseStart_560104 baseEnd_560104 := by
    simpa [prefixWord, tailWord_560104, baseEnd_560104] using wordTrace_append hprefix tailTrace_560104
  have hstable : (prefixWord ++ tailWord_560104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560104).length < 2 ^ (prefixWord ++ tailWord_560104).sum := by decide
  have hdescent : baseEnd_560104 < baseStart_560104 := by decide
  rcases family_descends (prefixWord ++ tailWord_560104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560111 : List Nat := [1, 1, 2, 1, 4, 4, 1, 6]
def baseStart_560111 : Nat := 118140960795 + 560111 * 2 ^ 59
def prefixEnd_560111 : Nat := 4983230072969 + 3 ^ 40 * 560111 * 2
def baseEnd_560111 : Nat := 85216640850537273136771

theorem tailTrace_560111 : CollatzResearch.WordTrace tailWord_560111 prefixEnd_560111 85216640850537273136771 := by
  unfold tailWord_560111
  simp only [CollatzResearch.WordTrace]
  refine ⟨20428926473820981188080187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13619284315880654125386791 20428926473820981188080187)
  ·
    refine ⟨30643389710731471782120281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20428926473820981188080187 30643389710731471782120281)
    ·
      refine ⟨22982542283048603836590211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30643389710731471782120281 22982542283048603836590211)
      ·
        refine ⟨34473813424572905754885317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22982542283048603836590211 34473813424572905754885317)
        ·
          refine ⟨6463840017107419829040997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34473813424572905754885317 6463840017107419829040997)
          ·
            refine ⟨1211970003207641217945187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6463840017107419829040997 1211970003207641217945187)
            ·
              refine ⟨1817955004811461826917781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211970003207641217945187 1817955004811461826917781)
              ·
                refine ⟨85216640850537273136771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1817955004811461826917781 85216640850537273136771)
                ·
                  rfl

theorem cell20_560111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 6].length) (baseStart_560111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560111 prefixEnd_560111 := by exact prefixLift 560111
  have htrace : WordTrace (prefixWord ++ tailWord_560111) baseStart_560111 baseEnd_560111 := by
    simpa [prefixWord, tailWord_560111, baseEnd_560111] using wordTrace_append hprefix tailTrace_560111
  have hstable : (prefixWord ++ tailWord_560111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560111).length < 2 ^ (prefixWord ++ tailWord_560111).sum := by decide
  have hdescent : baseEnd_560111 < baseStart_560111 := by decide
  rcases family_descends (prefixWord ++ tailWord_560111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560135 : List Nat := [1, 1, 4, 3, 1, 1, 2, 4, 3]
def baseStart_560135 : Nat := 118140960795 + 560135 * 2 ^ 59
def prefixEnd_560135 : Nat := 4983230072969 + 3 ^ 40 * 560135 * 2
def baseEnd_560135 : Nat := 255660876805574402610215

theorem tailTrace_560135 : CollatzResearch.WordTrace tailWord_560135 prefixEnd_560135 255660876805574402610215 := by
  unfold tailWord_560135
  simp only [CollatzResearch.WordTrace]
  refine ⟨20429801825734033286953859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13619867883822688857969239 20429801825734033286953859)
  ·
    refine ⟨30644702738601049930430789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20429801825734033286953859 30644702738601049930430789)
    ·
      refine ⟨5745881763487696861955773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30644702738601049930430789 5745881763487696861955773)
      ·
        refine ⟨2154705661307886323233415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5745881763487696861955773 2154705661307886323233415)
        ·
          refine ⟨3232058491961829484850123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2154705661307886323233415 3232058491961829484850123)
          ·
            refine ⟨4848087737942744227275185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3232058491961829484850123 4848087737942744227275185)
            ·
              refine ⟨3636065803457058170456389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4848087737942744227275185 3636065803457058170456389)
              ·
                refine ⟨681762338148198406960573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3636065803457058170456389 681762338148198406960573)
                ·
                  refine ⟨255660876805574402610215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681762338148198406960573 255660876805574402610215)
                  ·
                    rfl

theorem cell20_560135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 3].length) (baseStart_560135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560135 prefixEnd_560135 := by exact prefixLift 560135
  have htrace : WordTrace (prefixWord ++ tailWord_560135) baseStart_560135 baseEnd_560135 := by
    simpa [prefixWord, tailWord_560135, baseEnd_560135] using wordTrace_append hprefix tailTrace_560135
  have hstable : (prefixWord ++ tailWord_560135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560135).length < 2 ^ (prefixWord ++ tailWord_560135).sum := by decide
  have hdescent : baseEnd_560135 < baseStart_560135 := by decide
  rcases family_descends (prefixWord ++ tailWord_560135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560149 : List Nat := [1, 3, 2, 1, 4, 1, 1, 7]
def baseStart_560149 : Nat := 118140960795 + 560149 * 2 ^ 59
def prefixEnd_560149 : Nat := 4983230072969 + 3 ^ 40 * 560149 * 2
def baseEnd_560149 : Nat := 85222422262350858714497

theorem tailTrace_560149 : CollatzResearch.WordTrace tailWord_560149 prefixEnd_560149 85222422262350858714497 := by
  unfold tailWord_560149
  simp only [CollatzResearch.WordTrace]
  refine ⟨20430312447683313677963501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13620208298455542451975667 20430312447683313677963501)
  ·
    refine ⟨7661367167881242629236313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20430312447683313677963501 7661367167881242629236313)
    ·
      refine ⟨5746025375910931971927235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7661367167881242629236313 5746025375910931971927235)
      ·
        refine ⟨8619038063866397957890853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5746025375910931971927235 8619038063866397957890853)
        ·
          refine ⟨1616069636974949617104535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8619038063866397957890853 1616069636974949617104535)
          ·
            refine ⟨2424104455462424425656803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1616069636974949617104535 2424104455462424425656803)
            ·
              refine ⟨3636156683193636638485205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2424104455462424425656803 3636156683193636638485205)
              ·
                refine ⟨85222422262350858714497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3636156683193636638485205 85222422262350858714497)
                ·
                  rfl

theorem cell20_560149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 7].length) (baseStart_560149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560149 prefixEnd_560149 := by exact prefixLift 560149
  have htrace : WordTrace (prefixWord ++ tailWord_560149) baseStart_560149 baseEnd_560149 := by
    simpa [prefixWord, tailWord_560149, baseEnd_560149] using wordTrace_append hprefix tailTrace_560149
  have hstable : (prefixWord ++ tailWord_560149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560149).length < 2 ^ (prefixWord ++ tailWord_560149).sum := by decide
  have hdescent : baseEnd_560149 < baseStart_560149 := by decide
  rcases family_descends (prefixWord ++ tailWord_560149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560152 : List Nat := [2, 1, 2, 3, 2, 2, 4, 1, 3]
def baseStart_560152 : Nat := 118140960795 + 560152 * 2 ^ 59
def prefixEnd_560152 : Nat := 4983230072969 + 3 ^ 40 * 560152 * 2
def baseEnd_560152 : Nat := 255668636068797899043479

theorem tailTrace_560152 : CollatzResearch.WordTrace tailWord_560152 prefixEnd_560152 255668636068797899043479 := by
  unfold tailWord_560152
  simp only [CollatzResearch.WordTrace]
  refine ⟨10215210933336222595161355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13620281244448296793548473 10215210933336222595161355)
  ·
    refine ⟨15322816400004333892742033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10215210933336222595161355 15322816400004333892742033)
    ·
      refine ⟨11492112300003250419556525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15322816400004333892742033 11492112300003250419556525)
      ·
        refine ⟨4309542112501218907333697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11492112300003250419556525 4309542112501218907333697)
        ·
          refine ⟨3232156584375914180500273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4309542112501218907333697 3232156584375914180500273)
          ·
            refine ⟨2424117438281935635375205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3232156584375914180500273 2424117438281935635375205)
            ·
              refine ⟨454522019677862931632851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2424117438281935635375205 454522019677862931632851)
              ·
                refine ⟨681783029516794397449277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454522019677862931632851 681783029516794397449277)
                ·
                  refine ⟨255668636068797899043479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681783029516794397449277 255668636068797899043479)
                  ·
                    rfl

theorem cell20_560152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_560152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560152 prefixEnd_560152 := by exact prefixLift 560152
  have htrace : WordTrace (prefixWord ++ tailWord_560152) baseStart_560152 baseEnd_560152 := by
    simpa [prefixWord, tailWord_560152, baseEnd_560152] using wordTrace_append hprefix tailTrace_560152
  have hstable : (prefixWord ++ tailWord_560152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560152).length < 2 ^ (prefixWord ++ tailWord_560152).sum := by decide
  have hdescent : baseEnd_560152 < baseStart_560152 := by decide
  rcases family_descends (prefixWord ++ tailWord_560152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560190 : List Nat := [4, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_560190 : Nat := 118140960795 + 560190 * 2 ^ 59
def prefixEnd_560190 : Nat := 4983230072969 + 3 ^ 40 * 560190 * 2
def baseEnd_560190 : Nat := 255685980304238655776657

theorem tailTrace_560190 : CollatzResearch.WordTrace tailWord_560190 prefixEnd_560190 255685980304238655776657 := by
  unfold tailWord_560190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2553975980066847210025753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13621205227023185120137349 2553975980066847210025753)
  ·
    refine ⟨1915481985050135407519315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2553975980066847210025753 1915481985050135407519315)
    ·
      refine ⟨2873222977575203111278973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1915481985050135407519315 2873222977575203111278973)
      ·
        refine ⟨1077458616590701166729615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2873222977575203111278973 1077458616590701166729615)
        ·
          refine ⟨1616187924886051750094423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1077458616590701166729615 1616187924886051750094423)
          ·
            refine ⟨2424281887329077625141635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1616187924886051750094423 2424281887329077625141635)
            ·
              refine ⟨3636422830993616437712453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2424281887329077625141635 3636422830993616437712453)
              ·
                refine ⟨681829280811303082071085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3636422830993616437712453 681829280811303082071085)
                ·
                  refine ⟨255685980304238655776657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681829280811303082071085 255685980304238655776657)
                  ·
                    rfl

theorem cell20_560190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_560190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560190 prefixEnd_560190 := by exact prefixLift 560190
  have htrace : WordTrace (prefixWord ++ tailWord_560190) baseStart_560190 baseEnd_560190 := by
    simpa [prefixWord, tailWord_560190, baseEnd_560190] using wordTrace_append hprefix tailTrace_560190
  have hstable : (prefixWord ++ tailWord_560190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560190).length < 2 ^ (prefixWord ++ tailWord_560190).sum := by decide
  have hdescent : baseEnd_560190 < baseStart_560190 := by decide
  rcases family_descends (prefixWord ++ tailWord_560190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560239 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 6]
def baseStart_560239 : Nat := 118140960795 + 560239 * 2 ^ 59
def prefixEnd_560239 : Nat := 4983230072969 + 3 ^ 40 * 560239 * 2
def baseEnd_560239 : Nat := 255708345239412263143123

theorem tailTrace_560239 : CollatzResearch.WordTrace tailWord_560239 prefixEnd_560239 255708345239412263143123 := by
  unfold tailWord_560239
  simp only [CollatzResearch.WordTrace]
  refine ⟨20433595017357259048739771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13622396678238172699159847 20433595017357259048739771)
  ·
    refine ⟨30650392526035888573109657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20433595017357259048739771 30650392526035888573109657)
    ·
      refine ⟨22987794394526916429832243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30650392526035888573109657 22987794394526916429832243)
      ·
        refine ⟨34481691591790374644748365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22987794394526916429832243 34481691591790374644748365)
        ·
          refine ⟨12930634346921390491780637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34481691591790374644748365 12930634346921390491780637)
          ·
            refine ⟨4848987880095521434417739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12930634346921390491780637 4848987880095521434417739)
            ·
              refine ⟨7273481820143282151626609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4848987880095521434417739 7273481820143282151626609)
              ·
                refine ⟨5455111365107461613719957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7273481820143282151626609 5455111365107461613719957)
                ·
                  refine ⟨255708345239412263143123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5455111365107461613719957 255708345239412263143123)
                  ·
                    rfl

theorem cell20_560239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_560239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560239 prefixEnd_560239 := by exact prefixLift 560239
  have htrace : WordTrace (prefixWord ++ tailWord_560239) baseStart_560239 baseEnd_560239 := by
    simpa [prefixWord, tailWord_560239, baseEnd_560239] using wordTrace_append hprefix tailTrace_560239
  have hstable : (prefixWord ++ tailWord_560239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560239).length < 2 ^ (prefixWord ++ tailWord_560239).sum := by decide
  have hdescent : baseEnd_560239 < baseStart_560239 := by decide
  rcases family_descends (prefixWord ++ tailWord_560239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
