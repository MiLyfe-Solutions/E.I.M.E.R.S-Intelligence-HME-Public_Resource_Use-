import V185TrunkScan21Chunk139

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1707437 : List Nat := [1, 5, 2, 2, 1, 1, 4, 5]
def baseStart_1707437 : Nat := 118140960795 + 1707437 * 2 ^ 59
def prefixEnd_1707437 : Nat := 4983230072969 + 3 ^ 40 * 1707437 * 2
def baseEnd_1707437 : Nat := 129886795299398722753355

theorem tailTrace_1707437 : CollatzResearch.WordTrace tailWord_1707437 prefixEnd_1707437 129886795299398722753355 := by
  unfold tailWord_1707437
  simp only [CollatzResearch.WordTrace]
  refine ⟨62275343515254830868688565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41516895676836553912459043 62275343515254830868688565)
  ·
    refine ⟨5838313454555140393939553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62275343515254830868688565 5838313454555140393939553)
    ·
      refine ⟨4378735090916355295454665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5838313454555140393939553 4378735090916355295454665)
      ·
        refine ⟨3284051318187266471590999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4378735090916355295454665 3284051318187266471590999)
        ·
          refine ⟨4926076977280899707386499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3284051318187266471590999 4926076977280899707386499)
          ·
            refine ⟨7389115465921349561079749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4926076977280899707386499 7389115465921349561079749)
            ·
              refine ⟨1385459149860253042702453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7389115465921349561079749 1385459149860253042702453)
              ·
                refine ⟨129886795299398722753355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1385459149860253042702453 129886795299398722753355)
                ·
                  rfl

theorem cell21_1707437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 5].length) (baseStart_1707437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707437 prefixEnd_1707437 := by exact prefixLift 1707437
  have htrace : WordTrace (prefixWord ++ tailWord_1707437) baseStart_1707437 baseEnd_1707437 := by
    simpa [prefixWord, tailWord_1707437, baseEnd_1707437] using wordTrace_append hprefix tailTrace_1707437
  have hstable : (prefixWord ++ tailWord_1707437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707437).length < 2 ^ (prefixWord ++ tailWord_1707437).sum := by decide
  have hdescent : baseEnd_1707437 < baseStart_1707437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707448 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 6]
def baseStart_1707448 : Nat := 118140960795 + 1707448 * 2 ^ 59
def prefixEnd_1707448 : Nat := 4983230072969 + 3 ^ 40 * 1707448 * 2
def baseEnd_1707448 : Nat := 389662896248062593576709

theorem tailTrace_1707448 : CollatzResearch.WordTrace tailWord_1707448 prefixEnd_1707448 389662896248062593576709 := by
  unfold tailWord_1707448
  simp only [CollatzResearch.WordTrace]
  refine ⟨31137872359107489873669499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41517163145476653164892665 31137872359107489873669499)
  ·
    refine ⟨46706808538661234810504249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31137872359107489873669499 46706808538661234810504249)
    ·
      refine ⟨35030106403995926107878187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46706808538661234810504249 35030106403995926107878187)
      ·
        refine ⟨52545159605993889161817281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35030106403995926107878187 52545159605993889161817281)
        ·
          refine ⟨39408869704495416871362961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52545159605993889161817281 39408869704495416871362961)
          ·
            refine ⟨29556652278371562653522221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39408869704495416871362961 29556652278371562653522221)
            ·
              refine ⟨11083744604389335995070833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29556652278371562653522221 11083744604389335995070833)
              ·
                refine ⟨8312808453292001996303125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11083744604389335995070833 8312808453292001996303125)
                ·
                  refine ⟨389662896248062593576709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8312808453292001996303125 389662896248062593576709)
                  ·
                    rfl

theorem cell21_1707448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_1707448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707448 prefixEnd_1707448 := by exact prefixLift 1707448
  have htrace : WordTrace (prefixWord ++ tailWord_1707448) baseStart_1707448 baseEnd_1707448 := by
    simpa [prefixWord, tailWord_1707448, baseEnd_1707448] using wordTrace_append hprefix tailTrace_1707448
  have hstable : (prefixWord ++ tailWord_1707448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707448).length < 2 ^ (prefixWord ++ tailWord_1707448).sum := by decide
  have hdescent : baseEnd_1707448 < baseStart_1707448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707482 : List Nat := [3, 1, 1, 2, 3, 2, 4, 1, 4]
def baseStart_1707482 : Nat := 118140960795 + 1707482 * 2 ^ 59
def prefixEnd_1707482 : Nat := 4983230072969 + 3 ^ 40 * 1707482 * 2
def baseEnd_1707482 : Nat := 389670655511286090009973

theorem tailTrace_1707482 : CollatzResearch.WordTrace tailWord_1707482 prefixEnd_1707482 389670655511286090009973 := by
  unfold tailWord_1707482
  simp only [CollatzResearch.WordTrace]
  refine ⟨15569246200022950888519175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41517989866727869036051133 15569246200022950888519175)
  ·
    refine ⟨23353869300034426332778763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15569246200022950888519175 23353869300034426332778763)
    ·
      refine ⟨35030803950051639499168145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23353869300034426332778763 35030803950051639499168145)
      ·
        refine ⟨26273102962538729624376109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35030803950051639499168145 26273102962538729624376109)
        ·
          refine ⟨9852413610952023609141041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26273102962538729624376109 9852413610952023609141041)
          ·
            refine ⟨7389310208214017706855781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9852413610952023609141041 7389310208214017706855781)
            ·
              refine ⟨1385495664040128320035459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7389310208214017706855781 1385495664040128320035459)
              ·
                refine ⟨2078243496060192480053189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385495664040128320035459 2078243496060192480053189)
                ·
                  refine ⟨389670655511286090009973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2078243496060192480053189 389670655511286090009973)
                  ·
                    rfl

theorem cell21_1707482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_1707482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707482 prefixEnd_1707482 := by exact prefixLift 1707482
  have htrace : WordTrace (prefixWord ++ tailWord_1707482) baseStart_1707482 baseEnd_1707482 := by
    simpa [prefixWord, tailWord_1707482, baseEnd_1707482] using wordTrace_append hprefix tailTrace_1707482
  have hstable : (prefixWord ++ tailWord_1707482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707482).length < 2 ^ (prefixWord ++ tailWord_1707482).sum := by decide
  have hdescent : baseEnd_1707482 < baseStart_1707482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707541 : List Nat := [1, 3, 2, 1, 3, 2, 2, 3, 4]
def baseStart_1707541 : Nat := 118140960795 + 1707541 * 2 ^ 59
def prefixEnd_1707541 : Nat := 4983230072969 + 3 ^ 40 * 1707541 * 2
def baseEnd_1707541 : Nat := 389684120115115098526519

theorem tailTrace_1707541 : CollatzResearch.WordTrace tailWord_1707541 prefixEnd_1707541 389684120115115098526519 := by
  unfold tailWord_1707541
  simp only [CollatzResearch.WordTrace]
  refine ⟨62279136706878056630474477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41519424471252037753649651 62279136706878056630474477)
  ·
    refine ⟨23354676265079271236427929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62279136706878056630474477 23354676265079271236427929)
    ·
      refine ⟨17516007198809453427320947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23354676265079271236427929 17516007198809453427320947)
      ·
        refine ⟨26274010798214180140981421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17516007198809453427320947 26274010798214180140981421)
        ·
          refine ⟨9852754049330317552868033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26274010798214180140981421 9852754049330317552868033)
          ·
            refine ⟨7389565536997738164651025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9852754049330317552868033 7389565536997738164651025)
            ·
              refine ⟨5542174152748303623488269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7389565536997738164651025 5542174152748303623488269)
              ·
                refine ⟨2078315307280613858808101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5542174152748303623488269 2078315307280613858808101)
                ·
                  refine ⟨389684120115115098526519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2078315307280613858808101 389684120115115098526519)
                  ·
                    rfl

theorem cell21_1707541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_1707541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707541 prefixEnd_1707541 := by exact prefixLift 1707541
  have htrace : WordTrace (prefixWord ++ tailWord_1707541) baseStart_1707541 baseEnd_1707541 := by
    simpa [prefixWord, tailWord_1707541, baseEnd_1707541] using wordTrace_append hprefix tailTrace_1707541
  have hstable : (prefixWord ++ tailWord_1707541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707541).length < 2 ^ (prefixWord ++ tailWord_1707541).sum := by decide
  have hdescent : baseEnd_1707541 < baseStart_1707541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707569 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 9]
def baseStart_1707569 : Nat := 118140960795 + 1707569 * 2 ^ 59
def prefixEnd_1707569 : Nat := 4983230072969 + 3 ^ 40 * 1707569 * 2
def baseEnd_1707569 : Nat := 389690510096593272059795

theorem tailTrace_1707569 : CollatzResearch.WordTrace tailWord_1707569 prefixEnd_1707569 389690510096593272059795 := by
  unfold tailWord_1707569
  simp only [CollatzResearch.WordTrace]
  refine ⟨62280157950776617412493761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41520105300517744941662507 62280157950776617412493761)
  ·
    refine ⟨46710118463082463059370321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62280157950776617412493761 46710118463082463059370321)
    ·
      refine ⟨35032588847311847294527741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46710118463082463059370321 35032588847311847294527741)
      ·
        refine ⟨13137220817741942735447903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35032588847311847294527741 13137220817741942735447903)
        ·
          refine ⟨19705831226612914103171855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13137220817741942735447903 19705831226612914103171855)
          ·
            refine ⟨29558746839919371154757783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19705831226612914103171855 29558746839919371154757783)
            ·
              refine ⟨44338120259879056732136675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29558746839919371154757783 44338120259879056732136675)
              ·
                refine ⟨66507180389818585098205013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44338120259879056732136675 66507180389818585098205013)
                ·
                  refine ⟨389690510096593272059795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66507180389818585098205013 389690510096593272059795)
                  ·
                    rfl

theorem cell21_1707569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_1707569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707569 prefixEnd_1707569 := by exact prefixLift 1707569
  have htrace : WordTrace (prefixWord ++ tailWord_1707569) baseStart_1707569 baseEnd_1707569 := by
    simpa [prefixWord, tailWord_1707569, baseEnd_1707569] using wordTrace_append hprefix tailTrace_1707569
  have hstable : (prefixWord ++ tailWord_1707569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707569).length < 2 ^ (prefixWord ++ tailWord_1707569).sum := by decide
  have hdescent : baseEnd_1707569 < baseStart_1707569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707606 : List Nat := [5, 2, 2, 2, 1, 1, 1, 7]
def baseStart_1707606 : Nat := 118140960795 + 1707606 * 2 ^ 59
def prefixEnd_1707606 : Nat := 4983230072969 + 3 ^ 40 * 1707606 * 2
def baseEnd_1707606 : Nat := 129899651333563143314351

theorem tailTrace_1707606 : CollatzResearch.WordTrace tailWord_1707606 prefixEnd_1707606 129899651333563143314351 := by
  unfold tailWord_1707606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3892594215727660795724417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41521004967761715154393781 3892594215727660795724417)
  ·
    refine ⟨2919445661795745596793313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3892594215727660795724417 2919445661795745596793313)
    ·
      refine ⟨2189584246346809197594985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2919445661795745596793313 2189584246346809197594985)
      ·
        refine ⟨1642188184760106898196239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2189584246346809197594985 1642188184760106898196239)
        ·
          refine ⟨2463282277140160347294359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1642188184760106898196239 2463282277140160347294359)
          ·
            refine ⟨3694923415710240520941539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2463282277140160347294359 3694923415710240520941539)
            ·
              refine ⟨5542385123565360781412309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694923415710240520941539 5542385123565360781412309)
              ·
                refine ⟨129899651333563143314351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5542385123565360781412309 129899651333563143314351)
                ·
                  rfl

theorem cell21_1707606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_1707606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707606 prefixEnd_1707606 := by exact prefixLift 1707606
  have htrace : WordTrace (prefixWord ++ tailWord_1707606) baseStart_1707606 baseEnd_1707606 := by
    simpa [prefixWord, tailWord_1707606, baseEnd_1707606] using wordTrace_append hprefix tailTrace_1707606
  have hstable : (prefixWord ++ tailWord_1707606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707606).length < 2 ^ (prefixWord ++ tailWord_1707606).sum := by decide
  have hdescent : baseEnd_1707606 < baseStart_1707606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707620 : List Nat := [2, 3, 1, 1, 2, 5, 1, 3, 3]
def baseStart_1707620 : Nat := 118140960795 + 1707620 * 2 ^ 59
def prefixEnd_1707620 : Nat := 4983230072969 + 3 ^ 40 * 1707620 * 2
def baseEnd_1707620 : Nat := 389702148991428516709691

theorem tailTrace_1707620 : CollatzResearch.WordTrace tailWord_1707620 prefixEnd_1707620 389702148991428516709691 := by
  unfold tailWord_1707620
  simp only [CollatzResearch.WordTrace]
  refine ⟨31141009036795926561300157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41521345382394568748400209 31141009036795926561300157)
  ·
    refine ⟨11677878388798472460487559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31141009036795926561300157 11677878388798472460487559)
    ·
      refine ⟨17516817583197708690731339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11677878388798472460487559 17516817583197708690731339)
      ·
        refine ⟨26275226374796563036097009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17516817583197708690731339 26275226374796563036097009)
        ·
          refine ⟨19706419781097422277072757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26275226374796563036097009 19706419781097422277072757)
          ·
            refine ⟨1847476854477883338475571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19706419781097422277072757 1847476854477883338475571)
            ·
              refine ⟨2771215281716825007713357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847476854477883338475571 2771215281716825007713357)
              ·
                refine ⟨1039205730643809377892509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2771215281716825007713357 1039205730643809377892509)
                ·
                  refine ⟨389702148991428516709691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1039205730643809377892509 389702148991428516709691)
                  ·
                    rfl

theorem cell21_1707620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_1707620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707620 prefixEnd_1707620 := by exact prefixLift 1707620
  have htrace : WordTrace (prefixWord ++ tailWord_1707620) baseStart_1707620 baseEnd_1707620 := by
    simpa [prefixWord, tailWord_1707620, baseEnd_1707620] using wordTrace_append hprefix tailTrace_1707620
  have hstable : (prefixWord ++ tailWord_1707620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707620).length < 2 ^ (prefixWord ++ tailWord_1707620).sum := by decide
  have hdescent : baseEnd_1707620 < baseStart_1707620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707637 : List Nat := [1, 3, 4, 2, 1, 2, 3, 2, 3]
def baseStart_1707637 : Nat := 118140960795 + 1707637 * 2 ^ 59
def prefixEnd_1707637 : Nat := 4983230072969 + 3 ^ 40 * 1707637 * 2
def baseEnd_1707637 : Nat := 389706028623040264926323

theorem tailTrace_1707637 : CollatzResearch.WordTrace tailWord_1707637 prefixEnd_1707637 389706028623040264926323 := by
  unfold tailWord_1707637
  simp only [CollatzResearch.WordTrace]
  refine ⟨62282638114530265025969165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41521758743020176683979443 62282638114530265025969165)
  ·
    refine ⟨23355989292948849384738437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62282638114530265025969165 23355989292948849384738437)
    ·
      refine ⟨4379247992427909259638457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23355989292948849384738437 4379247992427909259638457)
      ·
        refine ⟨3284435994320931944728843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4379247992427909259638457 3284435994320931944728843)
        ·
          refine ⟨4926653991481397917093265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3284435994320931944728843 4926653991481397917093265)
          ·
            refine ⟨3694990493611048437819949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4926653991481397917093265 3694990493611048437819949)
            ·
              refine ⟨1385621435104143164182481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3694990493611048437819949 1385621435104143164182481)
              ·
                refine ⟨1039216076328107373136861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1385621435104143164182481 1039216076328107373136861)
                ·
                  refine ⟨389706028623040264926323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1039216076328107373136861 389706028623040264926323)
                  ·
                    rfl

theorem cell21_1707637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_1707637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707637 prefixEnd_1707637 := by exact prefixLift 1707637
  have htrace : WordTrace (prefixWord ++ tailWord_1707637) baseStart_1707637 baseEnd_1707637 := by
    simpa [prefixWord, tailWord_1707637, baseEnd_1707637] using wordTrace_append hprefix tailTrace_1707637
  have hstable : (prefixWord ++ tailWord_1707637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707637).length < 2 ^ (prefixWord ++ tailWord_1707637).sum := by decide
  have hdescent : baseEnd_1707637 < baseStart_1707637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707688 : List Nat := [2, 1, 7, 1, 2, 1, 2, 2, 3]
def baseStart_1707688 : Nat := 118140960795 + 1707688 * 2 ^ 59
def prefixEnd_1707688 : Nat := 4983230072969 + 3 ^ 40 * 1707688 * 2
def baseEnd_1707688 : Nat := 389717667517875509576219

theorem tailTrace_1707688 : CollatzResearch.WordTrace tailWord_1707688 prefixEnd_1707688 389717667517875509576219 := by
  unfold tailWord_1707688
  simp only [CollatzResearch.WordTrace]
  refine ⟨31142249118672750368037859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41522998824897000490717145 31142249118672750368037859)
  ·
    refine ⟨46713373678009125552056789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31142249118672750368037859 46713373678009125552056789)
    ·
      refine ⟨1094844695578338880126331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 46713373678009125552056789 1094844695578338880126331)
      ·
        refine ⟨1642267043367508320189497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094844695578338880126331 1642267043367508320189497)
        ·
          refine ⟨1231700282525631240142123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1642267043367508320189497 1231700282525631240142123)
          ·
            refine ⟨1847550423788446860213185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231700282525631240142123 1847550423788446860213185)
            ·
              refine ⟨1385662817841335145159889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1847550423788446860213185 1385662817841335145159889)
              ·
                refine ⟨1039247113381001358869917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1385662817841335145159889 1039247113381001358869917)
                ·
                  refine ⟨389717667517875509576219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1039247113381001358869917 389717667517875509576219)
                  ·
                    rfl

theorem cell21_1707688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 3].length) (baseStart_1707688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707688 prefixEnd_1707688 := by exact prefixLift 1707688
  have htrace : WordTrace (prefixWord ++ tailWord_1707688) baseStart_1707688 baseEnd_1707688 := by
    simpa [prefixWord, tailWord_1707688, baseEnd_1707688] using wordTrace_append hprefix tailTrace_1707688
  have hstable : (prefixWord ++ tailWord_1707688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707688).length < 2 ^ (prefixWord ++ tailWord_1707688).sum := by decide
  have hdescent : baseEnd_1707688 < baseStart_1707688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707806 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 5]
def baseStart_1707806 : Nat := 118140960795 + 1707806 * 2 ^ 59
def prefixEnd_1707806 : Nat := 4983230072969 + 3 ^ 40 * 1707806 * 2
def baseEnd_1707806 : Nat := 389744596725533526609311

theorem tailTrace_1707806 : CollatzResearch.WordTrace tailWord_1707806 prefixEnd_1707806 389744596725533526609311 := by
  unfold tailWord_1707806
  simp only [CollatzResearch.WordTrace]
  refine ⟨7786100256364750861108909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41525868033945337925914181 7786100256364750861108909)
  ·
    refine ⟨2919787596136781572915841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7786100256364750861108909 2919787596136781572915841)
    ·
      refine ⟨2189840697102586179686881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2919787596136781572915841 2189840697102586179686881)
      ·
        refine ⟨1642380522826939634765161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2189840697102586179686881 1642380522826939634765161)
        ·
          refine ⟨1231785392120204726073871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1642380522826939634765161 1231785392120204726073871)
          ·
            refine ⟨1847678088180307089110807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231785392120204726073871 1847678088180307089110807)
            ·
              refine ⟨2771517132270460633666211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847678088180307089110807 2771517132270460633666211)
              ·
                refine ⟨4157275698405690950499317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2771517132270460633666211 4157275698405690950499317)
                ·
                  refine ⟨389744596725533526609311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4157275698405690950499317 389744596725533526609311)
                  ·
                    rfl

theorem cell21_1707806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_1707806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707806 prefixEnd_1707806 := by exact prefixLift 1707806
  have htrace : WordTrace (prefixWord ++ tailWord_1707806) baseStart_1707806 baseEnd_1707806 := by
    simpa [prefixWord, tailWord_1707806, baseEnd_1707806] using wordTrace_append hprefix tailTrace_1707806
  have hstable : (prefixWord ++ tailWord_1707806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707806).length < 2 ^ (prefixWord ++ tailWord_1707806).sum := by decide
  have hdescent : baseEnd_1707806 < baseStart_1707806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707873 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 5]
def baseStart_1707873 : Nat := 118140960795 + 1707873 * 2 ^ 59
def prefixEnd_1707873 : Nat := 4983230072969 + 3 ^ 40 * 1707873 * 2
def baseEnd_1707873 : Nat := 389759887038356298992507

theorem tailTrace_1707873 : CollatzResearch.WordTrace tailWord_1707873 prefixEnd_1707873 389759887038356298992507 := by
  unfold tailWord_1707873
  simp only [CollatzResearch.WordTrace]
  refine ⟨62291245741675277331560273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41527497161116851554373515 62291245741675277331560273)
  ·
    refine ⟨46718434306256457998670205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62291245741675277331560273 46718434306256457998670205)
    ·
      refine ⟨17519412864846171749501327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46718434306256457998670205 17519412864846171749501327)
      ·
        refine ⟨26279119297269257624251991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17519412864846171749501327 26279119297269257624251991)
        ·
          refine ⟨39418678945903886436377987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26279119297269257624251991 39418678945903886436377987)
          ·
            refine ⟨59128018418855829654566981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39418678945903886436377987 59128018418855829654566981)
            ·
              refine ⟨11086503453535468060231309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59128018418855829654566981 11086503453535468060231309)
              ·
                refine ⟨4157438795075800522586741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11086503453535468060231309 4157438795075800522586741)
                ·
                  refine ⟨389759887038356298992507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4157438795075800522586741 389759887038356298992507)
                  ·
                    rfl

theorem cell21_1707873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_1707873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707873 prefixEnd_1707873 := by exact prefixLift 1707873
  have htrace : WordTrace (prefixWord ++ tailWord_1707873) baseStart_1707873 baseEnd_1707873 := by
    simpa [prefixWord, tailWord_1707873, baseEnd_1707873] using wordTrace_append hprefix tailTrace_1707873
  have hstable : (prefixWord ++ tailWord_1707873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707873).length < 2 ^ (prefixWord ++ tailWord_1707873).sum := by decide
  have hdescent : baseEnd_1707873 < baseStart_1707873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707876 : List Nat := [2, 3, 1, 1, 5, 2, 1, 6]
def baseStart_1707876 : Nat := 118140960795 + 1707876 * 2 ^ 59
def prefixEnd_1707876 : Nat := 4983230072969 + 3 ^ 40 * 1707876 * 2
def baseEnd_1707876 : Nat := 129920190559742986814167

theorem tailTrace_1707876 : CollatzResearch.WordTrace tailWord_1707876 prefixEnd_1707876 129920190559742986814167 := by
  unfold tailWord_1707876
  simp only [CollatzResearch.WordTrace]
  refine ⟨31145677580332204421959741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41527570107109605895946321 31145677580332204421959741)
  ·
    refine ⟨11679629092624576658234903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31145677580332204421959741 11679629092624576658234903)
    ·
      refine ⟨17519443638936864987352355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11679629092624576658234903 17519443638936864987352355)
      ·
        refine ⟨26279165458405297481028533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17519443638936864987352355 26279165458405297481028533)
        ·
          refine ⟨2463671761725496638846425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26279165458405297481028533 2463671761725496638846425)
          ·
            refine ⟨1847753821294122479134819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2463671761725496638846425 1847753821294122479134819)
            ·
              refine ⟨2771630731941183718702229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847753821294122479134819 2771630731941183718702229)
              ·
                refine ⟨129920190559742986814167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2771630731941183718702229 129920190559742986814167)
                ·
                  rfl

theorem cell21_1707876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 6].length) (baseStart_1707876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707876 prefixEnd_1707876 := by exact prefixLift 1707876
  have htrace : WordTrace (prefixWord ++ tailWord_1707876) baseStart_1707876 baseEnd_1707876 := by
    simpa [prefixWord, tailWord_1707876, baseEnd_1707876] using wordTrace_append hprefix tailTrace_1707876
  have hstable : (prefixWord ++ tailWord_1707876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707876).length < 2 ^ (prefixWord ++ tailWord_1707876).sum := by decide
  have hdescent : baseEnd_1707876 < baseStart_1707876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707887 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 10]
def baseStart_1707887 : Nat := 118140960795 + 1707887 * 2 ^ 59
def prefixEnd_1707887 : Nat := 4983230072969 + 3 ^ 40 * 1707887 * 2
def baseEnd_1707887 : Nat := 389763082029095385759145

theorem tailTrace_1707887 : CollatzResearch.WordTrace tailWord_1707887 prefixEnd_1707887 389763082029095385759145 := by
  unfold tailWord_1707887
  simp only [CollatzResearch.WordTrace]
  refine ⟨62291756363624557722569915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41527837575749705148379943 62291756363624557722569915)
  ·
    refine ⟨93437634545436836583854873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62291756363624557722569915 93437634545436836583854873)
    ·
      refine ⟨70078225909077627437891155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93437634545436836583854873 70078225909077627437891155)
      ·
        refine ⟨105117338863616441156836733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70078225909077627437891155 105117338863616441156836733)
        ·
          refine ⟨39419002073856165433813775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105117338863616441156836733 39419002073856165433813775)
          ·
            refine ⟨59128503110784248150720663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39419002073856165433813775 59128503110784248150720663)
            ·
              refine ⟨88692754666176372226080995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59128503110784248150720663 88692754666176372226080995)
              ·
                refine ⟨133039131999264558339121493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88692754666176372226080995 133039131999264558339121493)
                ·
                  refine ⟨389763082029095385759145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 133039131999264558339121493 389763082029095385759145)
                  ·
                    rfl

theorem cell21_1707887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 10].length) (baseStart_1707887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707887 prefixEnd_1707887 := by exact prefixLift 1707887
  have htrace : WordTrace (prefixWord ++ tailWord_1707887) baseStart_1707887 baseEnd_1707887 := by
    simpa [prefixWord, tailWord_1707887, baseEnd_1707887] using wordTrace_append hprefix tailTrace_1707887
  have hstable : (prefixWord ++ tailWord_1707887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707887).length < 2 ^ (prefixWord ++ tailWord_1707887).sum := by decide
  have hdescent : baseEnd_1707887 < baseStart_1707887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707907 : List Nat := [1, 1, 1, 3, 4, 3, 2, 3, 3]
def baseStart_1707907 : Nat := 118140960795 + 1707907 * 2 ^ 59
def prefixEnd_1707907 : Nat := 4983230072969 + 3 ^ 40 * 1707907 * 2
def baseEnd_1707907 : Nat := 389767646301579795425771

theorem tailTrace_1707907 : CollatzResearch.WordTrace tailWord_1707907 prefixEnd_1707907 389767646301579795425771 := by
  unfold tailWord_1707907
  simp only [CollatzResearch.WordTrace]
  refine ⟨62292485823552101138297975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41528323882368067425531983 62292485823552101138297975)
  ·
    refine ⟨93438728735328151707446963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62292485823552101138297975 93438728735328151707446963)
    ·
      refine ⟨140158093102992227561170445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93438728735328151707446963 140158093102992227561170445)
      ·
        refine ⟨52559284913622085335438917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140158093102992227561170445 52559284913622085335438917)
        ·
          refine ⟨9854865921304141000394797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52559284913622085335438917 9854865921304141000394797)
          ·
            refine ⟨3695574720489052875148049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9854865921304141000394797 3695574720489052875148049)
            ·
              refine ⟨2771681040366789656361037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3695574720489052875148049 2771681040366789656361037)
              ·
                refine ⟨1039380390137546121135389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2771681040366789656361037 1039380390137546121135389)
                ·
                  refine ⟨389767646301579795425771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1039380390137546121135389 389767646301579795425771)
                  ·
                    rfl

theorem cell21_1707907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 3].length) (baseStart_1707907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707907 prefixEnd_1707907 := by exact prefixLift 1707907
  have htrace : WordTrace (prefixWord ++ tailWord_1707907) baseStart_1707907 baseEnd_1707907 := by
    simpa [prefixWord, tailWord_1707907, baseEnd_1707907] using wordTrace_append hprefix tailTrace_1707907
  have hstable : (prefixWord ++ tailWord_1707907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707907).length < 2 ^ (prefixWord ++ tailWord_1707907).sum := by decide
  have hdescent : baseEnd_1707907 < baseStart_1707907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707963 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 6]
def baseStart_1707963 : Nat := 118140960795 + 1707963 * 2 ^ 59
def prefixEnd_1707963 : Nat := 4983230072969 + 3 ^ 40 * 1707963 * 2
def baseEnd_1707963 : Nat := 389780426264536142492323

theorem tailTrace_1707963 : CollatzResearch.WordTrace tailWord_1707963 prefixEnd_1707963 389780426264536142492323 := by
  unfold tailWord_1707963
  simp only [CollatzResearch.WordTrace]
  refine ⟨62294528311349222702336543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41529685540899481801557695 62294528311349222702336543)
  ·
    refine ⟨93441792467023834053504815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62294528311349222702336543 93441792467023834053504815)
    ·
      refine ⟨140162688700535751080257223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93441792467023834053504815 140162688700535751080257223)
      ·
        refine ⟨210244033050803626620385835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140162688700535751080257223 210244033050803626620385835)
        ·
          refine ⟨315366049576205439930578753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210244033050803626620385835 315366049576205439930578753)
          ·
            refine ⟨236524537182154079947934065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315366049576205439930578753 236524537182154079947934065)
            ·
              refine ⟨177393402886615559960950549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236524537182154079947934065 177393402886615559960950549)
              ·
                refine ⟨8315315760310104373169557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177393402886615559960950549 8315315760310104373169557)
                ·
                  refine ⟨389780426264536142492323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8315315760310104373169557 389780426264536142492323)
                  ·
                    rfl

theorem cell21_1707963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 6].length) (baseStart_1707963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707963 prefixEnd_1707963 := by exact prefixLift 1707963
  have htrace : WordTrace (prefixWord ++ tailWord_1707963) baseStart_1707963 baseEnd_1707963 := by
    simpa [prefixWord, tailWord_1707963, baseEnd_1707963] using wordTrace_append hprefix tailTrace_1707963
  have hstable : (prefixWord ++ tailWord_1707963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707963).length < 2 ^ (prefixWord ++ tailWord_1707963).sum := by decide
  have hdescent : baseEnd_1707963 < baseStart_1707963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707980 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 6]
def baseStart_1707980 : Nat := 118140960795 + 1707980 * 2 ^ 59
def prefixEnd_1707980 : Nat := 4983230072969 + 3 ^ 40 * 1707980 * 2
def baseEnd_1707980 : Nat := 389784305896147890708955

theorem tailTrace_1707980 : CollatzResearch.WordTrace tailWord_1707980 prefixEnd_1707980 389784305896147890708955 := by
  unfold tailWord_1707980
  simp only [CollatzResearch.WordTrace]
  refine ⟨31147574176143817302852697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41530098901525089737136929 31147574176143817302852697)
  ·
    refine ⟨23360680632107862977139523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31147574176143817302852697 23360680632107862977139523)
    ·
      refine ⟨35041020948161794465709285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23360680632107862977139523 35041020948161794465709285)
      ·
        refine ⟨6570191427780336462320491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35041020948161794465709285 6570191427780336462320491)
        ·
          refine ⟨9855287141670504693480737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6570191427780336462320491 9855287141670504693480737)
          ·
            refine ⟨7391465356252878520110553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9855287141670504693480737 7391465356252878520110553)
            ·
              refine ⟨5543599017189658890082915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7391465356252878520110553 5543599017189658890082915)
              ·
                refine ⟨8315398525784488335124373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5543599017189658890082915 8315398525784488335124373)
                ·
                  refine ⟨389784305896147890708955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8315398525784488335124373 389784305896147890708955)
                  ·
                    rfl

theorem cell21_1707980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_1707980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707980 prefixEnd_1707980 := by exact prefixLift 1707980
  have htrace : WordTrace (prefixWord ++ tailWord_1707980) baseStart_1707980 baseEnd_1707980 := by
    simpa [prefixWord, tailWord_1707980, baseEnd_1707980] using wordTrace_append hprefix tailTrace_1707980
  have hstable : (prefixWord ++ tailWord_1707980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707980).length < 2 ^ (prefixWord ++ tailWord_1707980).sum := by decide
  have hdescent : baseEnd_1707980 < baseStart_1707980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707983 : List Nat := [1, 1, 2, 1, 1, 5, 5, 2, 3]
def baseStart_1707983 : Nat := 118140960795 + 1707983 * 2 ^ 59
def prefixEnd_1707983 : Nat := 4983230072969 + 3 ^ 40 * 1707983 * 2
def baseEnd_1707983 : Nat := 389784990537020552158949

theorem tailTrace_1707983 : CollatzResearch.WordTrace tailWord_1707983 prefixEnd_1707983 389784990537020552158949 := by
  unfold tailWord_1707983
  simp only [CollatzResearch.WordTrace]
  refine ⟨62295257771276766118064603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41530171847517844078709735 62295257771276766118064603)
  ·
    refine ⟨93442886656915149177096905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62295257771276766118064603 93442886656915149177096905)
    ·
      refine ⟨70082164992686361882822679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93442886656915149177096905 70082164992686361882822679)
      ·
        refine ⟨105123247489029542824234019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70082164992686361882822679 105123247489029542824234019)
        ·
          refine ⟨157684871233544314236351029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105123247489029542824234019 157684871233544314236351029)
          ·
            refine ⟨14782956678144779459657909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157684871233544314236351029 14782956678144779459657909)
            ·
              refine ⟨1385902188576073074342929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14782956678144779459657909 1385902188576073074342929)
              ·
                refine ⟨1039426641432054805757197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1385902188576073074342929 1039426641432054805757197)
                ·
                  refine ⟨389784990537020552158949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1039426641432054805757197 389784990537020552158949)
                  ·
                    rfl

theorem cell21_1707983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 3].length) (baseStart_1707983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707983 prefixEnd_1707983 := by exact prefixLift 1707983
  have htrace : WordTrace (prefixWord ++ tailWord_1707983) baseStart_1707983 baseEnd_1707983 := by
    simpa [prefixWord, tailWord_1707983, baseEnd_1707983] using wordTrace_append hprefix tailTrace_1707983
  have hstable : (prefixWord ++ tailWord_1707983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707983).length < 2 ^ (prefixWord ++ tailWord_1707983).sum := by decide
  have hdescent : baseEnd_1707983 < baseStart_1707983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708056 : List Nat := [2, 1, 2, 3, 2, 1, 1, 5, 4]
def baseStart_1708056 : Nat := 118140960795 + 1708056 * 2 ^ 59
def prefixEnd_1708056 : Nat := 4983230072969 + 3 ^ 40 * 1708056 * 2
def baseEnd_1708056 : Nat := 389801650131588647442133

theorem tailTrace_1708056 : CollatzResearch.WordTrace tailWord_1708056 prefixEnd_1708056 389801650131588647442133 := by
  unfold tailWord_1708056
  simp only [CollatzResearch.WordTrace]
  refine ⟨31148960150006149792736011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41531946866674866390314681 31148960150006149792736011)
  ·
    refine ⟨46723440225009224689104017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31148960150006149792736011 46723440225009224689104017)
    ·
      refine ⟨35042580168756918516828013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46723440225009224689104017 35042580168756918516828013)
      ·
        refine ⟨13140967563283844443810505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35042580168756918516828013 13140967563283844443810505)
        ·
          refine ⟨9855725672462883332857879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13140967563283844443810505 9855725672462883332857879)
          ·
            refine ⟨14783588508694324999286819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9855725672462883332857879 14783588508694324999286819)
            ·
              refine ⟨22175382763041487498930229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14783588508694324999286819 22175382763041487498930229)
              ·
                refine ⟨2078942134035139453024709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22175382763041487498930229 2078942134035139453024709)
                ·
                  refine ⟨389801650131588647442133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2078942134035139453024709 389801650131588647442133)
                  ·
                    rfl

theorem cell21_1708056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_1708056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708056 prefixEnd_1708056 := by exact prefixLift 1708056
  have htrace : WordTrace (prefixWord ++ tailWord_1708056) baseStart_1708056 baseEnd_1708056 := by
    simpa [prefixWord, tailWord_1708056, baseEnd_1708056] using wordTrace_append hprefix tailTrace_1708056
  have hstable : (prefixWord ++ tailWord_1708056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708056).length < 2 ^ (prefixWord ++ tailWord_1708056).sum := by decide
  have hdescent : baseEnd_1708056 < baseStart_1708056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708146 : List Nat := [3, 2, 1, 2, 2, 2, 9]
def baseStart_1708146 : Nat := 118140960795 + 1708146 * 2 ^ 59
def prefixEnd_1708146 : Nat := 4983230072969 + 3 ^ 40 * 1708146 * 2
def baseEnd_1708146 : Nat := 43313576595307610104661

theorem tailTrace_1708146 : CollatzResearch.WordTrace tailWord_1708146 prefixEnd_1708146 43313576595307610104661 := by
  unfold tailWord_1708146
  simp only [CollatzResearch.WordTrace]
  refine ⟨15575300717421561239062073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41534135246457496637498861 15575300717421561239062073)
  ·
    refine ⟨11681475538066170929296555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15575300717421561239062073 11681475538066170929296555)
    ·
      refine ⟨17522213307099256393944833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11681475538066170929296555 17522213307099256393944833)
      ·
        refine ⟨13141659980324442295458625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17522213307099256393944833 13141659980324442295458625)
        ·
          refine ⟨9856244985243331721593969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13141659980324442295458625 9856244985243331721593969)
          ·
            refine ⟨7392183738932498791195477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9856244985243331721593969 7392183738932498791195477)
            ·
              refine ⟨43313576595307610104661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7392183738932498791195477 43313576595307610104661)
              ·
                rfl

theorem cell21_1708146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 9].length) (baseStart_1708146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708146 prefixEnd_1708146 := by exact prefixLift 1708146
  have htrace : WordTrace (prefixWord ++ tailWord_1708146) baseStart_1708146 baseEnd_1708146 := by
    simpa [prefixWord, tailWord_1708146, baseEnd_1708146] using wordTrace_append hprefix tailTrace_1708146
  have hstable : (prefixWord ++ tailWord_1708146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708146).length < 2 ^ (prefixWord ++ tailWord_1708146).sum := by decide
  have hdescent : baseEnd_1708146 < baseStart_1708146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708259 : List Nat := [1, 1, 1, 8, 2, 1, 1, 2, 4]
def baseStart_1708259 : Nat := 118140960795 + 1708259 * 2 ^ 59
def prefixEnd_1708259 : Nat := 4983230072969 + 3 ^ 40 * 1708259 * 2
def baseEnd_1708259 : Nat := 389847977497305405558385

theorem tailTrace_1708259 : CollatzResearch.WordTrace tailWord_1708259 prefixEnd_1708259 389847977497305405558385 := by
  unfold tailWord_1708259
  simp only [CollatzResearch.WordTrace]
  refine ⟨62305324318276865255111831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41536882878851243503407887 62305324318276865255111831)
  ·
    refine ⟨93457986477415297882667747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62305324318276865255111831 93457986477415297882667747)
    ·
      refine ⟨140186979716122946824001621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93457986477415297882667747 140186979716122946824001621)
      ·
        refine ⟨1642816168548315783093769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 140186979716122946824001621 1642816168548315783093769)
        ·
          refine ⟨1232112126411236837320327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1642816168548315783093769 1232112126411236837320327)
          ·
            refine ⟨1848168189616855255980491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232112126411236837320327 1848168189616855255980491)
            ·
              refine ⟨2772252284425282883970737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848168189616855255980491 2772252284425282883970737)
              ·
                refine ⟨2079189213318962162978053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2772252284425282883970737 2079189213318962162978053)
                ·
                  refine ⟨389847977497305405558385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079189213318962162978053 389847977497305405558385)
                  ·
                    rfl

theorem cell21_1708259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 4].length) (baseStart_1708259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708259 prefixEnd_1708259 := by exact prefixLift 1708259
  have htrace : WordTrace (prefixWord ++ tailWord_1708259) baseStart_1708259 baseEnd_1708259 := by
    simpa [prefixWord, tailWord_1708259, baseEnd_1708259] using wordTrace_append hprefix tailTrace_1708259
  have hstable : (prefixWord ++ tailWord_1708259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708259).length < 2 ^ (prefixWord ++ tailWord_1708259).sum := by decide
  have hdescent : baseEnd_1708259 < baseStart_1708259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708267 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 6]
def baseStart_1708267 : Nat := 118140960795 + 1708267 * 2 ^ 59
def prefixEnd_1708267 : Nat := 4983230072969 + 3 ^ 40 * 1708267 * 2
def baseEnd_1708267 : Nat := 389849803206299169425035

theorem tailTrace_1708267 : CollatzResearch.WordTrace tailWord_1708267 prefixEnd_1708267 389849803206299169425035 := by
  unfold tailWord_1708267
  simp only [CollatzResearch.WordTrace]
  refine ⟨62305616102247882621403055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41537077401498588414268703 62305616102247882621403055)
  ·
    refine ⟨93458424153371823932104583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62305616102247882621403055 93458424153371823932104583)
    ·
      refine ⟨140187636230057735898156875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93458424153371823932104583 140187636230057735898156875)
      ·
        refine ⟨210281454345086603847235313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140187636230057735898156875 210281454345086603847235313)
        ·
          refine ⟨157711090758814952885426485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210281454345086603847235313 157711090758814952885426485)
          ·
            refine ⟨14785414758638901833008733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157711090758814952885426485 14785414758638901833008733)
            ·
              refine ⟨5544530534489588187378275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14785414758638901833008733 5544530534489588187378275)
              ·
                refine ⟨8316795801734382281067413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5544530534489588187378275 8316795801734382281067413)
                ·
                  refine ⟨389849803206299169425035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8316795801734382281067413 389849803206299169425035)
                  ·
                    rfl

theorem cell21_1708267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 6].length) (baseStart_1708267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708267 prefixEnd_1708267 := by exact prefixLift 1708267
  have htrace : WordTrace (prefixWord ++ tailWord_1708267) baseStart_1708267 baseEnd_1708267 := by
    simpa [prefixWord, tailWord_1708267, baseEnd_1708267] using wordTrace_append hprefix tailTrace_1708267
  have hstable : (prefixWord ++ tailWord_1708267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708267).length < 2 ^ (prefixWord ++ tailWord_1708267).sum := by decide
  have hdescent : baseEnd_1708267 < baseStart_1708267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708380 : List Nat := [2, 2, 4, 3, 1, 1, 1, 4, 3]
def baseStart_1708380 : Nat := 118140960795 + 1708380 * 2 ^ 59
def prefixEnd_1708380 : Nat := 4983230072969 + 3 ^ 40 * 1708380 * 2
def baseEnd_1708380 : Nat := 389875591345836084041471

theorem tailTrace_1708380 : CollatzResearch.WordTrace tailWord_1708380 prefixEnd_1708380 389875591345836084041471 := by
  unfold tailWord_1708380
  simp only [CollatzResearch.WordTrace]
  refine ⟨31154868775419251460133297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41539825033892335280177729 31154868775419251460133297)
  ·
    refine ⟨23366151581564438595099973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31154868775419251460133297 23366151581564438595099973)
    ·
      refine ⟨4381153421543332236581245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23366151581564438595099973 4381153421543332236581245)
      ·
        refine ⟨1642932533078749588717967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4381153421543332236581245 1642932533078749588717967)
        ·
          refine ⟨2464398799618124383076951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1642932533078749588717967 2464398799618124383076951)
          ·
            refine ⟨3696598199427186574615427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2464398799618124383076951 3696598199427186574615427)
            ·
              refine ⟨5544897299140779861923141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3696598199427186574615427 5544897299140779861923141)
              ·
                refine ⟨1039668243588896224110589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5544897299140779861923141 1039668243588896224110589)
                ·
                  refine ⟨389875591345836084041471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1039668243588896224110589 389875591345836084041471)
                  ·
                    rfl

theorem cell21_1708380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_1708380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708380 prefixEnd_1708380 := by exact prefixLift 1708380
  have htrace : WordTrace (prefixWord ++ tailWord_1708380) baseStart_1708380 baseEnd_1708380 := by
    simpa [prefixWord, tailWord_1708380, baseEnd_1708380] using wordTrace_append hprefix tailTrace_1708380
  have hstable : (prefixWord ++ tailWord_1708380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708380).length < 2 ^ (prefixWord ++ tailWord_1708380).sum := by decide
  have hdescent : baseEnd_1708380 < baseStart_1708380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708391 : List Nat := [1, 1, 5, 1, 3, 3, 1, 6]
def baseStart_1708391 : Nat := 118140960795 + 1708391 * 2 ^ 59
def prefixEnd_1708391 : Nat := 4983230072969 + 3 ^ 40 * 1708391 * 2
def baseEnd_1708391 : Nat := 129959367231900836452705

theorem tailTrace_1708391 : CollatzResearch.WordTrace tailWord_1708391 prefixEnd_1708391 129959367231900836452705 := by
  unfold tailWord_1708391
  simp only [CollatzResearch.WordTrace]
  refine ⟨62310138753798651798917027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41540092502532434532611351 62310138753798651798917027)
  ·
    refine ⟨93465208130697977698375541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62310138753798651798917027 93465208130697977698375541)
    ·
      refine ⟨8762363262252935409222707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93465208130697977698375541 8762363262252935409222707)
      ·
        refine ⟨13143544893379403113834061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8762363262252935409222707 13143544893379403113834061)
        ·
          refine ⟨4928829335017276167687773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13143544893379403113834061 4928829335017276167687773)
          ·
            refine ⟨1848311000631478562882915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4928829335017276167687773 1848311000631478562882915)
            ·
              refine ⟨2772466500947217844324373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848311000631478562882915 2772466500947217844324373)
              ·
                refine ⟨129959367231900836452705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2772466500947217844324373 129959367231900836452705)
                ·
                  rfl

theorem cell21_1708391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 6].length) (baseStart_1708391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708391 prefixEnd_1708391 := by exact prefixLift 1708391
  have htrace : WordTrace (prefixWord ++ tailWord_1708391) baseStart_1708391 baseEnd_1708391 := by
    simpa [prefixWord, tailWord_1708391, baseEnd_1708391] using wordTrace_append hprefix tailTrace_1708391
  have hstable : (prefixWord ++ tailWord_1708391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708391).length < 2 ^ (prefixWord ++ tailWord_1708391).sum := by decide
  have hdescent : baseEnd_1708391 < baseStart_1708391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708405 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 7]
def baseStart_1708405 : Nat := 118140960795 + 1708405 * 2 ^ 59
def prefixEnd_1708405 : Nat := 4983230072969 + 3 ^ 40 * 1708405 * 2
def baseEnd_1708405 : Nat := 389881296686441596124753

theorem tailTrace_1708405 : CollatzResearch.WordTrace tailWord_1708405 prefixEnd_1708405 389881296686441596124753 := by
  unfold tailWord_1708405
  simp only [CollatzResearch.WordTrace]
  refine ⟨62310649375747932189926669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41540432917165288126617779 62310649375747932189926669)
  ·
    refine ⟨23366493515905474571222501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62310649375747932189926669 23366493515905474571222501)
    ·
      refine ⟨4381217534232276482104219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23366493515905474571222501 4381217534232276482104219)
      ·
        refine ⟨6571826301348414723156329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4381217534232276482104219 6571826301348414723156329)
        ·
          refine ⟨4928869726011311042367247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6571826301348414723156329 4928869726011311042367247)
          ·
            refine ⟨7393304589016966563550871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4928869726011311042367247 7393304589016966563550871)
            ·
              refine ⟨11089956883525449845326307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7393304589016966563550871 11089956883525449845326307)
              ·
                refine ⟨16634935325288174767989461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11089956883525449845326307 16634935325288174767989461)
                ·
                  refine ⟨389881296686441596124753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16634935325288174767989461 389881296686441596124753)
                  ·
                    rfl

theorem cell21_1708405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_1708405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708405 prefixEnd_1708405 := by exact prefixLift 1708405
  have htrace : WordTrace (prefixWord ++ tailWord_1708405) baseStart_1708405 baseEnd_1708405 := by
    simpa [prefixWord, tailWord_1708405, baseEnd_1708405] using wordTrace_append hprefix tailTrace_1708405
  have hstable : (prefixWord ++ tailWord_1708405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708405).length < 2 ^ (prefixWord ++ tailWord_1708405).sum := by decide
  have hdescent : baseEnd_1708405 < baseStart_1708405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708450 : List Nat := [3, 3, 1, 2, 1, 1, 2, 8]
def baseStart_1708450 : Nat := 118140960795 + 1708450 * 2 ^ 59
def prefixEnd_1708450 : Nat := 4983230072969 + 3 ^ 40 * 1708450 * 2
def baseEnd_1708450 : Nat := 129963855433177172624887

theorem tailTrace_1708450 : CollatzResearch.WordTrace tailWord_1708450 prefixEnd_1708450 129963855433177172624887 := by
  unfold tailWord_1708450
  simp only [CollatzResearch.WordTrace]
  refine ⟨15578072665146226218828701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41541527107056603250209869 15578072665146226218828701)
  ·
    refine ⟨5841777249429834832060763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15578072665146226218828701 5841777249429834832060763)
    ·
      refine ⟨8762665874144752248091145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5841777249429834832060763 8762665874144752248091145)
      ·
        refine ⟨6571999405608564186068359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8762665874144752248091145 6571999405608564186068359)
        ·
          refine ⟨9857999108412846279102539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6571999405608564186068359 9857999108412846279102539)
          ·
            refine ⟨14786998662619269418653809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9857999108412846279102539 14786998662619269418653809)
            ·
              refine ⟨11090248996964452063990357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14786998662619269418653809 11090248996964452063990357)
              ·
                refine ⟨129963855433177172624887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11090248996964452063990357 129963855433177172624887)
                ·
                  rfl

theorem cell21_1708450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_1708450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708450 prefixEnd_1708450 := by exact prefixLift 1708450
  have htrace : WordTrace (prefixWord ++ tailWord_1708450) baseStart_1708450 baseEnd_1708450 := by
    simpa [prefixWord, tailWord_1708450, baseEnd_1708450] using wordTrace_append hprefix tailTrace_1708450
  have hstable : (prefixWord ++ tailWord_1708450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708450).length < 2 ^ (prefixWord ++ tailWord_1708450).sum := by decide
  have hdescent : baseEnd_1708450 < baseStart_1708450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708484 : List Nat := [2, 3, 3, 2, 3, 1, 7]
def baseStart_1708484 : Nat := 118140960795 + 1708484 * 2 ^ 59
def prefixEnd_1708484 : Nat := 4983230072969 + 3 ^ 40 * 1708484 * 2
def baseEnd_1708484 : Nat := 43322147284750557145325

theorem tailTrace_1708484 : CollatzResearch.WordTrace tailWord_1708484 prefixEnd_1708484 43322147284750557145325 := by
  unfold tailWord_1708484
  simp only [CollatzResearch.WordTrace]
  refine ⟨31156765371230864341026253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41542353828307819121368337 31156765371230864341026253)
  ·
    refine ⟨11683787014211574127884845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31156765371230864341026253 11683787014211574127884845)
    ·
      refine ⟨4381420130329340297956817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11683787014211574127884845 4381420130329340297956817)
      ·
        refine ⟨3286065097747005223467613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4381420130329340297956817 3286065097747005223467613)
        ·
          refine ⟨1232274411655126958800355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3286065097747005223467613 1232274411655126958800355)
          ·
            refine ⟨1848411617482690438200533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232274411655126958800355 1848411617482690438200533)
            ·
              refine ⟨43322147284750557145325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1848411617482690438200533 43322147284750557145325)
              ·
                rfl

theorem cell21_1708484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 7].length) (baseStart_1708484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708484 prefixEnd_1708484 := by exact prefixLift 1708484
  have htrace : WordTrace (prefixWord ++ tailWord_1708484) baseStart_1708484 baseEnd_1708484 := by
    simpa [prefixWord, tailWord_1708484, baseEnd_1708484] using wordTrace_append hprefix tailTrace_1708484
  have hstable : (prefixWord ++ tailWord_1708484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708484).length < 2 ^ (prefixWord ++ tailWord_1708484).sum := by decide
  have hdescent : baseEnd_1708484 < baseStart_1708484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708495 : List Nat := [1, 1, 2, 1, 1, 4, 1, 6, 4]
def baseStart_1708495 : Nat := 118140960795 + 1708495 * 2 ^ 59
def prefixEnd_1708495 : Nat := 4983230072969 + 3 ^ 40 * 1708495 * 2
def baseEnd_1708495 : Nat := 389901835912621439624569

theorem tailTrace_1708495 : CollatzResearch.WordTrace tailWord_1708495 prefixEnd_1708495 389901835912621439624569 := by
  unfold tailWord_1708495
  simp only [CollatzResearch.WordTrace]
  refine ⟨62313931945421877560702939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41542621296947918373801959 62313931945421877560702939)
  ·
    refine ⟨93470897918132816341054409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62313931945421877560702939 93470897918132816341054409)
    ·
      refine ⟨70103173438599612255790807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93470897918132816341054409 70103173438599612255790807)
      ·
        refine ⟨105154760157899418383686211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70103173438599612255790807 105154760157899418383686211)
        ·
          refine ⟨157732140236849127575529317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105154760157899418383686211 157732140236849127575529317)
          ·
            refine ⟨29574776294409211420411747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157732140236849127575529317 29574776294409211420411747)
            ·
              refine ⟨44362164441613817130617621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29574776294409211420411747 44362164441613817130617621)
              ·
                refine ⟨2079476458200647677997701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44362164441613817130617621 2079476458200647677997701)
                ·
                  refine ⟨389901835912621439624569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079476458200647677997701 389901835912621439624569)
                  ·
                    rfl

theorem cell21_1708495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 4].length) (baseStart_1708495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708495 prefixEnd_1708495 := by exact prefixLift 1708495
  have htrace : WordTrace (prefixWord ++ tailWord_1708495) baseStart_1708495 baseEnd_1708495 := by
    simpa [prefixWord, tailWord_1708495, baseEnd_1708495] using wordTrace_append hprefix tailTrace_1708495
  have hstable : (prefixWord ++ tailWord_1708495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708495).length < 2 ^ (prefixWord ++ tailWord_1708495).sum := by decide
  have hdescent : baseEnd_1708495 < baseStart_1708495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708526 : List Nat := [4, 1, 2, 1, 2, 2, 2, 7]
def baseStart_1708526 : Nat := 118140960795 + 1708526 * 2 ^ 59
def prefixEnd_1708526 : Nat := 4983230072969 + 3 ^ 40 * 1708526 * 2
def baseEnd_1708526 : Nat := 129969636844990758202613

theorem tailTrace_1708526 : CollatzResearch.WordTrace tailWord_1708526 prefixEnd_1708526 129969636844990758202613 := by
  unfold tailWord_1708526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7789382826038696231885179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41543375072206379903387621 7789382826038696231885179)
  ·
    refine ⟨11684074239058044347827769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7789382826038696231885179 11684074239058044347827769)
    ·
      refine ⟨8763055679293533260870827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11684074239058044347827769 8763055679293533260870827)
      ·
        refine ⟨13144583518940299891306241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8763055679293533260870827 13144583518940299891306241)
        ·
          refine ⟨9858437639205224918479681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13144583518940299891306241 9858437639205224918479681)
          ·
            refine ⟨7393828229403918688859761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9858437639205224918479681 7393828229403918688859761)
            ·
              refine ⟨5545371172052939016644821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7393828229403918688859761 5545371172052939016644821)
              ·
                refine ⟨129969636844990758202613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5545371172052939016644821 129969636844990758202613)
                ·
                  rfl

theorem cell21_1708526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_1708526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708526 prefixEnd_1708526 := by exact prefixLift 1708526
  have htrace : WordTrace (prefixWord ++ tailWord_1708526) baseStart_1708526 baseEnd_1708526 := by
    simpa [prefixWord, tailWord_1708526, baseEnd_1708526] using wordTrace_append hprefix tailTrace_1708526
  have hstable : (prefixWord ++ tailWord_1708526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708526).length < 2 ^ (prefixWord ++ tailWord_1708526).sum := by decide
  have hdescent : baseEnd_1708526 < baseStart_1708526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708546 : List Nat := [3, 4, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1708546 : Nat := 118140960795 + 1708546 * 2 ^ 59
def prefixEnd_1708546 : Nat := 4983230072969 + 3 ^ 40 * 1708546 * 2
def baseEnd_1708546 : Nat := 389913474807456684274465

theorem tailTrace_1708546 : CollatzResearch.WordTrace tailWord_1708546 prefixEnd_1708546 389913474807456684274465 := by
  unfold tailWord_1708546
  simp only [CollatzResearch.WordTrace]
  refine ⟨15578948017059278317702373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41543861378824742180539661 15578948017059278317702373)
  ·
    refine ⟨2921052753198614684569195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15578948017059278317702373 2921052753198614684569195)
    ·
      refine ⟨4381579129797922026853793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2921052753198614684569195 4381579129797922026853793)
      ·
        refine ⟨3286184347348441520140345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4381579129797922026853793 3286184347348441520140345)
        ·
          refine ⟨2464638260511331140105259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3286184347348441520140345 2464638260511331140105259)
          ·
            refine ⟨3696957390766996710157889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2464638260511331140105259 3696957390766996710157889)
            ·
              refine ⟨2772718043075247532618417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3696957390766996710157889 2772718043075247532618417)
              ·
                refine ⟨2079538532306435649463813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2772718043075247532618417 2079538532306435649463813)
                ·
                  refine ⟨389913474807456684274465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079538532306435649463813 389913474807456684274465)
                  ·
                    rfl

theorem cell21_1708546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1708546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708546 prefixEnd_1708546 := by exact prefixLift 1708546
  have htrace : WordTrace (prefixWord ++ tailWord_1708546) baseStart_1708546 baseEnd_1708546 := by
    simpa [prefixWord, tailWord_1708546, baseEnd_1708546] using wordTrace_append hprefix tailTrace_1708546
  have hstable : (prefixWord ++ tailWord_1708546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708546).length < 2 ^ (prefixWord ++ tailWord_1708546).sum := by decide
  have hdescent : baseEnd_1708546 < baseStart_1708546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708605 : List Nat := [1, 4, 1, 3, 2, 3, 1, 2, 4]
def baseStart_1708605 : Nat := 118140960795 + 1708605 * 2 ^ 59
def prefixEnd_1708605 : Nat := 4983230072969 + 3 ^ 40 * 1708605 * 2
def baseEnd_1708605 : Nat := 389926939411285692791011

theorem tailTrace_1708605 : CollatzResearch.WordTrace tailWord_1708605 prefixEnd_1708605 389926939411285692791011 := by
  unfold tailWord_1708605
  simp only [CollatzResearch.WordTrace]
  refine ⟨62317943975023366347207269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41545295983348910898138179 62317943975023366347207269)
  ·
    refine ⟨11684614495316881190101363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62317943975023366347207269 11684614495316881190101363)
    ·
      refine ⟨17526921742975321785152045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11684614495316881190101363 17526921742975321785152045)
      ·
        refine ⟨6572595653615745669432017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17526921742975321785152045 6572595653615745669432017)
        ·
          refine ⟨4929446740211809252074013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6572595653615745669432017 4929446740211809252074013)
          ·
            refine ⟨1848542527579428469527755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4929446740211809252074013 1848542527579428469527755)
            ·
              refine ⟨2772813791369142704291633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848542527579428469527755 2772813791369142704291633)
              ·
                refine ⟨2079610343526857028218725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2772813791369142704291633 2079610343526857028218725)
                ·
                  refine ⟨389926939411285692791011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079610343526857028218725 389926939411285692791011)
                  ·
                    rfl

theorem cell21_1708605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_1708605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708605 prefixEnd_1708605 := by exact prefixLift 1708605
  have htrace : WordTrace (prefixWord ++ tailWord_1708605) baseStart_1708605 baseEnd_1708605 := by
    simpa [prefixWord, tailWord_1708605, baseEnd_1708605] using wordTrace_append hprefix tailTrace_1708605
  have hstable : (prefixWord ++ tailWord_1708605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708605).length < 2 ^ (prefixWord ++ tailWord_1708605).sum := by decide
  have hdescent : baseEnd_1708605 < baseStart_1708605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708636 : List Nat := [2, 2, 4, 1, 3, 2, 2, 5]
def baseStart_1708636 : Nat := 118140960795 + 1708636 * 2 ^ 59
def prefixEnd_1708636 : Nat := 4983230072969 + 3 ^ 40 * 1708636 * 2
def baseEnd_1708636 : Nat := 129978004677878842591427

theorem tailTrace_1708636 : CollatzResearch.WordTrace tailWord_1708636 prefixEnd_1708636 129978004677878842591427 := by
  unfold tailWord_1708636
  simp only [CollatzResearch.WordTrace]
  refine ⟨31159537318955529320792881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41546049758607372427723841 31159537318955529320792881)
  ·
    refine ⟨23369652989216646990594661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31159537318955529320792881 23369652989216646990594661)
    ·
      refine ⟨4381809935478121310736499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23369652989216646990594661 4381809935478121310736499)
      ·
        refine ⟨6572714903217181966104749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4381809935478121310736499 6572714903217181966104749)
        ·
          refine ⟨2464768088706443237289281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6572714903217181966104749 2464768088706443237289281)
          ·
            refine ⟨1848576066529832427966961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2464768088706443237289281 1848576066529832427966961)
            ·
              refine ⟨1386432049897374320975221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1848576066529832427966961 1386432049897374320975221)
              ·
                refine ⟨129978004677878842591427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1386432049897374320975221 129978004677878842591427)
                ·
                  rfl

theorem cell21_1708636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 5].length) (baseStart_1708636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708636 prefixEnd_1708636 := by exact prefixLift 1708636
  have htrace : WordTrace (prefixWord ++ tailWord_1708636) baseStart_1708636 baseEnd_1708636 := by
    simpa [prefixWord, tailWord_1708636, baseEnd_1708636] using wordTrace_append hprefix tailTrace_1708636
  have hstable : (prefixWord ++ tailWord_1708636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708636).length < 2 ^ (prefixWord ++ tailWord_1708636).sum := by decide
  have hdescent : baseEnd_1708636 < baseStart_1708636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708709 : List Nat := [1, 3, 1, 2, 1, 2, 1, 7, 3]
def baseStart_1708709 : Nat := 118140960795 + 1708709 * 2 ^ 59
def prefixEnd_1708709 : Nat := 4983230072969 + 3 ^ 40 * 1708709 * 2
def baseEnd_1708709 : Nat := 389950673628204623057465

theorem tailTrace_1708709 : CollatzResearch.WordTrace tailWord_1708709 prefixEnd_1708709 389950673628204623057465 := by
  unfold tailWord_1708709
  simp only [CollatzResearch.WordTrace]
  refine ⟨62321737166646592108993181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41547824777764394739328787 62321737166646592108993181)
  ·
    refine ⟨23370651437492472040872443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62321737166646592108993181 23370651437492472040872443)
    ·
      refine ⟨35055977156238708061308665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23370651437492472040872443 35055977156238708061308665)
      ·
        refine ⟨26291982867179031045981499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35055977156238708061308665 26291982867179031045981499)
        ·
          refine ⟨39437974300768546568972249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26291982867179031045981499 39437974300768546568972249)
          ·
            refine ⟨29578480725576409926729187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39437974300768546568972249 29578480725576409926729187)
            ·
              refine ⟨44367721088364614890093781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29578480725576409926729187 44367721088364614890093781)
              ·
                refine ⟨1039868463008545661486573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 44367721088364614890093781 1039868463008545661486573)
                ·
                  refine ⟨389950673628204623057465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1039868463008545661486573 389950673628204623057465)
                  ·
                    rfl

theorem cell21_1708709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_1708709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708709 prefixEnd_1708709 := by exact prefixLift 1708709
  have htrace : WordTrace (prefixWord ++ tailWord_1708709) baseStart_1708709 baseEnd_1708709 := by
    simpa [prefixWord, tailWord_1708709, baseEnd_1708709] using wordTrace_append hprefix tailTrace_1708709
  have hstable : (prefixWord ++ tailWord_1708709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708709).length < 2 ^ (prefixWord ++ tailWord_1708709).sum := by decide
  have hdescent : baseEnd_1708709 < baseStart_1708709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708723 : List Nat := [1, 1, 1, 2, 3, 4, 1, 4, 4]
def baseStart_1708723 : Nat := 118140960795 + 1708723 * 2 ^ 59
def prefixEnd_1708723 : Nat := 4983230072969 + 3 ^ 40 * 1708723 * 2
def baseEnd_1708723 : Nat := 389953868618943709824103

theorem tailTrace_1708723 : CollatzResearch.WordTrace tailWord_1708723 prefixEnd_1708723 389953868618943709824103 := by
  unfold tailWord_1708723
  simp only [CollatzResearch.WordTrace]
  refine ⟨62322247788595872500002823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41548165192397248333335215 62322247788595872500002823)
  ·
    refine ⟨93483371682893808750004235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62322247788595872500002823 93483371682893808750004235)
    ·
      refine ⟨140225057524340713125006353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93483371682893808750004235 140225057524340713125006353)
      ·
        refine ⟨105168793143255534843754765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140225057524340713125006353 105168793143255534843754765)
        ·
          refine ⟨39438297428720825566408037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105168793143255534843754765 39438297428720825566408037)
          ·
            refine ⟨7394680767885154793701507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39438297428720825566408037 7394680767885154793701507)
            ·
              refine ⟨11092021151827732190552261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7394680767885154793701507 11092021151827732190552261)
              ·
                refine ⟨2079753965967699785728549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11092021151827732190552261 2079753965967699785728549)
                ·
                  refine ⟨389953868618943709824103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079753965967699785728549 389953868618943709824103)
                  ·
                    rfl

theorem cell21_1708723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 4].length) (baseStart_1708723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708723 prefixEnd_1708723 := by exact prefixLift 1708723
  have htrace : WordTrace (prefixWord ++ tailWord_1708723) baseStart_1708723 baseEnd_1708723 := by
    simpa [prefixWord, tailWord_1708723, baseEnd_1708723] using wordTrace_append hprefix tailTrace_1708723
  have hstable : (prefixWord ++ tailWord_1708723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708723).length < 2 ^ (prefixWord ++ tailWord_1708723).sum := by decide
  have hdescent : baseEnd_1708723 < baseStart_1708723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708740 : List Nat := [2, 3, 3, 1, 1, 2, 2, 3, 4]
def baseStart_1708740 : Nat := 118140960795 + 1708740 * 2 ^ 59
def prefixEnd_1708740 : Nat := 4983230072969 + 3 ^ 40 * 1708740 * 2
def baseEnd_1708740 : Nat := 389957748250555458040735

theorem tailTrace_1708740 : CollatzResearch.WordTrace tailWord_1708740 prefixEnd_1708740 389957748250555458040735 := by
  unfold tailWord_1708740
  simp only [CollatzResearch.WordTrace]
  refine ⟨31161433914767142201685837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41548578553022856268914449 31161433914767142201685837)
  ·
    refine ⟨11685537718037678325632189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31161433914767142201685837 11685537718037678325632189)
    ·
      refine ⟨4382076644264129372112071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11685537718037678325632189 4382076644264129372112071)
      ·
        refine ⟨6573114966396194058168107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4382076644264129372112071 6573114966396194058168107)
        ·
          refine ⟨9859672449594291087252161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6573114966396194058168107 9859672449594291087252161)
          ·
            refine ⟨7394754337195718315439121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9859672449594291087252161 7394754337195718315439121)
            ·
              refine ⟨5546065752896788736579341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7394754337195718315439121 5546065752896788736579341)
              ·
                refine ⟨2079774657336295776217253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5546065752896788736579341 2079774657336295776217253)
                ·
                  refine ⟨389957748250555458040735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079774657336295776217253 389957748250555458040735)
                  ·
                    rfl

theorem cell21_1708740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_1708740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708740 prefixEnd_1708740 := by exact prefixLift 1708740
  have htrace : WordTrace (prefixWord ++ tailWord_1708740) baseStart_1708740 baseEnd_1708740 := by
    simpa [prefixWord, tailWord_1708740, baseEnd_1708740] using wordTrace_append hprefix tailTrace_1708740
  have hstable : (prefixWord ++ tailWord_1708740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708740).length < 2 ^ (prefixWord ++ tailWord_1708740).sum := by decide
  have hdescent : baseEnd_1708740 < baseStart_1708740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708785 : List Nat := [1, 2, 2, 2, 2, 2, 1, 6, 3]
def baseStart_1708785 : Nat := 118140960795 + 1708785 * 2 ^ 59
def prefixEnd_1708785 : Nat := 4983230072969 + 3 ^ 40 * 1708785 * 2
def baseEnd_1708785 : Nat := 389968017863645379790643

theorem tailTrace_1708785 : CollatzResearch.WordTrace tailWord_1708785 prefixEnd_1708785 389968017863645379790643 := by
  unfold tailWord_1708785
  simp only [CollatzResearch.WordTrace]
  refine ⟨62324509114371257088759809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41549672742914171392506539 62324509114371257088759809)
  ·
    refine ⟨46743381835778442816569857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62324509114371257088759809 46743381835778442816569857)
    ·
      refine ⟨35057536376833832112427393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46743381835778442816569857 35057536376833832112427393)
      ·
        refine ⟨26293152282625374084320545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35057536376833832112427393 26293152282625374084320545)
        ·
          refine ⟨19719864211969030563240409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26293152282625374084320545 19719864211969030563240409)
          ·
            refine ⟨14789898158976772922430307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19719864211969030563240409 14789898158976772922430307)
            ·
              refine ⟨22184847238465159383645461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14789898158976772922430307 22184847238465159383645461)
              ·
                refine ⟨1039914714303054346108381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22184847238465159383645461 1039914714303054346108381)
                ·
                  refine ⟨389968017863645379790643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1039914714303054346108381 389968017863645379790643)
                  ·
                    rfl

theorem cell21_1708785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 3].length) (baseStart_1708785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708785 prefixEnd_1708785 := by exact prefixLift 1708785
  have htrace : WordTrace (prefixWord ++ tailWord_1708785) baseStart_1708785 baseEnd_1708785 := by
    simpa [prefixWord, tailWord_1708785, baseEnd_1708785] using wordTrace_append hprefix tailTrace_1708785
  have hstable : (prefixWord ++ tailWord_1708785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708785).length < 2 ^ (prefixWord ++ tailWord_1708785).sum := by decide
  have hdescent : baseEnd_1708785 < baseStart_1708785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708892 : List Nat := [2, 2, 4, 2, 1, 1, 1, 4, 4]
def baseStart_1708892 : Nat := 118140960795 + 1708892 * 2 ^ 59
def prefixEnd_1708892 : Nat := 4983230072969 + 3 ^ 40 * 1708892 * 2
def baseEnd_1708892 : Nat := 389992436721436971507091

theorem tailTrace_1708892 : CollatzResearch.WordTrace tailWord_1708892 prefixEnd_1708892 389992436721436971507091 := by
  unfold tailWord_1708892
  simp only [CollatzResearch.WordTrace]
  refine ⟨31164205862491807181452465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41552274483322409575269953 31164205862491807181452465)
  ·
    refine ⟨23373154396868855386089349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31164205862491807181452465 23373154396868855386089349)
    ·
      refine ⟨4382466449412910384891753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23373154396868855386089349 4382466449412910384891753)
      ·
        refine ⟨3286849837059682788668815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4382466449412910384891753 3286849837059682788668815)
        ·
          refine ⟨4930274755589524183003223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3286849837059682788668815 4930274755589524183003223)
          ·
            refine ⟨7395412133384286274504835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4930274755589524183003223 7395412133384286274504835)
            ·
              refine ⟨11093118200076429411757253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7395412133384286274504835 11093118200076429411757253)
              ·
                refine ⟨2079959662514330514704485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11093118200076429411757253 2079959662514330514704485)
                ·
                  refine ⟨389992436721436971507091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079959662514330514704485 389992436721436971507091)
                  ·
                    rfl

theorem cell21_1708892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_1708892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708892 prefixEnd_1708892 := by exact prefixLift 1708892
  have htrace : WordTrace (prefixWord ++ tailWord_1708892) baseStart_1708892 baseEnd_1708892 := by
    simpa [prefixWord, tailWord_1708892, baseEnd_1708892] using wordTrace_append hprefix tailTrace_1708892
  have hstable : (prefixWord ++ tailWord_1708892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708892).length < 2 ^ (prefixWord ++ tailWord_1708892).sum := by decide
  have hdescent : baseEnd_1708892 < baseStart_1708892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708937 : List Nat := [1, 2, 1, 1, 5, 2, 1, 5, 3]
def baseStart_1708937 : Nat := 118140960795 + 1708937 * 2 ^ 59
def prefixEnd_1708937 : Nat := 4983230072969 + 3 ^ 40 * 1708937 * 2
def baseEnd_1708937 : Nat := 390002706334526893256999

theorem tailTrace_1708937 : CollatzResearch.WordTrace tailWord_1708937 prefixEnd_1708937 390002706334526893256999 := by
  unfold tailWord_1708937
  simp only [CollatzResearch.WordTrace]
  refine ⟨62330053009820587048293065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41553368673213724698862043 62330053009820587048293065)
  ·
    refine ⟨46747539757365440286219799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62330053009820587048293065 46747539757365440286219799)
    ·
      refine ⟨70121309636048160429329699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46747539757365440286219799 70121309636048160429329699)
      ·
        refine ⟨105181964454072240643994549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70121309636048160429329699 105181964454072240643994549)
        ·
          refine ⟨9860809167569272560374489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105181964454072240643994549 9860809167569272560374489)
          ·
            refine ⟨7395606875676954420280867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9860809167569272560374489 7395606875676954420280867)
            ·
              refine ⟨11093410313515431630421301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7395606875676954420280867 11093410313515431630421301)
              ·
                refine ⟨1040007216892071715351997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11093410313515431630421301 1040007216892071715351997)
                ·
                  refine ⟨390002706334526893256999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040007216892071715351997 390002706334526893256999)
                  ·
                    rfl

theorem cell21_1708937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 3].length) (baseStart_1708937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708937 prefixEnd_1708937 := by exact prefixLift 1708937
  have htrace : WordTrace (prefixWord ++ tailWord_1708937) baseStart_1708937 baseEnd_1708937 := by
    simpa [prefixWord, tailWord_1708937, baseEnd_1708937] using wordTrace_append hprefix tailTrace_1708937
  have hstable : (prefixWord ++ tailWord_1708937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708937).length < 2 ^ (prefixWord ++ tailWord_1708937).sum := by decide
  have hdescent : baseEnd_1708937 < baseStart_1708937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708979 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 7]
def baseStart_1708979 : Nat := 118140960795 + 1708979 * 2 ^ 59
def prefixEnd_1708979 : Nat := 4983230072969 + 3 ^ 40 * 1708979 * 2
def baseEnd_1708979 : Nat := 390012291306744153556913

theorem tailTrace_1708979 : CollatzResearch.WordTrace tailWord_1708979 prefixEnd_1708979 390012291306744153556913 := by
  unfold tailWord_1708979
  simp only [CollatzResearch.WordTrace]
  refine ⟨62331584875668428221321991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41554389917112285480881327 62331584875668428221321991)
  ·
    refine ⟨93497377313502642331982987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62331584875668428221321991 93497377313502642331982987)
    ·
      refine ⟨140246065970253963497974481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93497377313502642331982987 140246065970253963497974481)
      ·
        refine ⟨105184549477690472623480861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140246065970253963497974481 105184549477690472623480861)
        ·
          refine ⟨39444206054133927233805323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105184549477690472623480861 39444206054133927233805323)
          ·
            refine ⟨59166309081200890850707985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39444206054133927233805323 59166309081200890850707985)
            ·
              refine ⟨44374731810900668138030989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59166309081200890850707985 44374731810900668138030989)
              ·
                refine ⟨16640524429087750551761621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44374731810900668138030989 16640524429087750551761621)
                ·
                  refine ⟨390012291306744153556913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16640524429087750551761621 390012291306744153556913)
                  ·
                    rfl

theorem cell21_1708979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 7].length) (baseStart_1708979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1708979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1708979 prefixEnd_1708979 := by exact prefixLift 1708979
  have htrace : WordTrace (prefixWord ++ tailWord_1708979) baseStart_1708979 baseEnd_1708979 := by
    simpa [prefixWord, tailWord_1708979, baseEnd_1708979] using wordTrace_append hprefix tailTrace_1708979
  have hstable : (prefixWord ++ tailWord_1708979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708979).length < 2 ^ (prefixWord ++ tailWord_1708979).sum := by decide
  have hdescent : baseEnd_1708979 < baseStart_1708979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709005 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 5]
def baseStart_1709005 : Nat := 118140960795 + 1709005 * 2 ^ 59
def prefixEnd_1709005 : Nat := 4983230072969 + 3 ^ 40 * 1709005 * 2
def baseEnd_1709005 : Nat := 390018224860973886123527

theorem tailTrace_1709005 : CollatzResearch.WordTrace tailWord_1709005 prefixEnd_1709005 390018224860973886123527 := by
  unfold tailWord_1709005
  simp only [CollatzResearch.WordTrace]
  refine ⟨62332533173574234661768469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41555022115716156441178979 62332533173574234661768469)
  ·
    refine ⟨2921837492511292249770397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62332533173574234661768469 2921837492511292249770397)
    ·
      refine ⟨1095689059691734593663899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2921837492511292249770397 1095689059691734593663899)
      ·
        refine ⟨1643533589537601890495849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095689059691734593663899 1643533589537601890495849)
        ·
          refine ⟨1232650192153201417871887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1643533589537601890495849 1232650192153201417871887)
          ·
            refine ⟨1848975288229802126807831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232650192153201417871887 1848975288229802126807831)
            ·
              refine ⟨2773462932344703190211747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848975288229802126807831 2773462932344703190211747)
              ·
                refine ⟨4160194398517054785317621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2773462932344703190211747 4160194398517054785317621)
                ·
                  refine ⟨390018224860973886123527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4160194398517054785317621 390018224860973886123527)
                  ·
                    rfl

theorem cell21_1709005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_1709005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709005 prefixEnd_1709005 := by exact prefixLift 1709005
  have htrace : WordTrace (prefixWord ++ tailWord_1709005) baseStart_1709005 baseEnd_1709005 := by
    simpa [prefixWord, tailWord_1709005, baseEnd_1709005] using wordTrace_append hprefix tailTrace_1709005
  have hstable : (prefixWord ++ tailWord_1709005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709005).length < 2 ^ (prefixWord ++ tailWord_1709005).sum := by decide
  have hdescent : baseEnd_1709005 < baseStart_1709005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709027 : List Nat := [1, 1, 1, 6, 1, 1, 3, 3, 4]
def baseStart_1709027 : Nat := 118140960795 + 1709027 * 2 ^ 59
def prefixEnd_1709027 : Nat := 4983230072969 + 3 ^ 40 * 1709027 * 2
def baseEnd_1709027 : Nat := 390023245560706736756815

theorem tailTrace_1709027 : CollatzResearch.WordTrace tailWord_1709027 prefixEnd_1709027 390023245560706736756815 := by
  unfold tailWord_1709027
  simp only [CollatzResearch.WordTrace]
  refine ⟨62333335579494532419069335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41555557052996354946046223 62333335579494532419069335)
  ·
    refine ⟨93500003369241798628604003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62333335579494532419069335 93500003369241798628604003)
    ·
      refine ⟨140250005053862697942906005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93500003369241798628604003 140250005053862697942906005)
      ·
        refine ⟨6574218986899813966073719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 140250005053862697942906005 6574218986899813966073719)
        ·
          refine ⟨9861328480349720949110579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6574218986899813966073719 9861328480349720949110579)
          ·
            refine ⟨14791992720524581423665869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9861328480349720949110579 14791992720524581423665869)
            ·
              refine ⟨5546997270196718033874701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14791992720524581423665869 5546997270196718033874701)
              ·
                refine ⟨2080123976323769262703013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5546997270196718033874701 2080123976323769262703013)
                ·
                  refine ⟨390023245560706736756815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2080123976323769262703013 390023245560706736756815)
                  ·
                    rfl

theorem cell21_1709027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 4].length) (baseStart_1709027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709027 prefixEnd_1709027 := by exact prefixLift 1709027
  have htrace : WordTrace (prefixWord ++ tailWord_1709027) baseStart_1709027 baseEnd_1709027 := by
    simpa [prefixWord, tailWord_1709027, baseEnd_1709027] using wordTrace_append hprefix tailTrace_1709027
  have hstable : (prefixWord ++ tailWord_1709027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709027).length < 2 ^ (prefixWord ++ tailWord_1709027).sum := by decide
  have hdescent : baseEnd_1709027 < baseStart_1709027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709041 : List Nat := [1, 2, 2, 2, 4, 1, 2, 7]
def baseStart_1709041 : Nat := 118140960795 + 1709041 * 2 ^ 59
def prefixEnd_1709041 : Nat := 4983230072969 + 3 ^ 40 * 1709041 * 2
def baseEnd_1709041 : Nat := 130008813517148607841151

theorem tailTrace_1709041 : CollatzResearch.WordTrace tailWord_1709041 prefixEnd_1709041 130008813517148607841151 := by
  unfold tailWord_1709041
  simp only [CollatzResearch.WordTrace]
  refine ⟨62333846201443812810078977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41555897467629208540052651 62333846201443812810078977)
  ·
    refine ⟨46750384651082859607559233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62333846201443812810078977 46750384651082859607559233)
    ·
      refine ⟨35062788488312144705669425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46750384651082859607559233 35062788488312144705669425)
      ·
        refine ⟨26297091366234108529252069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35062788488312144705669425 26297091366234108529252069)
        ·
          refine ⟨4930704631168895349234763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26297091366234108529252069 4930704631168895349234763)
          ·
            refine ⟨7396056946753343023852145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4930704631168895349234763 7396056946753343023852145)
            ·
              refine ⟨5547042710065007267889109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7396056946753343023852145 5547042710065007267889109)
              ·
                refine ⟨130008813517148607841151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5547042710065007267889109 130008813517148607841151)
                ·
                  rfl

theorem cell21_1709041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 7].length) (baseStart_1709041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709041 prefixEnd_1709041 := by exact prefixLift 1709041
  have htrace : WordTrace (prefixWord ++ tailWord_1709041) baseStart_1709041 baseEnd_1709041 := by
    simpa [prefixWord, tailWord_1709041, baseEnd_1709041] using wordTrace_append hprefix tailTrace_1709041
  have hstable : (prefixWord ++ tailWord_1709041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709041).length < 2 ^ (prefixWord ++ tailWord_1709041).sum := by decide
  have hdescent : baseEnd_1709041 < baseStart_1709041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709058 : List Nat := [3, 4, 1, 3, 10]
def baseStart_1709058 : Nat := 118140960795 + 1709058 * 2 ^ 59
def prefixEnd_1709058 : Nat := 4983230072969 + 3 ^ 40 * 1709058 * 2
def baseEnd_1709058 : Nat := 4815189138062439157285

theorem tailTrace_1709058 : CollatzResearch.WordTrace tailWord_1709058 prefixEnd_1709058 4815189138062439157285 := by
  unfold tailWord_1709058
  simp only [CollatzResearch.WordTrace]
  refine ⟨15583616560595556178361957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41556310828254816475631885 15583616560595556178361957)
  ·
    refine ⟨2921928105111666783442867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15583616560595556178361957 2921928105111666783442867)
    ·
      refine ⟨4382892157667500175164301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2921928105111666783442867 4382892157667500175164301)
      ·
        refine ⟨1643584559125312565686613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4382892157667500175164301 1643584559125312565686613)
        ·
          refine ⟨4815189138062439157285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1643584559125312565686613 4815189138062439157285)
          ·
            rfl

theorem cell21_1709058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 10].length) (baseStart_1709058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709058 prefixEnd_1709058 := by exact prefixLift 1709058
  have htrace : WordTrace (prefixWord ++ tailWord_1709058) baseStart_1709058 baseEnd_1709058 := by
    simpa [prefixWord, tailWord_1709058, baseEnd_1709058] using wordTrace_append hprefix tailTrace_1709058
  have hstable : (prefixWord ++ tailWord_1709058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709058).length < 2 ^ (prefixWord ++ tailWord_1709058).sum := by decide
  have hdescent : baseEnd_1709058 < baseStart_1709058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709117 : List Nat := [1, 4, 1, 3, 1, 3, 8]
def baseStart_1709117 : Nat := 118140960795 + 1709117 * 2 ^ 59
def prefixEnd_1709117 : Nat := 4983230072969 + 3 ^ 40 * 1709117 * 2
def baseEnd_1709117 : Nat := 43338198309654064472959

theorem tailTrace_1709117 : CollatzResearch.WordTrace tailWord_1709117 prefixEnd_1709117 43338198309654064472959 := by
  unfold tailWord_1709117
  simp only [CollatzResearch.WordTrace]
  refine ⟨62336618149168477789845605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41557745432778985193230403 62336618149168477789845605)
  ·
    refine ⟨11688115902969089585596051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62336618149168477789845605 11688115902969089585596051)
    ·
      refine ⟨17532173854453634378394077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11688115902969089585596051 17532173854453634378394077)
      ·
        refine ⟨6574565195420112891897779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17532173854453634378394077 6574565195420112891897779)
        ·
          refine ⟨9861847793130169337846669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6574565195420112891897779 9861847793130169337846669)
          ·
            refine ⟨3698192922423813501692501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9861847793130169337846669 3698192922423813501692501)
            ·
              refine ⟨43338198309654064472959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3698192922423813501692501 43338198309654064472959)
              ·
                rfl

theorem cell21_1709117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 8].length) (baseStart_1709117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709117 prefixEnd_1709117 := by exact prefixLift 1709117
  have htrace : WordTrace (prefixWord ++ tailWord_1709117) baseStart_1709117 baseEnd_1709117 := by
    simpa [prefixWord, tailWord_1709117, baseEnd_1709117] using wordTrace_append hprefix tailTrace_1709117
  have hstable : (prefixWord ++ tailWord_1709117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709117).length < 2 ^ (prefixWord ++ tailWord_1709117).sum := by decide
  have hdescent : baseEnd_1709117 < baseStart_1709117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709148 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 5]
def baseStart_1709148 : Nat := 118140960795 + 1709148 * 2 ^ 59
def prefixEnd_1709148 : Nat := 4983230072969 + 3 ^ 40 * 1709148 * 2
def baseEnd_1709148 : Nat := 390050859409237415239901

theorem tailTrace_1709148 : CollatzResearch.WordTrace tailWord_1709148 prefixEnd_1709148 390050859409237415239901 := by
  unfold tailWord_1709148
  simp only [CollatzResearch.WordTrace]
  refine ⟨31168874406028085042112049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41558499208037446722816065 31168874406028085042112049)
  ·
    refine ⟨23376655804521063781584037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31168874406028085042112049 23376655804521063781584037)
    ·
      refine ⟨4383122963347699459047007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23376655804521063781584037 4383122963347699459047007)
      ·
        refine ⟨6574684445021549188570511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4383122963347699459047007 6574684445021549188570511)
        ·
          refine ⟨9862026667532323782855767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6574684445021549188570511 9862026667532323782855767)
          ·
            refine ⟨14793040001298485674283651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9862026667532323782855767 14793040001298485674283651)
            ·
              refine ⟨22189560001947728511425477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14793040001298485674283651 22189560001947728511425477)
              ·
                refine ⟨4160542500365199095892277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22189560001947728511425477 4160542500365199095892277)
                ·
                  refine ⟨390050859409237415239901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4160542500365199095892277 390050859409237415239901)
                  ·
                    rfl

theorem cell21_1709148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_1709148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709148 prefixEnd_1709148 := by exact prefixLift 1709148
  have htrace : WordTrace (prefixWord ++ tailWord_1709148) baseStart_1709148 baseEnd_1709148 := by
    simpa [prefixWord, tailWord_1709148, baseEnd_1709148] using wordTrace_append hprefix tailTrace_1709148
  have hstable : (prefixWord ++ tailWord_1709148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709148).length < 2 ^ (prefixWord ++ tailWord_1709148).sum := by decide
  have hdescent : baseEnd_1709148 < baseStart_1709148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709176 : List Nat := [2, 1, 2, 1, 1, 1, 13]
def baseStart_1709176 : Nat := 118140960795 + 1709176 * 2 ^ 59
def prefixEnd_1709176 : Nat := 4983230072969 + 3 ^ 40 * 1709176 * 2
def baseEnd_1709176 : Nat := 43339694376746176530353

theorem tailTrace_1709176 : CollatzResearch.WordTrace tailWord_1709176 prefixEnd_1709176 43339694376746176530353 := by
  unfold tailWord_1709176
  simp only [CollatzResearch.WordTrace]
  refine ⟨31169385027977365433121691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41559180037303153910828921 31169385027977365433121691)
  ·
    refine ⟨46754077541966048149682537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31169385027977365433121691 46754077541966048149682537)
    ·
      refine ⟨35065558156474536112261903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46754077541966048149682537 35065558156474536112261903)
      ·
        refine ⟨52598337234711804168392855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35065558156474536112261903 52598337234711804168392855)
        ·
          refine ⟨78897505852067706252589283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52598337234711804168392855 78897505852067706252589283)
          ·
            refine ⟨118346258778101559378883925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78897505852067706252589283 118346258778101559378883925)
            ·
              refine ⟨43339694376746176530353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 118346258778101559378883925 43339694376746176530353)
              ·
                rfl

theorem cell21_1709176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 13].length) (baseStart_1709176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709176 prefixEnd_1709176 := by exact prefixLift 1709176
  have htrace : WordTrace (prefixWord ++ tailWord_1709176) baseStart_1709176 baseEnd_1709176 := by
    simpa [prefixWord, tailWord_1709176, baseEnd_1709176] using wordTrace_append hprefix tailTrace_1709176
  have hstable : (prefixWord ++ tailWord_1709176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709176).length < 2 ^ (prefixWord ++ tailWord_1709176).sum := by decide
  have hdescent : baseEnd_1709176 < baseStart_1709176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709193 : List Nat := [1, 2, 1, 1, 4, 4, 2, 6]
def baseStart_1709193 : Nat := 118140960795 + 1709193 * 2 ^ 59
def prefixEnd_1709193 : Nat := 4983230072969 + 3 ^ 40 * 1709193 * 2
def baseEnd_1709193 : Nat := 130020376340775778996603

theorem tailTrace_1709193 : CollatzResearch.WordTrace tailWord_1709193 prefixEnd_1709193 130020376340775778996603 := by
  unfold tailWord_1709193
  simp only [CollatzResearch.WordTrace]
  refine ⟨62339390096893142769612233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41559593397928761846408155 62339390096893142769612233)
  ·
    refine ⟨46754542572669857077209175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62339390096893142769612233 46754542572669857077209175)
    ·
      refine ⟨70131813859004785615813763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46754542572669857077209175 70131813859004785615813763)
      ·
        refine ⟨105197720788507178423720645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70131813859004785615813763 105197720788507178423720645)
        ·
          refine ⟨19724572647845095954447621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105197720788507178423720645 19724572647845095954447621)
          ·
            refine ⟨3698357371470955491458929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19724572647845095954447621 3698357371470955491458929)
            ·
              refine ⟨2773768028603216618594197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3698357371470955491458929 2773768028603216618594197)
              ·
                refine ⟨130020376340775778996603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2773768028603216618594197 130020376340775778996603)
                ·
                  rfl

theorem cell21_1709193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 6].length) (baseStart_1709193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709193 prefixEnd_1709193 := by exact prefixLift 1709193
  have htrace : WordTrace (prefixWord ++ tailWord_1709193) baseStart_1709193 baseEnd_1709193 := by
    simpa [prefixWord, tailWord_1709193, baseEnd_1709193] using wordTrace_append hprefix tailTrace_1709193
  have hstable : (prefixWord ++ tailWord_1709193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709193).length < 2 ^ (prefixWord ++ tailWord_1709193).sum := by decide
  have hdescent : baseEnd_1709193 < baseStart_1709193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709241 : List Nat := [1, 2, 1, 4, 1, 4, 1, 4, 3]
def baseStart_1709241 : Nat := 118140960795 + 1709241 * 2 ^ 59
def prefixEnd_1709241 : Nat := 4983230072969 + 3 ^ 40 * 1709241 * 2
def baseEnd_1709241 : Nat := 390072083276289920189711

theorem tailTrace_1709241 : CollatzResearch.WordTrace tailWord_1709241 prefixEnd_1709241 390072083276289920189711 := by
  unfold tailWord_1709241
  simp only [CollatzResearch.WordTrace]
  refine ⟨62341140800719246967359577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41560760533812831311573051 62341140800719246967359577)
  ·
    refine ⟨46755855600539435225519683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62341140800719246967359577 46755855600539435225519683)
    ·
      refine ⟨70133783400809152838279525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46755855600539435225519683 70133783400809152838279525)
      ·
        refine ⟨13150084387651716157177411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70133783400809152838279525 13150084387651716157177411)
        ·
          refine ⟨19725126581477574235766117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13150084387651716157177411 19725126581477574235766117)
          ·
            refine ⟨3698461234027045169206147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19725126581477574235766117 3698461234027045169206147)
            ·
              refine ⟨5547691851040567753809221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3698461234027045169206147 5547691851040567753809221)
              ·
                refine ⟨1040192222070106453839229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5547691851040567753809221 1040192222070106453839229)
                ·
                  refine ⟨390072083276289920189711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040192222070106453839229 390072083276289920189711)
                  ·
                    rfl

theorem cell21_1709241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 3].length) (baseStart_1709241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709241 prefixEnd_1709241 := by exact prefixLift 1709241
  have htrace : WordTrace (prefixWord ++ tailWord_1709241) baseStart_1709241 baseEnd_1709241 := by
    simpa [prefixWord, tailWord_1709241, baseEnd_1709241] using wordTrace_append hprefix tailTrace_1709241
  have hstable : (prefixWord ++ tailWord_1709241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709241).length < 2 ^ (prefixWord ++ tailWord_1709241).sum := by decide
  have hdescent : baseEnd_1709241 < baseStart_1709241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709404 : List Nat := [2, 2, 4, 13]
def baseStart_1709404 : Nat := 118140960795 + 1709404 * 2 ^ 59
def prefixEnd_1709404 : Nat := 4983230072969 + 3 ^ 40 * 1709404 * 2
def baseEnd_1709404 : Nat := 1605387992168880078077

theorem tailTrace_1709404 : CollatzResearch.WordTrace tailWord_1709404 prefixEnd_1709404 1605387992168880078077 := by
  unfold tailWord_1709404
  simp only [CollatzResearch.WordTrace]
  refine ⟨31173542949564362902771633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41564723932752483870362177 31173542949564362902771633)
  ·
    refine ⟨23380157212173272177078725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31173542949564362902771633 23380157212173272177078725)
    ·
      refine ⟨4383779477282488533202261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23380157212173272177078725 4383779477282488533202261)
      ·
        refine ⟨1605387992168880078077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4383779477282488533202261 1605387992168880078077)
        ·
          rfl

theorem cell21_1709404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 13].length) (baseStart_1709404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709404 prefixEnd_1709404 := by exact prefixLift 1709404
  have htrace : WordTrace (prefixWord ++ tailWord_1709404) baseStart_1709404 baseEnd_1709404 := by
    simpa [prefixWord, tailWord_1709404, baseEnd_1709404] using wordTrace_append hprefix tailTrace_1709404
  have hstable : (prefixWord ++ tailWord_1709404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709404).length < 2 ^ (prefixWord ++ tailWord_1709404).sum := by decide
  have hdescent : baseEnd_1709404 < baseStart_1709404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709421 : List Nat := [1, 5, 1, 1, 1, 3, 3, 6]
def baseStart_1709421 : Nat := 118140960795 + 1709421 * 2 ^ 59
def prefixEnd_1709421 : Nat := 4983230072969 + 3 ^ 40 * 1709421 * 2
def baseEnd_1709421 : Nat := 130037720576216535729781

theorem tailTrace_1709421 : CollatzResearch.WordTrace tailWord_1709421 prefixEnd_1709421 130037720576216535729781 := by
  unfold tailWord_1709421
  simp only [CollatzResearch.WordTrace]
  refine ⟨62347705940067137708912117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41565137293378091805941411 62347705940067137708912117)
  ·
    refine ⟨5845097431881294160210511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62347705940067137708912117 5845097431881294160210511)
    ·
      refine ⟨8767646147821941240315767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5845097431881294160210511 8767646147821941240315767)
      ·
        refine ⟨13151469221732911860473651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8767646147821941240315767 13151469221732911860473651)
        ·
          refine ⟨19727203832599367790710477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13151469221732911860473651 19727203832599367790710477)
          ·
            refine ⟨7397701437224762921516429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19727203832599367790710477 7397701437224762921516429)
            ·
              refine ⟨2774138038959286095568661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7397701437224762921516429 2774138038959286095568661)
              ·
                refine ⟨130037720576216535729781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2774138038959286095568661 130037720576216535729781)
                ·
                  rfl

theorem cell21_1709421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 6].length) (baseStart_1709421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709421 prefixEnd_1709421 := by exact prefixLift 1709421
  have htrace : WordTrace (prefixWord ++ tailWord_1709421) baseStart_1709421 baseEnd_1709421 := by
    simpa [prefixWord, tailWord_1709421, baseEnd_1709421] using wordTrace_append hprefix tailTrace_1709421
  have hstable : (prefixWord ++ tailWord_1709421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709421).length < 2 ^ (prefixWord ++ tailWord_1709421).sum := by decide
  have hdescent : baseEnd_1709421 < baseStart_1709421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709435 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 5]
def baseStart_1709435 : Nat := 118140960795 + 1709435 * 2 ^ 59
def prefixEnd_1709435 : Nat := 4983230072969 + 3 ^ 40 * 1709435 * 2
def baseEnd_1709435 : Nat := 390116356719388693955981

theorem tailTrace_1709435 : CollatzResearch.WordTrace tailWord_1709435 prefixEnd_1709435 390116356719388693955981 := by
  unfold tailWord_1709435
  simp only [CollatzResearch.WordTrace]
  refine ⟨62348216562016418099921759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41565477708010945399947839 62348216562016418099921759)
  ·
    refine ⟨93522324843024627149882639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62348216562016418099921759 93522324843024627149882639)
    ·
      refine ⟨140283487264536940724823959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93522324843024627149882639 140283487264536940724823959)
      ·
        refine ⟨210425230896805411087235939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140283487264536940724823959 210425230896805411087235939)
        ·
          refine ⟨315637846345208116630853909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210425230896805411087235939 315637846345208116630853909)
          ·
            refine ⟨14795524047431630467071277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 315637846345208116630853909 14795524047431630467071277)
            ·
              refine ⟨5548321517786861425151729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14795524047431630467071277 5548321517786861425151729)
              ·
                refine ⟨4161241138340146068863797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5548321517786861425151729 4161241138340146068863797)
                ·
                  refine ⟨390116356719388693955981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4161241138340146068863797 390116356719388693955981)
                  ·
                    rfl

theorem cell21_1709435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 5].length) (baseStart_1709435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709435 prefixEnd_1709435 := by exact prefixLift 1709435
  have htrace : WordTrace (prefixWord ++ tailWord_1709435) baseStart_1709435 baseEnd_1709435 := by
    simpa [prefixWord, tailWord_1709435, baseEnd_1709435] using wordTrace_append hprefix tailTrace_1709435
  have hstable : (prefixWord ++ tailWord_1709435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709435).length < 2 ^ (prefixWord ++ tailWord_1709435).sum := by decide
  have hdescent : baseEnd_1709435 < baseStart_1709435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709458 : List Nat := [3, 2, 3, 3, 2, 1, 1, 2, 4]
def baseStart_1709458 : Nat := 118140960795 + 1709458 * 2 ^ 59
def prefixEnd_1709458 : Nat := 4983230072969 + 3 ^ 40 * 1709458 * 2
def baseEnd_1709458 : Nat := 390121605632745765072601

theorem tailTrace_1709458 : CollatzResearch.WordTrace tailWord_1709458 prefixEnd_1709458 390121605632745765072601 := by
  unfold tailWord_1709458
  simp only [CollatzResearch.WordTrace]
  refine ⟨15587263860233273257002257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41566036960622062018672685 15587263860233273257002257)
  ·
    refine ⟨11690447895174954942751693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15587263860233273257002257 11690447895174954942751693)
    ·
      refine ⟨4383917960690608103531885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11690447895174954942751693 4383917960690608103531885)
      ·
        refine ⟨1643969235258978038824457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4383917960690608103531885 1643969235258978038824457)
        ·
          refine ⟨1232976926444233529118343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1643969235258978038824457 1232976926444233529118343)
          ·
            refine ⟨1849465389666350293677515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232976926444233529118343 1849465389666350293677515)
            ·
              refine ⟨2774198084499525440516273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849465389666350293677515 2774198084499525440516273)
              ·
                refine ⟨2080648563374644080387205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2774198084499525440516273 2080648563374644080387205)
                ·
                  refine ⟨390121605632745765072601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2080648563374644080387205 390121605632745765072601)
                  ·
                    rfl

theorem cell21_1709458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_1709458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709458 prefixEnd_1709458 := by exact prefixLift 1709458
  have htrace : WordTrace (prefixWord ++ tailWord_1709458) baseStart_1709458 baseEnd_1709458 := by
    simpa [prefixWord, tailWord_1709458, baseEnd_1709458] using wordTrace_append hprefix tailTrace_1709458
  have hstable : (prefixWord ++ tailWord_1709458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709458).length < 2 ^ (prefixWord ++ tailWord_1709458).sum := by decide
  have hdescent : baseEnd_1709458 < baseStart_1709458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709466 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 6]
def baseStart_1709466 : Nat := 118140960795 + 1709466 * 2 ^ 59
def prefixEnd_1709466 : Nat := 4983230072969 + 3 ^ 40 * 1709466 * 2
def baseEnd_1709466 : Nat := 390123431341739528939251

theorem tailTrace_1709466 : CollatzResearch.WordTrace tailWord_1709466 prefixEnd_1709466 390123431341739528939251 := by
  unfold tailWord_1709466
  simp only [CollatzResearch.WordTrace]
  refine ⟨15587336806226027598575063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41566231483269406929533501 15587336806226027598575063)
  ·
    refine ⟨23381005209339041397862595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15587336806226027598575063 23381005209339041397862595)
    ·
      refine ⟨35071507814008562096793893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23381005209339041397862595 35071507814008562096793893)
      ·
        refine ⟨6575907715126605393148855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35071507814008562096793893 6575907715126605393148855)
        ·
          refine ⟨9863861572689908089723283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6575907715126605393148855 9863861572689908089723283)
          ·
            refine ⟨14795792359034862134584925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9863861572689908089723283 14795792359034862134584925)
            ·
              refine ⟨5548422134638073300469347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14795792359034862134584925 5548422134638073300469347)
              ·
                refine ⟨8322633201957109950704021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5548422134638073300469347 8322633201957109950704021)
                ·
                  refine ⟨390123431341739528939251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8322633201957109950704021 390123431341739528939251)
                  ·
                    rfl

theorem cell21_1709466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_1709466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709466 prefixEnd_1709466 := by exact prefixLift 1709466
  have htrace : WordTrace (prefixWord ++ tailWord_1709466) baseStart_1709466 baseEnd_1709466 := by
    simpa [prefixWord, tailWord_1709466, baseEnd_1709466] using wordTrace_append hprefix tailTrace_1709466
  have hstable : (prefixWord ++ tailWord_1709466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709466).length < 2 ^ (prefixWord ++ tailWord_1709466).sum := by decide
  have hdescent : baseEnd_1709466 < baseStart_1709466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709469 : List Nat := [1, 4, 2, 1, 3, 1, 2, 4, 3]
def baseStart_1709469 : Nat := 118140960795 + 1709469 * 2 ^ 59
def prefixEnd_1709469 : Nat := 4983230072969 + 3 ^ 40 * 1709469 * 2
def baseEnd_1709469 : Nat := 390124115982612190389245

theorem tailTrace_1709469 : CollatzResearch.WordTrace tailWord_1709469 prefixEnd_1709469 390124115982612190389245 := by
  unfold tailWord_1709469
  simp only [CollatzResearch.WordTrace]
  refine ⟨62349456643893241906659461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41566304429262161271106307 62349456643893241906659461)
  ·
    refine ⟨11690523120729982857498649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62349456643893241906659461 11690523120729982857498649)
    ·
      refine ⟨8767892340547487143123987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11690523120729982857498649 8767892340547487143123987)
      ·
        refine ⟨13151838510821230714685981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8767892340547487143123987 13151838510821230714685981)
        ·
          refine ⟨4931939441557961518007243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13151838510821230714685981 4931939441557961518007243)
          ·
            refine ⟨7397909162336942277010865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4931939441557961518007243 7397909162336942277010865)
            ·
              refine ⟨5548431871752706707758149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7397909162336942277010865 5548431871752706707758149)
              ·
                refine ⟨1040330975953632507704653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5548431871752706707758149 1040330975953632507704653)
                ·
                  refine ⟨390124115982612190389245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040330975953632507704653 390124115982612190389245)
                  ·
                    rfl

theorem cell21_1709469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_1709469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709469 prefixEnd_1709469 := by exact prefixLift 1709469
  have htrace : WordTrace (prefixWord ++ tailWord_1709469) baseStart_1709469 baseEnd_1709469 := by
    simpa [prefixWord, tailWord_1709469, baseEnd_1709469] using wordTrace_append hprefix tailTrace_1709469
  have hstable : (prefixWord ++ tailWord_1709469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709469).length < 2 ^ (prefixWord ++ tailWord_1709469).sum := by decide
  have hdescent : baseEnd_1709469 < baseStart_1709469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709497 : List Nat := [1, 2, 1, 4, 4, 1, 1, 7]
def baseStart_1709497 : Nat := 118140960795 + 1709497 * 2 ^ 59
def prefixEnd_1709497 : Nat := 4983230072969 + 3 ^ 40 * 1709497 * 2
def baseEnd_1709497 : Nat := 130043501988030121307507

theorem tailTrace_1709497 : CollatzResearch.WordTrace tailWord_1709497 prefixEnd_1709497 130043501988030121307507 := by
  unfold tailWord_1709497
  simp only [CollatzResearch.WordTrace]
  refine ⟨62350477887791802688678745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41566985258527868459119163 62350477887791802688678745)
  ·
    refine ⟨46762858415843852016509059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62350477887791802688678745 46762858415843852016509059)
    ·
      refine ⟨70144287623765778024763589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46762858415843852016509059 70144287623765778024763589)
      ·
        refine ⟨13152053929456083379643173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70144287623765778024763589 13152053929456083379643173)
        ·
          refine ⟨2466010111773015633683095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13152053929456083379643173 2466010111773015633683095)
          ·
            refine ⟨3699015167659523450524643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2466010111773015633683095 3699015167659523450524643)
            ·
              refine ⟨5548522751489285175786965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3699015167659523450524643 5548522751489285175786965)
              ·
                refine ⟨130043501988030121307507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5548522751489285175786965 130043501988030121307507)
                ·
                  rfl

theorem cell21_1709497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 7].length) (baseStart_1709497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709497 prefixEnd_1709497 := by exact prefixLift 1709497
  have htrace : WordTrace (prefixWord ++ tailWord_1709497) baseStart_1709497 baseEnd_1709497 := by
    simpa [prefixWord, tailWord_1709497, baseEnd_1709497] using wordTrace_append hprefix tailTrace_1709497
  have hstable : (prefixWord ++ tailWord_1709497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709497).length < 2 ^ (prefixWord ++ tailWord_1709497).sum := by decide
  have hdescent : baseEnd_1709497 < baseStart_1709497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709528 : List Nat := [2, 1, 2, 2, 2, 1, 2, 6, 3]
def baseStart_1709528 : Nat := 118140960795 + 1709528 * 2 ^ 59
def prefixEnd_1709528 : Nat := 4983230072969 + 3 ^ 40 * 1709528 * 2
def baseEnd_1709528 : Nat := 390137580586441198905791

theorem tailTrace_1709528 : CollatzResearch.WordTrace tailWord_1709528 prefixEnd_1709528 390137580586441198905791 := by
  unfold tailWord_1709528
  simp only [CollatzResearch.WordTrace]
  refine ⟨31175804275339747491528619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41567739033786329988704825 31175804275339747491528619)
  ·
    refine ⟨46763706413009621237292929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31175804275339747491528619 46763706413009621237292929)
    ·
      refine ⟨35072779809757215927969697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46763706413009621237292929 35072779809757215927969697)
      ·
        refine ⟨26304584857317911945977273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35072779809757215927969697 26304584857317911945977273)
        ·
          refine ⟨19728438642988433959482955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26304584857317911945977273 19728438642988433959482955)
          ·
            refine ⟨29592657964482650939224433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19728438642988433959482955 29592657964482650939224433)
            ·
              refine ⟨22194493473361988204418325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29592657964482650939224433 22194493473361988204418325)
              ·
                refine ⟨1040366881563843197082109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22194493473361988204418325 1040366881563843197082109)
                ·
                  refine ⟨390137580586441198905791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040366881563843197082109 390137580586441198905791)
                  ·
                    rfl

theorem cell21_1709528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 3].length) (baseStart_1709528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709528 prefixEnd_1709528 := by exact prefixLift 1709528
  have htrace : WordTrace (prefixWord ++ tailWord_1709528) baseStart_1709528 baseEnd_1709528 := by
    simpa [prefixWord, tailWord_1709528, baseEnd_1709528] using wordTrace_append hprefix tailTrace_1709528
  have hstable : (prefixWord ++ tailWord_1709528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709528).length < 2 ^ (prefixWord ++ tailWord_1709528).sum := by decide
  have hdescent : baseEnd_1709528 < baseStart_1709528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709579 : List Nat := [1, 1, 1, 1, 9, 1, 2, 2, 3]
def baseStart_1709579 : Nat := 118140960795 + 1709579 * 2 ^ 59
def prefixEnd_1709579 : Nat := 4983230072969 + 3 ^ 40 * 1709579 * 2
def baseEnd_1709579 : Nat := 390149219481276443555687

theorem tailTrace_1709579 : CollatzResearch.WordTrace tailWord_1709579 prefixEnd_1709579 390149219481276443555687 := by
  unfold tailWord_1709579
  simp only [CollatzResearch.WordTrace]
  refine ⟨62353468673494730693163791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41568979115663153795442527 62353468673494730693163791)
  ·
    refine ⟨93530203010242096039745687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62353468673494730693163791 93530203010242096039745687)
    ·
      refine ⟨140295304515363144059618531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93530203010242096039745687 140295304515363144059618531)
      ·
        refine ⟨210442956773044716089427797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140295304515363144059618531 210442956773044716089427797)
        ·
          refine ⟨1233064199842058883336491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 210442956773044716089427797 1233064199842058883336491)
          ·
            refine ⟨1849596299763088325004737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233064199842058883336491 1849596299763088325004737)
            ·
              refine ⟨1387197224822316243753553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1849596299763088325004737 1387197224822316243753553)
              ·
                refine ⟨1040397918616737182815165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387197224822316243753553 1040397918616737182815165)
                ·
                  refine ⟨390149219481276443555687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040397918616737182815165 390149219481276443555687)
                  ·
                    rfl

theorem cell21_1709579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 3].length) (baseStart_1709579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709579 prefixEnd_1709579 := by exact prefixLift 1709579
  have htrace : WordTrace (prefixWord ++ tailWord_1709579) baseStart_1709579 baseEnd_1709579 := by
    simpa [prefixWord, tailWord_1709579, baseEnd_1709579] using wordTrace_append hprefix tailTrace_1709579
  have hstable : (prefixWord ++ tailWord_1709579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709579).length < 2 ^ (prefixWord ++ tailWord_1709579).sum := by decide
  have hdescent : baseEnd_1709579 < baseStart_1709579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709621 : List Nat := [1, 3, 3, 1, 1, 4, 2, 3, 3]
def baseStart_1709621 : Nat := 118140960795 + 1709621 * 2 ^ 59
def prefixEnd_1709621 : Nat := 4983230072969 + 3 ^ 40 * 1709621 * 2
def baseEnd_1709621 : Nat := 390158804453493703855601

theorem tailTrace_1709621 : CollatzResearch.WordTrace tailWord_1709621 prefixEnd_1709621 390158804453493703855601 := by
  unfold tailWord_1709621
  simp only [CollatzResearch.WordTrace]
  refine ⟨62355000539342571866192717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41570000359561714577461811 62355000539342571866192717)
  ·
    refine ⟨23383125202253464449822269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62355000539342571866192717 23383125202253464449822269)
    ·
      refine ⟨8768671950845049168683351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23383125202253464449822269 8768671950845049168683351)
      ·
        refine ⟨13153007926267573753025027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8768671950845049168683351 13153007926267573753025027)
        ·
          refine ⟨19729511889401360629537541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13153007926267573753025027 19729511889401360629537541)
          ·
            refine ⟨3699283479262755118038289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19729511889401360629537541 3699283479262755118038289)
            ·
              refine ⟨2774462609447066338528717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3699283479262755118038289 2774462609447066338528717)
              ·
                refine ⟨1040423478542649876948269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2774462609447066338528717 1040423478542649876948269)
                ·
                  refine ⟨390158804453493703855601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040423478542649876948269 390158804453493703855601)
                  ·
                    rfl

theorem cell21_1709621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_1709621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709621 prefixEnd_1709621 := by exact prefixLift 1709621
  have htrace : WordTrace (prefixWord ++ tailWord_1709621) baseStart_1709621 baseEnd_1709621 := by
    simpa [prefixWord, tailWord_1709621, baseEnd_1709621] using wordTrace_append hprefix tailTrace_1709621
  have hstable : (prefixWord ++ tailWord_1709621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709621).length < 2 ^ (prefixWord ++ tailWord_1709621).sum := by decide
  have hdescent : baseEnd_1709621 < baseStart_1709621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709638 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1709638 : Nat := 118140960795 + 1709638 * 2 ^ 59
def prefixEnd_1709638 : Nat := 4983230072969 + 3 ^ 40 * 1709638 * 2
def baseEnd_1709638 : Nat := 390162684085105452072233

theorem tailTrace_1709638 : CollatzResearch.WordTrace tailWord_1709638 prefixEnd_1709638 390162684085105452072233 := by
  unfold tailWord_1709638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1948613143133780742798799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41570413720187322513041045 1948613143133780742798799)
  ·
    refine ⟨2922919714700671114198199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1948613143133780742798799 2922919714700671114198199)
    ·
      refine ⟨4384379572051006671297299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2922919714700671114198199 4384379572051006671297299)
      ·
        refine ⟨6576569358076510006945949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4384379572051006671297299 6576569358076510006945949)
        ·
          refine ⟨2466213509278691252604731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6576569358076510006945949 2466213509278691252604731)
          ·
            refine ⟨3699320263918036878907097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2466213509278691252604731 3699320263918036878907097)
            ·
              refine ⟨2774490197938527659180323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3699320263918036878907097 2774490197938527659180323)
              ·
                refine ⟨4161735296907791488770485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2774490197938527659180323 4161735296907791488770485)
                ·
                  refine ⟨390162684085105452072233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4161735296907791488770485 390162684085105452072233)
                  ·
                    rfl

theorem cell21_1709638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1709638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709638 prefixEnd_1709638 := by exact prefixLift 1709638
  have htrace : WordTrace (prefixWord ++ tailWord_1709638) baseStart_1709638 baseEnd_1709638 := by
    simpa [prefixWord, tailWord_1709638, baseEnd_1709638] using wordTrace_append hprefix tailTrace_1709638
  have hstable : (prefixWord ++ tailWord_1709638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709638).length < 2 ^ (prefixWord ++ tailWord_1709638).sum := by decide
  have hdescent : baseEnd_1709638 < baseStart_1709638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709708 : List Nat := [2, 2, 1, 2, 1, 1, 6, 6]
def baseStart_1709708 : Nat := 118140960795 + 1709708 * 2 ^ 59
def prefixEnd_1709708 : Nat := 4983230072969 + 3 ^ 40 * 1709708 * 2
def baseEnd_1709708 : Nat := 130059553012933628635141

theorem tailTrace_1709708 : CollatzResearch.WordTrace tailWord_1709708 prefixEnd_1709708 130059553012933628635141 := by
  unfold tailWord_1709708
  simp only [CollatzResearch.WordTrace]
  refine ⟨31179086845013692862304889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41572115793351590483073185 31179086845013692862304889)
  ·
    refine ⟨23384315133760269646728667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31179086845013692862304889 23384315133760269646728667)
    ·
      refine ⟨35076472700640404470093001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23384315133760269646728667 35076472700640404470093001)
      ·
        refine ⟨26307354525480303352569751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35076472700640404470093001 26307354525480303352569751)
        ·
          refine ⟨39461031788220455028854627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26307354525480303352569751 39461031788220455028854627)
          ·
            refine ⟨59191547682330682543281941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39461031788220455028854627 59191547682330682543281941)
            ·
              refine ⟨2774603797609250744216341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59191547682330682543281941 2774603797609250744216341)
              ·
                refine ⟨130059553012933628635141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2774603797609250744216341 130059553012933628635141)
                ·
                  rfl

theorem cell21_1709708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 6].length) (baseStart_1709708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709708 prefixEnd_1709708 := by exact prefixLift 1709708
  have htrace : WordTrace (prefixWord ++ tailWord_1709708) baseStart_1709708 baseEnd_1709708 := by
    simpa [prefixWord, tailWord_1709708, baseEnd_1709708] using wordTrace_append hprefix tailTrace_1709708
  have hstable : (prefixWord ++ tailWord_1709708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709708).length < 2 ^ (prefixWord ++ tailWord_1709708).sum := by decide
  have hdescent : baseEnd_1709708 < baseStart_1709708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709742 : List Nat := [4, 1, 4, 1, 3, 8]
def baseStart_1709742 : Nat := 118140960795 + 1709742 * 2 ^ 59
def prefixEnd_1709742 : Nat := 4983230072969 + 3 ^ 40 * 1709742 * 2
def baseEnd_1709742 : Nat := 14451348826000903049581

theorem tailTrace_1709742 : CollatzResearch.WordTrace tailWord_1709742 prefixEnd_1709742 14451348826000903049581 := by
  unfold tailWord_1709742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7794926721488026191418435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41572942514602806354231653 7794926721488026191418435)
  ·
    refine ⟨11692390082232039287127653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7794926721488026191418435 11692390082232039287127653)
    ·
      refine ⟨2192323140418507366336435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11692390082232039287127653 2192323140418507366336435)
      ·
        refine ⟨3288484710627761049504653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2192323140418507366336435 3288484710627761049504653)
        ·
          refine ⟨1233181766485410393564245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3288484710627761049504653 1233181766485410393564245)
          ·
            refine ⟨14451348826000903049581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1233181766485410393564245 14451348826000903049581)
            ·
              rfl

theorem cell21_1709742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 8].length) (baseStart_1709742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709742 prefixEnd_1709742 := by exact prefixLift 1709742
  have htrace : WordTrace (prefixWord ++ tailWord_1709742) baseStart_1709742 baseEnd_1709742 := by
    simpa [prefixWord, tailWord_1709742, baseEnd_1709742] using wordTrace_append hprefix tailTrace_1709742
  have hstable : (prefixWord ++ tailWord_1709742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709742).length < 2 ^ (prefixWord ++ tailWord_1709742).sum := by decide
  have hdescent : baseEnd_1709742 < baseStart_1709742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709753 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 6]
def baseStart_1709753 : Nat := 118140960795 + 1709753 * 2 ^ 59
def prefixEnd_1709753 : Nat := 4983230072969 + 3 ^ 40 * 1709753 * 2
def baseEnd_1709753 : Nat := 390188928651890807655331

theorem tailTrace_1709753 : CollatzResearch.WordTrace tailWord_1709753 prefixEnd_1709753 390188928651890807655331 := by
  unfold tailWord_1709753
  simp only [CollatzResearch.WordTrace]
  refine ⟨62359814974864358409997913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41573209983242905606665275 62359814974864358409997913)
  ·
    refine ⟨46769861231148268807498435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62359814974864358409997913 46769861231148268807498435)
    ·
      refine ⟨70154791846722403211247653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46769861231148268807498435 70154791846722403211247653)
      ·
        refine ⟨13154023471260450602108935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70154791846722403211247653 13154023471260450602108935)
        ·
          refine ⟨19731035206890675903163403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13154023471260450602108935 19731035206890675903163403)
          ·
            refine ⟨29596552810336013854745105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19731035206890675903163403 29596552810336013854745105)
            ·
              refine ⟨22197414607752010391058829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29596552810336013854745105 22197414607752010391058829)
              ·
                refine ⟨8324030477907003896647061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22197414607752010391058829 8324030477907003896647061)
                ·
                  refine ⟨390188928651890807655331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8324030477907003896647061 390188928651890807655331)
                  ·
                    rfl

theorem cell21_1709753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_1709753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709753 prefixEnd_1709753 := by exact prefixLift 1709753
  have htrace : WordTrace (prefixWord ++ tailWord_1709753) baseStart_1709753 baseEnd_1709753 := by
    simpa [prefixWord, tailWord_1709753, baseEnd_1709753] using wordTrace_append hprefix tailTrace_1709753
  have hstable : (prefixWord ++ tailWord_1709753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709753).length < 2 ^ (prefixWord ++ tailWord_1709753).sum := by decide
  have hdescent : baseEnd_1709753 < baseStart_1709753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709773 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1709773 : Nat := 118140960795 + 1709773 * 2 ^ 59
def prefixEnd_1709773 : Nat := 4983230072969 + 3 ^ 40 * 1709773 * 2
def baseEnd_1709773 : Nat := 390193492924375217321957

theorem tailTrace_1709773 : CollatzResearch.WordTrace tailWord_1709773 prefixEnd_1709773 390193492924375217321957 := by
  unfold tailWord_1709773
  simp only [CollatzResearch.WordTrace]
  refine ⟨62360544434791901825725973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41573696289861267883817315 62360544434791901825725973)
  ·
    refine ⟨2923150520380870398080905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62360544434791901825725973 2923150520380870398080905)
    ·
      refine ⟨2192362890285652798560679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2923150520380870398080905 2192362890285652798560679)
      ·
        refine ⟨3288544335428479197841019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2192362890285652798560679 3288544335428479197841019)
        ·
          refine ⟨4932816503142718796761529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3288544335428479197841019 4932816503142718796761529)
          ·
            refine ⟨3699612377357039097571147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4932816503142718796761529 3699612377357039097571147)
            ·
              refine ⟨5549418566035558646356721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3699612377357039097571147 5549418566035558646356721)
              ·
                refine ⟨4162063924526668984767541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5549418566035558646356721 4162063924526668984767541)
                ·
                  refine ⟨390193492924375217321957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4162063924526668984767541 390193492924375217321957)
                  ·
                    rfl

theorem cell21_1709773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1709773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709773 prefixEnd_1709773 := by exact prefixLift 1709773
  have htrace : WordTrace (prefixWord ++ tailWord_1709773) baseStart_1709773 baseEnd_1709773 := by
    simpa [prefixWord, tailWord_1709773, baseEnd_1709773] using wordTrace_append hprefix tailTrace_1709773
  have hstable : (prefixWord ++ tailWord_1709773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709773).length < 2 ^ (prefixWord ++ tailWord_1709773).sum := by decide
  have hdescent : baseEnd_1709773 < baseStart_1709773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709860 : List Nat := [2, 3, 1, 3, 2, 1, 9]
def baseStart_1709860 : Nat := 118140960795 + 1709860 * 2 ^ 59
def prefixEnd_1709860 : Nat := 4983230072969 + 3 ^ 40 * 1709860 * 2
def baseEnd_1709860 : Nat := 43357038612186933263531

theorem tailTrace_1709860 : CollatzResearch.WordTrace tailWord_1709860 prefixEnd_1709860 43357038612186933263531 := by
  unfold tailWord_1709860
  simp only [CollatzResearch.WordTrace]
  refine ⟨31181858792738357842071517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41575811723651143789428689 31181858792738357842071517)
  ·
    refine ⟨11693197047276884190776819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31181858792738357842071517 11693197047276884190776819)
    ·
      refine ⟨17539795570915326286165229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11693197047276884190776819 17539795570915326286165229)
      ·
        refine ⟨6577423339093247357311961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17539795570915326286165229 6577423339093247357311961)
        ·
          refine ⟨4933067504319935517983971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6577423339093247357311961 4933067504319935517983971)
          ·
            refine ⟨7399601256479903276975957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4933067504319935517983971 7399601256479903276975957)
            ·
              refine ⟨43357038612186933263531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7399601256479903276975957 43357038612186933263531)
              ·
                rfl

theorem cell21_1709860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 9].length) (baseStart_1709860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709860 prefixEnd_1709860 := by exact prefixLift 1709860
  have htrace : WordTrace (prefixWord ++ tailWord_1709860) baseStart_1709860 baseEnd_1709860 := by
    simpa [prefixWord, tailWord_1709860, baseEnd_1709860] using wordTrace_append hprefix tailTrace_1709860
  have hstable : (prefixWord ++ tailWord_1709860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709860).length < 2 ^ (prefixWord ++ tailWord_1709860).sum := by decide
  have hdescent : baseEnd_1709860 < baseStart_1709860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709877 : List Nat := [1, 3, 3, 1, 4, 1, 2, 6]
def baseStart_1709877 : Nat := 118140960795 + 1709877 * 2 ^ 59
def prefixEnd_1709877 : Nat := 4983230072969 + 3 ^ 40 * 1709877 * 2
def baseEnd_1709877 : Nat := 130072409047098049196137

theorem tailTrace_1709877 : CollatzResearch.WordTrace tailWord_1709877 prefixEnd_1709877 130072409047098049196137 := by
  unfold tailWord_1709877
  simp only [CollatzResearch.WordTrace]
  refine ⟨62364337626415127587511885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41576225084276751725007923 62364337626415127587511885)
  ·
    refine ⟨23386626609905672845316957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62364337626415127587511885 23386626609905672845316957)
    ·
      refine ⟨8769984978714627316993859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23386626609905672845316957 8769984978714627316993859)
      ·
        refine ⟨13154977468071940975490789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8769984978714627316993859 13154977468071940975490789)
        ·
          refine ⟨2466558275263488932904523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13154977468071940975490789 2466558275263488932904523)
          ·
            refine ⟨3699837412895233399356785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2466558275263488932904523 3699837412895233399356785)
            ·
              refine ⟨2774878059671425049517589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3699837412895233399356785 2774878059671425049517589)
              ·
                refine ⟨130072409047098049196137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2774878059671425049517589 130072409047098049196137)
                ·
                  rfl

theorem cell21_1709877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 6].length) (baseStart_1709877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709877 prefixEnd_1709877 := by exact prefixLift 1709877
  have htrace : WordTrace (prefixWord ++ tailWord_1709877) baseStart_1709877 baseEnd_1709877 := by
    simpa [prefixWord, tailWord_1709877, baseEnd_1709877] using wordTrace_append hprefix tailTrace_1709877
  have hstable : (prefixWord ++ tailWord_1709877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709877).length < 2 ^ (prefixWord ++ tailWord_1709877).sum := by decide
  have hdescent : baseEnd_1709877 < baseStart_1709877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709894 : List Nat := [6, 1, 1, 2, 1, 1, 2, 7]
def baseStart_1709894 : Nat := 118140960795 + 1709894 * 2 ^ 59
def prefixEnd_1709894 : Nat := 4983230072969 + 3 ^ 40 * 1709894 * 2
def baseEnd_1709894 : Nat := 130073702257635298601681

theorem tailTrace_1709894 : CollatzResearch.WordTrace tailWord_1709894 prefixEnd_1709894 130073702257635298601681 := by
  unfold tailWord_1709894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1948904927104798109090023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41576638444902359660587157 1948904927104798109090023)
  ·
    refine ⟨2923357390657197163635035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1948904927104798109090023 2923357390657197163635035)
    ·
      refine ⟨4385036085985795745452553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2923357390657197163635035 4385036085985795745452553)
      ·
        refine ⟨3288777064489346809089415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4385036085985795745452553 3288777064489346809089415)
        ·
          refine ⟨4933165596734020213634123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3288777064489346809089415 4933165596734020213634123)
          ·
            refine ⟨7399748395101030320451185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4933165596734020213634123 7399748395101030320451185)
            ·
              refine ⟨5549811296325772740338389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7399748395101030320451185 5549811296325772740338389)
              ·
                refine ⟨130073702257635298601681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5549811296325772740338389 130073702257635298601681)
                ·
                  rfl

theorem cell21_1709894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_1709894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709894 prefixEnd_1709894 := by exact prefixLift 1709894
  have htrace : WordTrace (prefixWord ++ tailWord_1709894) baseStart_1709894 baseEnd_1709894 := by
    simpa [prefixWord, tailWord_1709894, baseEnd_1709894] using wordTrace_append hprefix tailTrace_1709894
  have hstable : (prefixWord ++ tailWord_1709894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709894).length < 2 ^ (prefixWord ++ tailWord_1709894).sum := by decide
  have hdescent : baseEnd_1709894 < baseStart_1709894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709919 : List Nat := [1, 1, 2, 3, 1, 13]
def baseStart_1709919 : Nat := 118140960795 + 1709919 * 2 ^ 59
def prefixEnd_1709919 : Nat := 4983230072969 + 3 ^ 40 * 1709919 * 2
def baseEnd_1709919 : Nat := 14452844893093015106975

theorem tailTrace_1709919 : CollatzResearch.WordTrace tailWord_1709919 prefixEnd_1709919 14452844893093015106975 := by
  unfold tailWord_1709919
  simp only [CollatzResearch.WordTrace]
  refine ⟨62365869492262968760540811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41577246328175312507027207 62365869492262968760540811)
  ·
    refine ⟨93548804238394453140811217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62365869492262968760540811 93548804238394453140811217)
    ·
      refine ⟨70161603178795839855608413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93548804238394453140811217 70161603178795839855608413)
      ·
        refine ⟨26310601192048439945853155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70161603178795839855608413 26310601192048439945853155)
        ·
          refine ⟨39465901788072659918779733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26310601192048439945853155 39465901788072659918779733)
          ·
            refine ⟨14452844893093015106975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 39465901788072659918779733 14452844893093015106975)
            ·
              rfl

theorem cell21_1709919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 13].length) (baseStart_1709919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1709919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1709919 prefixEnd_1709919 := by exact prefixLift 1709919
  have htrace : WordTrace (prefixWord ++ tailWord_1709919) baseStart_1709919 baseEnd_1709919 := by
    simpa [prefixWord, tailWord_1709919, baseEnd_1709919] using wordTrace_append hprefix tailTrace_1709919
  have hstable : (prefixWord ++ tailWord_1709919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709919).length < 2 ^ (prefixWord ++ tailWord_1709919).sum := by decide
  have hdescent : baseEnd_1709919 < baseStart_1709919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710004 : List Nat := [2, 5, 2, 1, 3, 1, 2, 5]
def baseStart_1710004 : Nat := 118140960795 + 1710004 * 2 ^ 59
def prefixEnd_1710004 : Nat := 4983230072969 + 3 ^ 40 * 1710004 * 2
def baseEnd_1710004 : Nat := 130082070090523382990495

theorem tailTrace_1710004 : CollatzResearch.WordTrace tailWord_1710004 prefixEnd_1710004 130082070090523382990495 := by
  unfold tailWord_1710004
  simp only [CollatzResearch.WordTrace]
  refine ⟨31184484848477514138692533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41579313131303352184923377 31184484848477514138692533)
  ·
    refine ⟨2923545454544766950502425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31184484848477514138692533 2923545454544766950502425)
    ·
      refine ⟨2192659090908575212876819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2923545454544766950502425 2192659090908575212876819)
      ·
        refine ⟨3288988636362862819315229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2192659090908575212876819 3288988636362862819315229)
        ·
          refine ⟨1233370738636073557243211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3288988636362862819315229 1233370738636073557243211)
          ·
            refine ⟨1850056107954110335864817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233370738636073557243211 1850056107954110335864817)
            ·
              refine ⟨1387542080965582751898613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1850056107954110335864817 1387542080965582751898613)
              ·
                refine ⟨130082070090523382990495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1387542080965582751898613 130082070090523382990495)
                ·
                  rfl

theorem cell21_1710004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 5].length) (baseStart_1710004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710004 prefixEnd_1710004 := by exact prefixLift 1710004
  have htrace : WordTrace (prefixWord ++ tailWord_1710004) baseStart_1710004 baseEnd_1710004 := by
    simpa [prefixWord, tailWord_1710004, baseEnd_1710004] using wordTrace_append hprefix tailTrace_1710004
  have hstable : (prefixWord ++ tailWord_1710004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710004).length < 2 ^ (prefixWord ++ tailWord_1710004).sum := by decide
  have hdescent : baseEnd_1710004 < baseStart_1710004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710026 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 7]
def baseStart_1710026 : Nat := 118140960795 + 1710026 * 2 ^ 59
def prefixEnd_1710026 : Nat := 4983230072969 + 3 ^ 40 * 1710026 * 2
def baseEnd_1710026 : Nat := 390251230971302999604773

theorem tailTrace_1710026 : CollatzResearch.WordTrace tailWord_1710026 prefixEnd_1710026 390251230971302999604773 := by
  unfold tailWord_1710026
  simp only [CollatzResearch.WordTrace]
  refine ⟨15592443025718831508671483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41579848068583550689790621 15592443025718831508671483)
  ·
    refine ⟨23388664538578247263007225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15592443025718831508671483 23388664538578247263007225)
    ·
      refine ⟨17541498403933685447255419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23388664538578247263007225 17541498403933685447255419)
      ·
        refine ⟨26312247605900528170883129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17541498403933685447255419 26312247605900528170883129)
        ·
          refine ⟨19734185704425396128162347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26312247605900528170883129 19734185704425396128162347)
          ·
            refine ⟨29601278556638094192243521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19734185704425396128162347 29601278556638094192243521)
            ·
              refine ⟨22200958917478570644182641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29601278556638094192243521 22200958917478570644182641)
              ·
                refine ⟨16650719188108927983136981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22200958917478570644182641 16650719188108927983136981)
                ·
                  refine ⟨390251230971302999604773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16650719188108927983136981 390251230971302999604773)
                  ·
                    rfl

theorem cell21_1710026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_1710026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710026 prefixEnd_1710026 := by exact prefixLift 1710026
  have htrace : WordTrace (prefixWord ++ tailWord_1710026) baseStart_1710026 baseEnd_1710026 := by
    simpa [prefixWord, tailWord_1710026, baseEnd_1710026] using wordTrace_append hprefix tailTrace_1710026
  have hstable : (prefixWord ++ tailWord_1710026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710026).length < 2 ^ (prefixWord ++ tailWord_1710026).sum := by decide
  have hdescent : baseEnd_1710026 < baseStart_1710026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710086 : List Nat := [6, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1710086 : Nat := 118140960795 + 1710086 * 2 ^ 59
def prefixEnd_1710086 : Nat := 4983230072969 + 3 ^ 40 * 1710086 * 2
def baseEnd_1710086 : Nat := 390264923788756228604651

theorem tailTrace_1710086 : CollatzResearch.WordTrace tailWord_1710086 prefixEnd_1710086 390264923788756228604651 := by
  unfold tailWord_1710086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1949123765083061133808441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41581306988438637521246741 1949123765083061133808441)
  ·
    refine ⟨1461842823812295850356331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1949123765083061133808441 1461842823812295850356331)
    ·
      refine ⟨2192764235718443775534497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1461842823812295850356331 2192764235718443775534497)
      ·
        refine ⟨1644573176788832831650873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2192764235718443775534497 1644573176788832831650873)
        ·
          refine ⟨1233429882591624623738155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1644573176788832831650873 1233429882591624623738155)
          ·
            refine ⟨1850144823887436935607233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233429882591624623738155 1850144823887436935607233)
            ·
              refine ⟨1387608617915577701705425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1850144823887436935607233 1387608617915577701705425)
              ·
                refine ⟨1040706463436683276279069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387608617915577701705425 1040706463436683276279069)
                ·
                  refine ⟨390264923788756228604651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040706463436683276279069 390264923788756228604651)
                  ·
                    rfl

theorem cell21_1710086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1710086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710086 prefixEnd_1710086 := by exact prefixLift 1710086
  have htrace : WordTrace (prefixWord ++ tailWord_1710086) baseStart_1710086 baseEnd_1710086 := by
    simpa [prefixWord, tailWord_1710086, baseEnd_1710086] using wordTrace_append hprefix tailTrace_1710086
  have hstable : (prefixWord ++ tailWord_1710086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710086).length < 2 ^ (prefixWord ++ tailWord_1710086).sum := by decide
  have hdescent : baseEnd_1710086 < baseStart_1710086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710181 : List Nat := [1, 3, 1, 3, 2, 4, 2, 5]
def baseStart_1710181 : Nat := 118140960795 + 1710181 * 2 ^ 59
def prefixEnd_1710181 : Nat := 4983230072969 + 3 ^ 40 * 1710181 * 2
def baseEnd_1710181 : Nat := 130095534694352391507041

theorem tailTrace_1710181 : CollatzResearch.WordTrace tailWord_1710181 prefixEnd_1710181 130095534694352391507041 := by
  unfold tailWord_1710181
  simp only [CollatzResearch.WordTrace]
  refine ⟨62375425417313787506578397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41583616944875858337718931 62375425417313787506578397)
  ·
    refine ⟨23390784531492670314966899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62375425417313787506578397 23390784531492670314966899)
    ·
      refine ⟨35086176797239005472450349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23390784531492670314966899 35086176797239005472450349)
      ·
        refine ⟨13157316298964627052168881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35086176797239005472450349 13157316298964627052168881)
        ·
          refine ⟨9867987224223470289126661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13157316298964627052168881 9867987224223470289126661)
          ·
            refine ⟨1850247604541900679211249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9867987224223470289126661 1850247604541900679211249)
            ·
              refine ⟨1387685703406425509408437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1850247604541900679211249 1387685703406425509408437)
              ·
                refine ⟨130095534694352391507041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1387685703406425509408437 130095534694352391507041)
                ·
                  rfl

theorem cell21_1710181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 5].length) (baseStart_1710181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710181 prefixEnd_1710181 := by exact prefixLift 1710181
  have htrace : WordTrace (prefixWord ++ tailWord_1710181) baseStart_1710181 baseEnd_1710181 := by
    simpa [prefixWord, tailWord_1710181, baseEnd_1710181] using wordTrace_append hprefix tailTrace_1710181
  have hstable : (prefixWord ++ tailWord_1710181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710181).length < 2 ^ (prefixWord ++ tailWord_1710181).sum := by decide
  have hdescent : baseEnd_1710181 < baseStart_1710181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710226 : List Nat := [3, 2, 3, 1, 1, 1, 3, 3, 4]
def baseStart_1710226 : Nat := 118140960795 + 1710226 * 2 ^ 59
def prefixEnd_1710226 : Nat := 4983230072969 + 3 ^ 40 * 1710226 * 2
def baseEnd_1710226 : Nat := 390296873696147096271031

theorem tailTrace_1710226 : CollatzResearch.WordTrace tailWord_1710226 prefixEnd_1710226 390296873696147096271031 := by
  unfold tailWord_1710226
  simp only [CollatzResearch.WordTrace]
  refine ⟨15594266675537690047991633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41584711134767173461311021 15594266675537690047991633)
  ·
    refine ⟨11695700006653267535993725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15594266675537690047991633 11695700006653267535993725)
    ·
      refine ⟨4385887502494975325997647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11695700006653267535993725 4385887502494975325997647)
      ·
        refine ⟨6578831253742462988996471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4385887502494975325997647 6578831253742462988996471)
        ·
          refine ⟨9868246880613694483494707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6578831253742462988996471 9868246880613694483494707)
          ·
            refine ⟨14802370320920541725242061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9868246880613694483494707 14802370320920541725242061)
            ·
              refine ⟨5550888870345203146965773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14802370320920541725242061 5550888870345203146965773)
              ·
                refine ⟨2081583326379451180112165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5550888870345203146965773 2081583326379451180112165)
                ·
                  refine ⟨390296873696147096271031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2081583326379451180112165 390296873696147096271031)
                  ·
                    rfl

theorem cell21_1710226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_1710226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710226 prefixEnd_1710226 := by exact prefixLift 1710226
  have htrace : WordTrace (prefixWord ++ tailWord_1710226) baseStart_1710226 baseEnd_1710226 := by
    simpa [prefixWord, tailWord_1710226, baseEnd_1710226] using wordTrace_append hprefix tailTrace_1710226
  have hstable : (prefixWord ++ tailWord_1710226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710226).length < 2 ^ (prefixWord ++ tailWord_1710226).sum := by decide
  have hdescent : baseEnd_1710226 < baseStart_1710226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710274 : List Nat := [3, 5, 1, 1, 1, 1, 3, 6]
def baseStart_1710274 : Nat := 118140960795 + 1710274 * 2 ^ 59
def prefixEnd_1710274 : Nat := 4983230072969 + 3 ^ 40 * 1710274 * 2
def baseEnd_1710274 : Nat := 130102609316703226490311

theorem tailTrace_1710274 : CollatzResearch.WordTrace tailWord_1710274 prefixEnd_1710274 130102609316703226490311 := by
  unfold tailWord_1710274
  simp only [CollatzResearch.WordTrace]
  refine ⟨15594704351494216097428469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41585878270651242926475917 15594704351494216097428469)
  ·
    refine ⟨1462003532952582759133919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15594704351494216097428469 1462003532952582759133919)
    ·
      refine ⟨2193005299428874138700879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1462003532952582759133919 2193005299428874138700879)
      ·
        refine ⟨3289507949143311208051319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2193005299428874138700879 3289507949143311208051319)
        ·
          refine ⟨4934261923714966812076979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3289507949143311208051319 4934261923714966812076979)
          ·
            refine ⟨7401392885572450218115469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4934261923714966812076979 7401392885572450218115469)
            ·
              refine ⟨2775522332089668831793301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7401392885572450218115469 2775522332089668831793301)
              ·
                refine ⟨130102609316703226490311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2775522332089668831793301 130102609316703226490311)
                ·
                  rfl

theorem cell21_1710274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_1710274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710274 prefixEnd_1710274 := by exact prefixLift 1710274
  have htrace : WordTrace (prefixWord ++ tailWord_1710274) baseStart_1710274 baseEnd_1710274 := by
    simpa [prefixWord, tailWord_1710274, baseEnd_1710274] using wordTrace_append hprefix tailTrace_1710274
  have hstable : (prefixWord ++ tailWord_1710274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710274).length < 2 ^ (prefixWord ++ tailWord_1710274).sum := by decide
  have hdescent : baseEnd_1710274 < baseStart_1710274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710330 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 5]
def baseStart_1710330 : Nat := 118140960795 + 1710330 * 2 ^ 59
def prefixEnd_1710330 : Nat := 4983230072969 + 3 ^ 40 * 1710330 * 2
def baseEnd_1710330 : Nat := 390320607913066026537485

theorem tailTrace_1710330 : CollatzResearch.WordTrace tailWord_1710330 prefixEnd_1710330 390320607913066026537485 := by
  unfold tailWord_1710330
  simp only [CollatzResearch.WordTrace]
  refine ⟨15595214973443496488438111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41587239929182657302501629 15595214973443496488438111)
  ·
    refine ⟨23392822460165244732657167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15595214973443496488438111 23392822460165244732657167)
    ·
      refine ⟨35089233690247867098985751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23392822460165244732657167 35089233690247867098985751)
      ·
        refine ⟨52633850535371800648478627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35089233690247867098985751 52633850535371800648478627)
        ·
          refine ⟨78950775803057700972717941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52633850535371800648478627 78950775803057700972717941)
          ·
            refine ⟨7401635231536659466192307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78950775803057700972717941 7401635231536659466192307)
            ·
              refine ⟨11102452847304989199288461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7401635231536659466192307 11102452847304989199288461)
              ·
                refine ⟨4163419817739370949733173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11102452847304989199288461 4163419817739370949733173)
                ·
                  refine ⟨390320607913066026537485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4163419817739370949733173 390320607913066026537485)
                  ·
                    rfl

theorem cell21_1710330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_1710330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710330 prefixEnd_1710330 := by exact prefixLift 1710330
  have htrace : WordTrace (prefixWord ++ tailWord_1710330) baseStart_1710330 baseEnd_1710330 := by
    simpa [prefixWord, tailWord_1710330, baseEnd_1710330] using wordTrace_append hprefix tailTrace_1710330
  have hstable : (prefixWord ++ tailWord_1710330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710330).length < 2 ^ (prefixWord ++ tailWord_1710330).sum := by decide
  have hdescent : baseEnd_1710330 < baseStart_1710330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710381 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 5]
def baseStart_1710381 : Nat := 118140960795 + 1710381 * 2 ^ 59
def prefixEnd_1710381 : Nat := 4983230072969 + 3 ^ 40 * 1710381 * 2
def baseEnd_1710381 : Nat := 390332246807901271187381

theorem tailTrace_1710381 : CollatzResearch.WordTrace tailWord_1710381 prefixEnd_1710381 390332246807901271187381 := by
  unfold tailWord_1710381
  simp only [CollatzResearch.WordTrace]
  refine ⟨62382720016589221663858997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41588480011059481109239331 62382720016589221663858997)
  ·
    refine ⟨5848380001555239530986781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62382720016589221663858997 5848380001555239530986781)
    ·
      refine ⟨2193142500583214824120043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5848380001555239530986781 2193142500583214824120043)
      ·
        refine ⟨3289713750874822236180065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2193142500583214824120043 3289713750874822236180065)
        ·
          refine ⟨2467285313156116677135049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3289713750874822236180065 2467285313156116677135049)
          ·
            refine ⟨1850463984867087507851287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2467285313156116677135049 1850463984867087507851287)
            ·
              refine ⟨2775695977300631261776931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850463984867087507851287 2775695977300631261776931)
              ·
                refine ⟨4163543965950946892665397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2775695977300631261776931 4163543965950946892665397)
                ·
                  refine ⟨390332246807901271187381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4163543965950946892665397 390332246807901271187381)
                  ·
                    rfl

theorem cell21_1710381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_1710381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710381 prefixEnd_1710381 := by exact prefixLift 1710381
  have htrace : WordTrace (prefixWord ++ tailWord_1710381) baseStart_1710381 baseEnd_1710381 := by
    simpa [prefixWord, tailWord_1710381, baseEnd_1710381] using wordTrace_append hprefix tailTrace_1710381
  have hstable : (prefixWord ++ tailWord_1710381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710381).length < 2 ^ (prefixWord ++ tailWord_1710381).sum := by decide
  have hdescent : baseEnd_1710381 < baseStart_1710381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710423 : List Nat := [1, 1, 3, 2, 3, 1, 2, 5, 3]
def baseStart_1710423 : Nat := 118140960795 + 1710423 * 2 ^ 59
def prefixEnd_1710423 : Nat := 4983230072969 + 3 ^ 40 * 1710423 * 2
def baseEnd_1710423 : Nat := 390341831780118531487295

theorem tailTrace_1710423 : CollatzResearch.WordTrace tailWord_1710423 prefixEnd_1710423 390341831780118531487295 := by
  unfold tailWord_1710423
  simp only [CollatzResearch.WordTrace]
  refine ⟨62384251882437062836887923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41589501254958041891258615 62384251882437062836887923)
  ·
    refine ⟨93576377823655594255331885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62384251882437062836887923 93576377823655594255331885)
    ·
      refine ⟨35091141683870847845749457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93576377823655594255331885 35091141683870847845749457)
      ·
        refine ⟨26318356262903135884312093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35091141683870847845749457 26318356262903135884312093)
        ·
          refine ⟨9869383598588675956617035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26318356262903135884312093 9869383598588675956617035)
          ·
            refine ⟨14804075397883013934925553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9869383598588675956617035 14804075397883013934925553)
            ·
              refine ⟨11103056548412260451194165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14804075397883013934925553 11103056548412260451194165)
              ·
                refine ⟨1040911551413649417299453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11103056548412260451194165 1040911551413649417299453)
                ·
                  refine ⟨390341831780118531487295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040911551413649417299453 390341831780118531487295)
                  ·
                    rfl

theorem cell21_1710423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 3].length) (baseStart_1710423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710423 prefixEnd_1710423 := by exact prefixLift 1710423
  have htrace : WordTrace (prefixWord ++ tailWord_1710423) baseStart_1710423 baseEnd_1710423 := by
    simpa [prefixWord, tailWord_1710423, baseEnd_1710423] using wordTrace_append hprefix tailTrace_1710423
  have hstable : (prefixWord ++ tailWord_1710423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710423).length < 2 ^ (prefixWord ++ tailWord_1710423).sum := by decide
  have hdescent : baseEnd_1710423 < baseStart_1710423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710437 : List Nat := [1, 3, 1, 3, 1, 3, 1, 4, 4]
def baseStart_1710437 : Nat := 118140960795 + 1710437 * 2 ^ 59
def prefixEnd_1710437 : Nat := 4983230072969 + 3 ^ 40 * 1710437 * 2
def baseEnd_1710437 : Nat := 390345026770857618253933

theorem tailTrace_1710437 : CollatzResearch.WordTrace tailWord_1710437 prefixEnd_1710437 390345026770857618253933 := by
  unfold tailWord_1710437
  simp only [CollatzResearch.WordTrace]
  refine ⟨62384762504386343227897565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41589841669590895485265043 62384762504386343227897565)
  ·
    refine ⟨23394285939144878710461587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62384762504386343227897565 23394285939144878710461587)
    ·
      refine ⟨35091428908717318065692381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23394285939144878710461587 35091428908717318065692381)
      ·
        refine ⟨13159285840768994274634643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35091428908717318065692381 13159285840768994274634643)
        ·
          refine ⟨19738928761153491411951965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13159285840768994274634643 19738928761153491411951965)
          ·
            refine ⟨7402098285432559279481987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19738928761153491411951965 7402098285432559279481987)
            ·
              refine ⟨11103147428148838919222981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7402098285432559279481987 11103147428148838919222981)
              ·
                refine ⟨2081840142777907297354309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11103147428148838919222981 2081840142777907297354309)
                ·
                  refine ⟨390345026770857618253933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2081840142777907297354309 390345026770857618253933)
                  ·
                    rfl

theorem cell21_1710437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_1710437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710437 prefixEnd_1710437 := by exact prefixLift 1710437
  have htrace : WordTrace (prefixWord ++ tailWord_1710437) baseStart_1710437 baseEnd_1710437 := by
    simpa [prefixWord, tailWord_1710437, baseEnd_1710437] using wordTrace_append hprefix tailTrace_1710437
  have hstable : (prefixWord ++ tailWord_1710437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710437).length < 2 ^ (prefixWord ++ tailWord_1710437).sum := by decide
  have hdescent : baseEnd_1710437 < baseStart_1710437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710440 : List Nat := [2, 1, 4, 2, 2, 2, 1, 4, 3]
def baseStart_1710440 : Nat := 118140960795 + 1710440 * 2 ^ 59
def prefixEnd_1710440 : Nat := 4983230072969 + 3 ^ 40 * 1710440 * 2
def baseEnd_1710440 : Nat := 390345711411730279703927

theorem tailTrace_1710440 : CollatzResearch.WordTrace tailWord_1710440 prefixEnd_1710440 390345711411730279703927 := by
  unfold tailWord_1710440
  simp only [CollatzResearch.WordTrace]
  refine ⟨31192435961687737370128387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41589914615583649826837849 31192435961687737370128387)
  ·
    refine ⟨46788653942531606055192581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31192435961687737370128387 46788653942531606055192581)
    ·
      refine ⟨8772872614224676135348609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46788653942531606055192581 8772872614224676135348609)
      ·
        refine ⟨6579654460668507101511457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8772872614224676135348609 6579654460668507101511457)
        ·
          refine ⟨4934740845501380326133593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6579654460668507101511457 4934740845501380326133593)
          ·
            refine ⟨3701055634126035244600195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4934740845501380326133593 3701055634126035244600195)
            ·
              refine ⟨5551583451189052866900293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3701055634126035244600195 5551583451189052866900293)
              ·
                refine ⟨1040921897097947412543805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5551583451189052866900293 1040921897097947412543805)
                ·
                  refine ⟨390345711411730279703927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040921897097947412543805 390345711411730279703927)
                  ·
                    rfl

theorem cell21_1710440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 3].length) (baseStart_1710440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710440 prefixEnd_1710440 := by exact prefixLift 1710440
  have htrace : WordTrace (prefixWord ++ tailWord_1710440) baseStart_1710440 baseEnd_1710440 := by
    simpa [prefixWord, tailWord_1710440, baseEnd_1710440] using wordTrace_append hprefix tailTrace_1710440
  have hstable : (prefixWord ++ tailWord_1710440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710440).length < 2 ^ (prefixWord ++ tailWord_1710440).sum := by decide
  have hdescent : baseEnd_1710440 < baseStart_1710440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710468 : List Nat := [2, 3, 2, 1, 1, 2, 5, 5]
def baseStart_1710468 : Nat := 118140960795 + 1710468 * 2 ^ 59
def prefixEnd_1710468 : Nat := 4983230072969 + 3 ^ 40 * 1710468 * 2
def baseEnd_1710468 : Nat := 130117367131069484412401

theorem tailTrace_1710468 : CollatzResearch.WordTrace tailWord_1710468 prefixEnd_1710468 130117367131069484412401 := by
  unfold tailWord_1710468
  simp only [CollatzResearch.WordTrace]
  refine ⟨31192946583637017761138029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41590595444849357014850705 31192946583637017761138029)
  ·
    refine ⟨11697354968863881660426761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31192946583637017761138029 11697354968863881660426761)
    ·
      refine ⟨8773016226647911245320071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11697354968863881660426761 8773016226647911245320071)
      ·
        refine ⟨13159524339971866867980107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8773016226647911245320071 13159524339971866867980107)
        ·
          refine ⟨19739286509957800301970161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13159524339971866867980107 19739286509957800301970161)
          ·
            refine ⟨14804464882468350226477621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19739286509957800301970161 14804464882468350226477621)
            ·
              refine ⟨1387918582731407833732277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14804464882468350226477621 1387918582731407833732277)
              ·
                refine ⟨130117367131069484412401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1387918582731407833732277 130117367131069484412401)
                ·
                  rfl

theorem cell21_1710468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 5].length) (baseStart_1710468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710468 prefixEnd_1710468 := by exact prefixLift 1710468
  have htrace : WordTrace (prefixWord ++ tailWord_1710468) baseStart_1710468 baseEnd_1710468 := by
    simpa [prefixWord, tailWord_1710468, baseEnd_1710468] using wordTrace_append hprefix tailTrace_1710468
  have hstable : (prefixWord ++ tailWord_1710468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710468).length < 2 ^ (prefixWord ++ tailWord_1710468).sum := by decide
  have hdescent : baseEnd_1710468 < baseStart_1710468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710499 : List Nat := [1, 1, 1, 4, 1, 4, 2, 4, 3]
def baseStart_1710499 : Nat := 118140960795 + 1710499 * 2 ^ 59
def prefixEnd_1710499 : Nat := 4983230072969 + 3 ^ 40 * 1710499 * 2
def baseEnd_1710499 : Nat := 390359176015559288220473

theorem tailTrace_1710499 : CollatzResearch.WordTrace tailWord_1710499 prefixEnd_1710499 390359176015559288220473 := by
  unfold tailWord_1710499
  simp only [CollatzResearch.WordTrace]
  refine ⟨62387023830161727816654551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41591349220107818544436367 62387023830161727816654551)
  ·
    refine ⟨93580535745242591724981827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62387023830161727816654551 93580535745242591724981827)
    ·
      refine ⟨140370803617863887587472741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93580535745242591724981827 140370803617863887587472741)
      ·
        refine ⟨26319525678349478922651139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140370803617863887587472741 26319525678349478922651139)
        ·
          refine ⟨39479288517524218383976709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26319525678349478922651139 39479288517524218383976709)
          ·
            refine ⟨7402366597035790946995633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39479288517524218383976709 7402366597035790946995633)
            ·
              refine ⟨5551774947776843210246725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7402366597035790946995633 5551774947776843210246725)
              ·
                refine ⟨1040957802708158101921261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5551774947776843210246725 1040957802708158101921261)
                ·
                  refine ⟨390359176015559288220473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040957802708158101921261 390359176015559288220473)
                  ·
                    rfl

theorem cell21_1710499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 3].length) (baseStart_1710499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710499 prefixEnd_1710499 := by exact prefixLift 1710499
  have htrace : WordTrace (prefixWord ++ tailWord_1710499) baseStart_1710499 baseEnd_1710499 := by
    simpa [prefixWord, tailWord_1710499, baseEnd_1710499] using wordTrace_append hprefix tailTrace_1710499
  have hstable : (prefixWord ++ tailWord_1710499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710499).length < 2 ^ (prefixWord ++ tailWord_1710499).sum := by decide
  have hdescent : baseEnd_1710499 < baseStart_1710499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710606 : List Nat := [4, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_1710606 : Nat := 118140960795 + 1710606 * 2 ^ 59
def prefixEnd_1710606 : Nat := 4983230072969 + 3 ^ 40 * 1710606 * 2
def baseEnd_1710606 : Nat := 390383594873350879936921

theorem tailTrace_1710606 : CollatzResearch.WordTrace tailWord_1710606 prefixEnd_1710606 390383594873350879936921 := by
  unfold tailWord_1710606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7798865805096760636349959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41593950960516056727199781 7798865805096760636349959)
  ·
    refine ⟨11698298707645140954524939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7798865805096760636349959 11698298707645140954524939)
    ·
      refine ⟨17547448061467711431787409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11698298707645140954524939 17547448061467711431787409)
      ·
        refine ⟨13160586046100783573840557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17547448061467711431787409 13160586046100783573840557)
        ·
          refine ⟨4935219767287793840190209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13160586046100783573840557 4935219767287793840190209)
          ·
            refine ⟨3701414825465845380142657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4935219767287793840190209 3701414825465845380142657)
            ·
              refine ⟨2776061119099384035106993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3701414825465845380142657 2776061119099384035106993)
              ·
                refine ⟨2082045839324538026330245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2776061119099384035106993 2082045839324538026330245)
                ·
                  refine ⟨390383594873350879936921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2082045839324538026330245 390383594873350879936921)
                  ·
                    rfl

theorem cell21_1710606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_1710606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710606 prefixEnd_1710606 := by exact prefixLift 1710606
  have htrace : WordTrace (prefixWord ++ tailWord_1710606) baseStart_1710606 baseEnd_1710606 := by
    simpa [prefixWord, tailWord_1710606, baseEnd_1710606] using wordTrace_append hprefix tailTrace_1710606
  have hstable : (prefixWord ++ tailWord_1710606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710606).length < 2 ^ (prefixWord ++ tailWord_1710606).sum := by decide
  have hdescent : baseEnd_1710606 < baseStart_1710606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710620 : List Nat := [2, 2, 3, 1, 2, 4, 1, 6]
def baseStart_1710620 : Nat := 118140960795 + 1710620 * 2 ^ 59
def prefixEnd_1710620 : Nat := 4983230072969 + 3 ^ 40 * 1710620 * 2
def baseEnd_1710620 : Nat := 130128929954696655567853

theorem tailTrace_1710620 : CollatzResearch.WordTrace tailWord_1710620 prefixEnd_1710620 130128929954696655567853 := by
  unfold tailWord_1710620
  simp only [CollatzResearch.WordTrace]
  refine ⟨31195718531361682740904657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41594291375148910321206209 31195718531361682740904657)
  ·
    refine ⟨23396788898521262055678493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31195718531361682740904657 23396788898521262055678493)
    ·
      refine ⟨8773795836945473270879435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23396788898521262055678493 8773795836945473270879435)
      ·
        refine ⟨13160693755418209906319153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8773795836945473270879435 13160693755418209906319153)
        ·
          refine ⟨9870520316563657429739365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13160693755418209906319153 9870520316563657429739365)
          ·
            refine ⟨1850722559355685768076131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9870520316563657429739365 1850722559355685768076131)
            ·
              refine ⟨2776083839033528652114197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850722559355685768076131 2776083839033528652114197)
              ·
                refine ⟨130128929954696655567853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2776083839033528652114197 130128929954696655567853)
                ·
                  rfl

theorem cell21_1710620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 6].length) (baseStart_1710620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710620 prefixEnd_1710620 := by exact prefixLift 1710620
  have htrace : WordTrace (prefixWord ++ tailWord_1710620) baseStart_1710620 baseEnd_1710620 := by
    simpa [prefixWord, tailWord_1710620, baseEnd_1710620] using wordTrace_append hprefix tailTrace_1710620
  have hstable : (prefixWord ++ tailWord_1710620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710620).length < 2 ^ (prefixWord ++ tailWord_1710620).sum := by decide
  have hdescent : baseEnd_1710620 < baseStart_1710620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710634 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 7]
def baseStart_1710634 : Nat := 118140960795 + 1710634 * 2 ^ 59
def prefixEnd_1710634 : Nat := 4983230072969 + 3 ^ 40 * 1710634 * 2
def baseEnd_1710634 : Nat := 390389984854829053470197

theorem tailTrace_1710634 : CollatzResearch.WordTrace tailWord_1710634 prefixEnd_1710634 390389984854829053470197 := by
  unfold tailWord_1710634
  simp only [CollatzResearch.WordTrace]
  refine ⟨15597986921168161468204739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41594631789781763915212637 15597986921168161468204739)
  ·
    refine ⟨23396980381752242202307109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15597986921168161468204739 23396980381752242202307109)
    ·
      refine ⟨4386933821578545412932583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23396980381752242202307109 4386933821578545412932583)
      ·
        refine ⟨6580400732367818119398875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4386933821578545412932583 6580400732367818119398875)
        ·
          refine ⟨9870601098551727179098313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6580400732367818119398875 9870601098551727179098313)
          ·
            refine ⟨7402950823913795384323735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9870601098551727179098313 7402950823913795384323735)
            ·
              refine ⟨11104426235870693076485603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7402950823913795384323735 11104426235870693076485603)
              ·
                refine ⟨16656639353806039614728405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11104426235870693076485603 16656639353806039614728405)
                ·
                  refine ⟨390389984854829053470197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16656639353806039614728405 390389984854829053470197)
                  ·
                    rfl

theorem cell21_1710634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_1710634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710634 prefixEnd_1710634 := by exact prefixLift 1710634
  have htrace : WordTrace (prefixWord ++ tailWord_1710634) baseStart_1710634 baseEnd_1710634 := by
    simpa [prefixWord, tailWord_1710634, baseEnd_1710634] using wordTrace_append hprefix tailTrace_1710634
  have hstable : (prefixWord ++ tailWord_1710634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710634).length < 2 ^ (prefixWord ++ tailWord_1710634).sum := by decide
  have hdescent : baseEnd_1710634 < baseStart_1710634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710648 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 6]
def baseStart_1710648 : Nat := 118140960795 + 1710648 * 2 ^ 59
def prefixEnd_1710648 : Nat := 4983230072969 + 3 ^ 40 * 1710648 * 2
def baseEnd_1710648 : Nat := 390393179845568140236835

theorem tailTrace_1710648 : CollatzResearch.WordTrace tailWord_1710648 prefixEnd_1710648 390393179845568140236835 := by
  unfold tailWord_1710648
  simp only [CollatzResearch.WordTrace]
  refine ⟨31196229153310963131914299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41594972204414617509219065 31196229153310963131914299)
  ·
    refine ⟨46794343729966444697871449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31196229153310963131914299 46794343729966444697871449)
    ·
      refine ⟨35095757797474833523403587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46794343729966444697871449 35095757797474833523403587)
      ·
        refine ⟨52643636696212250285105381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35095757797474833523403587 52643636696212250285105381)
        ·
          refine ⟨9870681880539796928457259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52643636696212250285105381 9870681880539796928457259)
          ·
            refine ⟨14806022820809695392685889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9870681880539796928457259 14806022820809695392685889)
            ·
              refine ⟨11104517115607271544514417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14806022820809695392685889 11104517115607271544514417)
              ·
                refine ⟨8328387836705453658385813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11104517115607271544514417 8328387836705453658385813)
                ·
                  refine ⟨390393179845568140236835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8328387836705453658385813 390393179845568140236835)
                  ·
                    rfl

theorem cell21_1710648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_1710648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710648 prefixEnd_1710648 := by exact prefixLift 1710648
  have htrace : WordTrace (prefixWord ++ tailWord_1710648) baseStart_1710648 baseEnd_1710648 := by
    simpa [prefixWord, tailWord_1710648, baseEnd_1710648] using wordTrace_append hprefix tailTrace_1710648
  have hstable : (prefixWord ++ tailWord_1710648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710648).length < 2 ^ (prefixWord ++ tailWord_1710648).sum := by decide
  have hdescent : baseEnd_1710648 < baseStart_1710648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710696 : List Nat := [2, 1, 4, 3, 2, 1, 1, 7]
def baseStart_1710696 : Nat := 118140960795 + 1710696 * 2 ^ 59
def prefixEnd_1710696 : Nat := 4983230072969 + 3 ^ 40 * 1710696 * 2
def baseEnd_1710696 : Nat := 130134711366510241145579

theorem tailTrace_1710696 : CollatzResearch.WordTrace tailWord_1710696 prefixEnd_1710696 130134711366510241145579 := by
  unfold tailWord_1710696
  simp only [CollatzResearch.WordTrace]
  refine ⟨31197104505224015230787971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41596139340298686974383961 31197104505224015230787971)
  ·
    refine ⟨46795656757836022846181957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31197104505224015230787971 46795656757836022846181957)
    ·
      refine ⟨8774185642094254283659117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46795656757836022846181957 8774185642094254283659117)
      ·
        refine ⟨3290319615785345356372169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8774185642094254283659117 3290319615785345356372169)
        ·
          refine ⟨2467739711839009017279127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3290319615785345356372169 2467739711839009017279127)
          ·
            refine ⟨3701609567758513525918691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467739711839009017279127 3701609567758513525918691)
            ·
              refine ⟨5552414351637770288878037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3701609567758513525918691 5552414351637770288878037)
              ·
                refine ⟨130134711366510241145579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5552414351637770288878037 130134711366510241145579)
                ·
                  rfl

theorem cell21_1710696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 7].length) (baseStart_1710696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710696 prefixEnd_1710696 := by exact prefixLift 1710696
  have htrace : WordTrace (prefixWord ++ tailWord_1710696) baseStart_1710696 baseEnd_1710696 := by
    simpa [prefixWord, tailWord_1710696, baseEnd_1710696] using wordTrace_append hprefix tailTrace_1710696
  have hstable : (prefixWord ++ tailWord_1710696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710696).length < 2 ^ (prefixWord ++ tailWord_1710696).sum := by decide
  have hdescent : baseEnd_1710696 < baseStart_1710696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710834 : List Nat := [3, 2, 1, 3, 1, 4, 1, 2, 4]
def baseStart_1710834 : Nat := 118140960795 + 1710834 * 2 ^ 59
def prefixEnd_1710834 : Nat := 4983230072969 + 3 ^ 40 * 1710834 * 2
def baseEnd_1710834 : Nat := 390435627579673150136455

theorem tailTrace_1710834 : CollatzResearch.WordTrace tailWord_1710834 prefixEnd_1710834 390435627579673150136455 := by
  unfold tailWord_1710834
  simp only [CollatzResearch.WordTrace]
  refine ⟨15599810570987020007524889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41599494855965386686733037 15599810570987020007524889)
  ·
    refine ⟨11699857928240265005643667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15599810570987020007524889 11699857928240265005643667)
    ·
      refine ⟨17549786892360397508465501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11699857928240265005643667 17549786892360397508465501)
      ·
        refine ⟨6581170084635149065674563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17549786892360397508465501 6581170084635149065674563)
        ·
          refine ⟨9871755126952723598511845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6581170084635149065674563 9871755126952723598511845)
          ·
            refine ⟨1850954086303635674720971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9871755126952723598511845 1850954086303635674720971)
            ·
              refine ⟨2776431129455453512081457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850954086303635674720971 2776431129455453512081457)
              ·
                refine ⟨2082323347091590134061093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2776431129455453512081457 2082323347091590134061093)
                ·
                  refine ⟨390435627579673150136455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2082323347091590134061093 390435627579673150136455)
                  ·
                    rfl

theorem cell21_1710834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_1710834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710834 prefixEnd_1710834 := by exact prefixLift 1710834
  have htrace : WordTrace (prefixWord ++ tailWord_1710834) baseStart_1710834 baseEnd_1710834 := by
    simpa [prefixWord, tailWord_1710834, baseEnd_1710834] using wordTrace_append hprefix tailTrace_1710834
  have hstable : (prefixWord ++ tailWord_1710834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710834).length < 2 ^ (prefixWord ++ tailWord_1710834).sum := by decide
  have hdescent : baseEnd_1710834 < baseStart_1710834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710837 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 5]
def baseStart_1710837 : Nat := 118140960795 + 1710837 * 2 ^ 59
def prefixEnd_1710837 : Nat := 4983230072969 + 3 ^ 40 * 1710837 * 2
def baseEnd_1710837 : Nat := 390436312220545811586449

theorem tailTrace_1710837 : CollatzResearch.WordTrace tailWord_1710837 prefixEnd_1710837 390436312220545811586449 := by
  unfold tailWord_1710837
  simp only [CollatzResearch.WordTrace]
  refine ⟨62399351702937211542458765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41599567801958141028305843 62399351702937211542458765)
  ·
    refine ⟨23399756888601454328422037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62399351702937211542458765 23399756888601454328422037)
    ·
      refine ⟨1096863604153193171644783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23399756888601454328422037 1096863604153193171644783)
      ·
        refine ⟨1645295406229789757467175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096863604153193171644783 1645295406229789757467175)
        ·
          refine ⟨2467943109344684636200763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1645295406229789757467175 2467943109344684636200763)
          ·
            refine ⟨3701914664017026954301145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467943109344684636200763 3701914664017026954301145)
            ·
              refine ⟨2776435998012770215725859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3701914664017026954301145 2776435998012770215725859)
              ·
                refine ⟨4164653997019155323588789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776435998012770215725859 4164653997019155323588789)
                ·
                  refine ⟨390436312220545811586449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4164653997019155323588789 390436312220545811586449)
                  ·
                    rfl

theorem cell21_1710837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_1710837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710837 prefixEnd_1710837 := by exact prefixLift 1710837
  have htrace : WordTrace (prefixWord ++ tailWord_1710837) baseStart_1710837 baseEnd_1710837 := by
    simpa [prefixWord, tailWord_1710837, baseEnd_1710837] using wordTrace_append hprefix tailTrace_1710837
  have hstable : (prefixWord ++ tailWord_1710837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710837).length < 2 ^ (prefixWord ++ tailWord_1710837).sum := by decide
  have hdescent : baseEnd_1710837 < baseStart_1710837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710876 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 6]
def baseStart_1710876 : Nat := 118140960795 + 1710876 * 2 ^ 59
def prefixEnd_1710876 : Nat := 4983230072969 + 3 ^ 40 * 1710876 * 2
def baseEnd_1710876 : Nat := 390445212551890410436369

theorem tailTrace_1710876 : CollatzResearch.WordTrace tailWord_1710876 prefixEnd_1710876 390445212551890410436369 := by
  unfold tailWord_1710876
  simp only [CollatzResearch.WordTrace]
  refine ⟨31200387074897960601564241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41600516099863947468752321 31200387074897960601564241)
  ·
    refine ⟨23400290306173470451173181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31200387074897960601564241 23400290306173470451173181)
    ·
      refine ⟨8775108864815051419189943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23400290306173470451173181 8775108864815051419189943)
      ·
        refine ⟨13162663297222577128784915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8775108864815051419189943 13162663297222577128784915)
        ·
          refine ⟨19743994945833865693177373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13162663297222577128784915 19743994945833865693177373)
          ·
            refine ⟨7403998104687699634941515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19743994945833865693177373 7403998104687699634941515)
            ·
              refine ⟨11105997157031549452412273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7403998104687699634941515 11105997157031549452412273)
              ·
                refine ⟨8329497867773662089309205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11105997157031549452412273 8329497867773662089309205)
                ·
                  refine ⟨390445212551890410436369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8329497867773662089309205 390445212551890410436369)
                  ·
                    rfl

theorem cell21_1710876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_1710876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710876 prefixEnd_1710876 := by exact prefixLift 1710876
  have htrace : WordTrace (prefixWord ++ tailWord_1710876) baseStart_1710876 baseEnd_1710876 := by
    simpa [prefixWord, tailWord_1710876, baseEnd_1710876] using wordTrace_append hprefix tailTrace_1710876
  have hstable : (prefixWord ++ tailWord_1710876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710876).length < 2 ^ (prefixWord ++ tailWord_1710876).sum := by decide
  have hdescent : baseEnd_1710876 < baseStart_1710876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710879 : List Nat := [1, 1, 2, 4, 2, 2, 3, 3, 3]
def baseStart_1710879 : Nat := 118140960795 + 1710879 * 2 ^ 59
def prefixEnd_1710879 : Nat := 4983230072969 + 3 ^ 40 * 1710879 * 2
def baseEnd_1710879 : Nat := 390445897192763071886363

theorem tailTrace_1710879 : CollatzResearch.WordTrace tailWord_1710879 prefixEnd_1710879 390445897192763071886363 := by
  unfold tailWord_1710879
  simp only [CollatzResearch.WordTrace]
  refine ⟨62400883568785052715487691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41600589045856701810325127 62400883568785052715487691)
  ·
    refine ⟨93601325353177579073231537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62400883568785052715487691 93601325353177579073231537)
    ·
      refine ⟨70200994014883184304923653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93601325353177579073231537 70200994014883184304923653)
      ·
        refine ⟨13162686377790597057173185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70200994014883184304923653 13162686377790597057173185)
        ·
          refine ⟨9872014783342947792879889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13162686377790597057173185 9872014783342947792879889)
          ·
            refine ⟨7404011087507210844659917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9872014783342947792879889 7404011087507210844659917)
            ·
              refine ⟨2776504157815204066747469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7404011087507210844659917 2776504157815204066747469)
              ·
                refine ⟨1041189059180701525030301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2776504157815204066747469 1041189059180701525030301)
                ·
                  refine ⟨390445897192763071886363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041189059180701525030301 390445897192763071886363)
                  ·
                    rfl

theorem cell21_1710879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 3].length) (baseStart_1710879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710879 prefixEnd_1710879 := by exact prefixLift 1710879
  have htrace : WordTrace (prefixWord ++ tailWord_1710879) baseStart_1710879 baseEnd_1710879 := by
    simpa [prefixWord, tailWord_1710879, baseEnd_1710879] using wordTrace_append hprefix tailTrace_1710879
  have hstable : (prefixWord ++ tailWord_1710879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710879).length < 2 ^ (prefixWord ++ tailWord_1710879).sum := by decide
  have hdescent : baseEnd_1710879 < baseStart_1710879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710910 : List Nat := [4, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_1710910 : Nat := 118140960795 + 1710910 * 2 ^ 59
def prefixEnd_1710910 : Nat := 4983230072969 + 3 ^ 40 * 1710910 * 2
def baseEnd_1710910 : Nat := 390452971815113906869633

theorem tailTrace_1710910 : CollatzResearch.WordTrace tailWord_1710910 prefixEnd_1710910 390452971815113906869633 := by
  unfold tailWord_1710910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7800251778959093126233273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41601342821115163339910789 7800251778959093126233273)
  ·
    refine ⟨5850188834219319844674955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7800251778959093126233273 5850188834219319844674955)
    ·
      refine ⟨8775283251328979767012433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5850188834219319844674955 8775283251328979767012433)
      ·
        refine ⟨6581462438496734825259325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8775283251328979767012433 6581462438496734825259325)
        ·
          refine ⟨2468048414436275559472247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6581462438496734825259325 2468048414436275559472247)
          ·
            refine ⟨3702072621654413339208371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2468048414436275559472247 3702072621654413339208371)
            ·
              refine ⟨5553108932481620008812557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3702072621654413339208371 5553108932481620008812557)
              ·
                refine ⟨2082415849680607503304709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5553108932481620008812557 2082415849680607503304709)
                ·
                  refine ⟨390452971815113906869633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2082415849680607503304709 390452971815113906869633)
                  ·
                    rfl

theorem cell21_1710910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_1710910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710910 prefixEnd_1710910 := by exact prefixLift 1710910
  have htrace : WordTrace (prefixWord ++ tailWord_1710910) baseStart_1710910 baseEnd_1710910 := by
    simpa [prefixWord, tailWord_1710910, baseEnd_1710910] using wordTrace_append hprefix tailTrace_1710910
  have hstable : (prefixWord ++ tailWord_1710910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710910).length < 2 ^ (prefixWord ++ tailWord_1710910).sum := by decide
  have hdescent : baseEnd_1710910 < baseStart_1710910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710955 : List Nat := [1, 1, 1, 1, 2, 2, 8, 2, 3]
def baseStart_1710955 : Nat := 118140960795 + 1710955 * 2 ^ 59
def prefixEnd_1710955 : Nat := 4983230072969 + 3 ^ 40 * 1710955 * 2
def baseEnd_1710955 : Nat := 390463241428203828619541

theorem tailTrace_1710955 : CollatzResearch.WordTrace tailWord_1710955 prefixEnd_1710955 390463241428203828619541 := by
  unfold tailWord_1710955
  simp only [CollatzResearch.WordTrace]
  refine ⟨62403655516509717695254319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41602437011006478463502879 62403655516509717695254319)
  ·
    refine ⟨93605483274764576542881479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62403655516509717695254319 93605483274764576542881479)
    ·
      refine ⟨140408224912146864814322219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93605483274764576542881479 140408224912146864814322219)
      ·
        refine ⟨210612337368220297221483329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140408224912146864814322219 210612337368220297221483329)
        ·
          refine ⟨157959253026165222916112497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210612337368220297221483329 157959253026165222916112497)
          ·
            refine ⟨118469439769623917187084373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157959253026165222916112497 118469439769623917187084373)
            ·
              refine ⟨1388313747300280279536145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 118469439769623917187084373 1388313747300280279536145)
              ·
                refine ⟨1041235310475210209652109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1388313747300280279536145 1041235310475210209652109)
                ·
                  refine ⟨390463241428203828619541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041235310475210209652109 390463241428203828619541)
                  ·
                    rfl

theorem cell21_1710955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 3].length) (baseStart_1710955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1710955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1710955 prefixEnd_1710955 := by exact prefixLift 1710955
  have htrace : WordTrace (prefixWord ++ tailWord_1710955) baseStart_1710955 baseEnd_1710955 := by
    simpa [prefixWord, tailWord_1710955, baseEnd_1710955] using wordTrace_append hprefix tailTrace_1710955
  have hstable : (prefixWord ++ tailWord_1710955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710955).length < 2 ^ (prefixWord ++ tailWord_1710955).sum := by decide
  have hdescent : baseEnd_1710955 < baseStart_1710955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711048 : List Nat := [2, 1, 3, 1, 5, 2, 1, 3, 3]
def baseStart_1711048 : Nat := 118140960795 + 1711048 * 2 ^ 59
def prefixEnd_1711048 : Nat := 4983230072969 + 3 ^ 40 * 1711048 * 2
def baseEnd_1711048 : Nat := 390484465295256333569351

theorem tailTrace_1711048 : CollatzResearch.WordTrace tailWord_1711048 prefixEnd_1711048 390484465295256333569351 := by
  unfold tailWord_1711048
  simp only [CollatzResearch.WordTrace]
  refine ⟨31203523752586397289194899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41604698336781863052259865 31203523752586397289194899)
  ·
    refine ⟨46805285628879595933792349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31203523752586397289194899 46805285628879595933792349)
    ·
      refine ⟨17551982110829848475172131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46805285628879595933792349 17551982110829848475172131)
      ·
        refine ⟨26327973166244772712758197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17551982110829848475172131 26327973166244772712758197)
        ·
          refine ⟨2468247484335447441821081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26327973166244772712758197 2468247484335447441821081)
          ·
            refine ⟨1851185613251585581365811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2468247484335447441821081 1851185613251585581365811)
            ·
              refine ⟨2776778419877378372048717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851185613251585581365811 2776778419877378372048717)
              ·
                refine ⟨1041291907454016889518269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2776778419877378372048717 1041291907454016889518269)
                ·
                  refine ⟨390484465295256333569351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041291907454016889518269 390484465295256333569351)
                  ·
                    rfl

theorem cell21_1711048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 3].length) (baseStart_1711048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1711048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1711048 prefixEnd_1711048 := by exact prefixLift 1711048
  have htrace : WordTrace (prefixWord ++ tailWord_1711048) baseStart_1711048 baseEnd_1711048 := by
    simpa [prefixWord, tailWord_1711048, baseEnd_1711048] using wordTrace_append hprefix tailTrace_1711048
  have hstable : (prefixWord ++ tailWord_1711048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711048).length < 2 ^ (prefixWord ++ tailWord_1711048).sum := by decide
  have hdescent : baseEnd_1711048 < baseStart_1711048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711118 : List Nat := [4, 1, 1, 2, 2, 11]
def baseStart_1711118 : Nat := 118140960795 + 1711118 * 2 ^ 59
def prefixEnd_1711118 : Nat := 4983230072969 + 3 ^ 40 * 1711118 * 2
def baseEnd_1711118 : Nat := 14462979268479695088983

theorem tailTrace_1711118 : CollatzResearch.WordTrace tailWord_1711118 prefixEnd_1711118 14462979268479695088983 := by
  unfold tailWord_1711118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7801200076864899566679751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41606400409946131022292005 7801200076864899566679751)
  ·
    refine ⟨11701800115297349350019627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7801200076864899566679751 11701800115297349350019627)
    ·
      refine ⟨17552700172946024025029441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11701800115297349350019627 17552700172946024025029441)
      ·
        refine ⟨13164525129709518018772081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17552700172946024025029441 13164525129709518018772081)
        ·
          refine ⟨9873393847282138514079061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13164525129709518018772081 9873393847282138514079061)
          ·
            refine ⟨14462979268479695088983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9873393847282138514079061 14462979268479695088983)
            ·
              rfl

theorem cell21_1711118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 11].length) (baseStart_1711118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1711118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1711118 prefixEnd_1711118 := by exact prefixLift 1711118
  have htrace : WordTrace (prefixWord ++ tailWord_1711118) baseStart_1711118 baseEnd_1711118 := by
    simpa [prefixWord, tailWord_1711118, baseEnd_1711118] using wordTrace_append hprefix tailTrace_1711118
  have hstable : (prefixWord ++ tailWord_1711118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711118).length < 2 ^ (prefixWord ++ tailWord_1711118).sum := by decide
  have hdescent : baseEnd_1711118 < baseStart_1711118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711135 : List Nat := [1, 1, 2, 4, 1, 5, 1, 6]
def baseStart_1711135 : Nat := 118140960795 + 1711135 * 2 ^ 59
def prefixEnd_1711135 : Nat := 4983230072969 + 3 ^ 40 * 1711135 * 2
def baseEnd_1711135 : Nat := 130168106626854505206391

theorem tailTrace_1711135 : CollatzResearch.WordTrace tailWord_1711135 prefixEnd_1711135 130168106626854505206391 := by
  unfold tailWord_1711135
  simp only [CollatzResearch.WordTrace]
  refine ⟨62410220655857608436806859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41606813770571738957871239 62410220655857608436806859)
  ·
    refine ⟨93615330983786412655210289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62410220655857608436806859 93615330983786412655210289)
    ·
      refine ⟨70211498237839809491407717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93615330983786412655210289 70211498237839809491407717)
      ·
        refine ⟨13164655919594964279638947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70211498237839809491407717 13164655919594964279638947)
        ·
          refine ⟨19746983879392446419458421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13164655919594964279638947 19746983879392446419458421)
          ·
            refine ⟨1851279738693041851824227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19746983879392446419458421 1851279738693041851824227)
            ·
              refine ⟨2776919608039562777736341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851279738693041851824227 2776919608039562777736341)
              ·
                refine ⟨130168106626854505206391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2776919608039562777736341 130168106626854505206391)
                ·
                  rfl

theorem cell21_1711135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 6].length) (baseStart_1711135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1711135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1711135 prefixEnd_1711135 := by exact prefixLift 1711135
  have htrace : WordTrace (prefixWord ++ tailWord_1711135) baseStart_1711135 baseEnd_1711135 := by
    simpa [prefixWord, tailWord_1711135, baseEnd_1711135] using wordTrace_append hprefix tailTrace_1711135
  have hstable : (prefixWord ++ tailWord_1711135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711135).length < 2 ^ (prefixWord ++ tailWord_1711135).sum := by decide
  have hdescent : baseEnd_1711135 < baseStart_1711135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711411 : List Nat := [1, 1, 1, 2, 5, 3, 3, 2, 3]
def baseStart_1711411 : Nat := 118140960795 + 1711411 * 2 ^ 59
def prefixEnd_1711411 : Nat := 4983230072969 + 3 ^ 40 * 1711411 * 2
def baseEnd_1711411 : Nat := 390567306840848369018609

theorem tailTrace_1711411 : CollatzResearch.WordTrace tailWord_1711411 prefixEnd_1711411 390567306840848369018609 := by
  unfold tailWord_1711411
  simp only [CollatzResearch.WordTrace]
  refine ⟨62420287202857707573854087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41613524801905138382569391 62420287202857707573854087)
  ·
    refine ⟨93630430804286561360781131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62420287202857707573854087 93630430804286561360781131)
    ·
      refine ⟨140445646206429842041171697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93630430804286561360781131 140445646206429842041171697)
      ·
        refine ⟨105334234654822381530878773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140445646206429842041171697 105334234654822381530878773)
        ·
          refine ⟨9875084498889598268519885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105334234654822381530878773 9875084498889598268519885)
          ·
            refine ⟨3703156687083599350694957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9875084498889598268519885 3703156687083599350694957)
            ·
              refine ⟨1388683757656349756510609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3703156687083599350694957 1388683757656349756510609)
              ·
                refine ⟨1041512818242262317382957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1388683757656349756510609 1041512818242262317382957)
                ·
                  refine ⟨390567306840848369018609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041512818242262317382957 390567306840848369018609)
                  ·
                    rfl

theorem cell21_1711411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 3].length) (baseStart_1711411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1711411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1711411 prefixEnd_1711411 := by exact prefixLift 1711411
  have htrace : WordTrace (prefixWord ++ tailWord_1711411) baseStart_1711411 baseEnd_1711411 := by
    simpa [prefixWord, tailWord_1711411, baseEnd_1711411] using wordTrace_append hprefix tailTrace_1711411
  have hstable : (prefixWord ++ tailWord_1711411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711411).length < 2 ^ (prefixWord ++ tailWord_1711411).sum := by decide
  have hdescent : baseEnd_1711411 < baseStart_1711411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711425 : List Nat := [1, 2, 5, 2, 1, 2, 1, 3, 4]
def baseStart_1711425 : Nat := 118140960795 + 1711425 * 2 ^ 59
def prefixEnd_1711425 : Nat := 4983230072969 + 3 ^ 40 * 1711425 * 2
def baseEnd_1711425 : Nat := 390570501831587455785247

theorem tailTrace_1711425 : CollatzResearch.WordTrace tailWord_1711425 prefixEnd_1711425 390570501831587455785247 := by
  unfold tailWord_1711425
  simp only [CollatzResearch.WordTrace]
  refine ⟨62420797824806987964863729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41613865216537991976575819 62420797824806987964863729)
  ·
    refine ⟨46815598368605240973647797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62420797824806987964863729 46815598368605240973647797)
    ·
      refine ⟨4388962347056741341279481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46815598368605240973647797 4388962347056741341279481)
      ·
        refine ⟨3291721760292556005959611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4388962347056741341279481 3291721760292556005959611)
        ·
          refine ⟨4937582640438834008939417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3291721760292556005959611 4937582640438834008939417)
          ·
            refine ⟨3703186980329125506704563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4937582640438834008939417 3703186980329125506704563)
            ·
              refine ⟨5554780470493688260056845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3703186980329125506704563 5554780470493688260056845)
              ·
                refine ⟨2083042676435133097521317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5554780470493688260056845 2083042676435133097521317)
                ·
                  refine ⟨390570501831587455785247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2083042676435133097521317 390570501831587455785247)
                  ·
                    rfl

theorem cell21_1711425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_1711425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1711425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1711425 prefixEnd_1711425 := by exact prefixLift 1711425
  have htrace : WordTrace (prefixWord ++ tailWord_1711425) baseStart_1711425 baseEnd_1711425 := by
    simpa [prefixWord, tailWord_1711425, baseEnd_1711425] using wordTrace_append hprefix tailTrace_1711425
  have hstable : (prefixWord ++ tailWord_1711425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711425).length < 2 ^ (prefixWord ++ tailWord_1711425).sum := by decide
  have hdescent : baseEnd_1711425 < baseStart_1711425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711594 : List Nat := [3, 1, 3, 1, 4, 2, 2, 1, 4]
def baseStart_1711594 : Nat := 118140960795 + 1711594 * 2 ^ 59
def prefixEnd_1711594 : Nat := 4983230072969 + 3 ^ 40 * 1711594 * 2
def baseEnd_1711594 : Nat := 390609069934080717468235

theorem tailTrace_1711594 : CollatzResearch.WordTrace tailWord_1711594 prefixEnd_1711594 390609069934080717468235 := by
  unfold tailWord_1711594
  simp only [CollatzResearch.WordTrace]
  refine ⟨15606740440298682456941459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41617974507463153218510557 15606740440298682456941459)
  ·
    refine ⟨23410110660448023685412189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15606740440298682456941459 23410110660448023685412189)
    ·
      refine ⟨8778791497668008882029571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23410110660448023685412189 8778791497668008882029571)
      ·
        refine ⟨13168187246502013323044357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8778791497668008882029571 13168187246502013323044357)
        ·
          refine ⟨2469035108719127498070817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13168187246502013323044357 2469035108719127498070817)
          ·
            refine ⟨1851776331539345623553113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2469035108719127498070817 1851776331539345623553113)
            ·
              refine ⟨1388832248654509217664835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1851776331539345623553113 1388832248654509217664835)
              ·
                refine ⟨2083248372981763826497253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388832248654509217664835 2083248372981763826497253)
                ·
                  refine ⟨390609069934080717468235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2083248372981763826497253 390609069934080717468235)
                  ·
                    rfl

theorem cell21_1711594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_1711594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1711594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1711594 prefixEnd_1711594 := by exact prefixLift 1711594
  have htrace : WordTrace (prefixWord ++ tailWord_1711594) baseStart_1711594 baseEnd_1711594 := by
    simpa [prefixWord, tailWord_1711594, baseEnd_1711594] using wordTrace_append hprefix tailTrace_1711594
  have hstable : (prefixWord ++ tailWord_1711594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711594).length < 2 ^ (prefixWord ++ tailWord_1711594).sum := by decide
  have hdescent : baseEnd_1711594 < baseStart_1711594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711650 : List Nat := [3, 3, 1, 1, 1, 1, 5, 6]
def baseStart_1711650 : Nat := 118140960795 + 1711650 * 2 ^ 59
def prefixEnd_1711650 : Nat := 4983230072969 + 3 ^ 40 * 1711650 * 2
def baseEnd_1711650 : Nat := 130207283299012354844929

theorem tailTrace_1711650 : CollatzResearch.WordTrace tailWord_1711650 prefixEnd_1711650 130207283299012354844929 := by
  unfold tailWord_1711650
  simp only [CollatzResearch.WordTrace]
  refine ⟨15607251062247962847951101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41619336165994567594536269 15607251062247962847951101)
  ·
    refine ⟨5852719148342986067981663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15607251062247962847951101 5852719148342986067981663)
    ·
      refine ⟨8779078722514479101972495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5852719148342986067981663 8779078722514479101972495)
      ·
        refine ⟨13168618083771718652958743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8779078722514479101972495 13168618083771718652958743)
        ·
          refine ⟨19752927125657577979438115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13168618083771718652958743 19752927125657577979438115)
          ·
            refine ⟨29629390688486366969157173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19752927125657577979438115 29629390688486366969157173)
            ·
              refine ⟨2777755377045596903358485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29629390688486366969157173 2777755377045596903358485)
              ·
                refine ⟨130207283299012354844929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2777755377045596903358485 130207283299012354844929)
                ·
                  rfl

theorem cell21_1711650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_1711650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1711650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1711650 prefixEnd_1711650 := by exact prefixLift 1711650
  have htrace : WordTrace (prefixWord ++ tailWord_1711650) baseStart_1711650 baseEnd_1711650 := by
    simpa [prefixWord, tailWord_1711650, baseEnd_1711650] using wordTrace_append hprefix tailTrace_1711650
  have hstable : (prefixWord ++ tailWord_1711650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711650).length < 2 ^ (prefixWord ++ tailWord_1711650).sum := by decide
  have hdescent : baseEnd_1711650 < baseStart_1711650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711698 : List Nat := [3, 2, 2, 1, 2, 2, 2, 4, 3]
def baseStart_1711698 : Nat := 118140960795 + 1711698 * 2 ^ 59
def prefixEnd_1711698 : Nat := 4983230072969 + 3 ^ 40 * 1711698 * 2
def baseEnd_1711698 : Nat := 390632804150999647734689

theorem tailTrace_1711698 : CollatzResearch.WordTrace tailWord_1711698 prefixEnd_1711698 390632804150999647734689 := by
  unfold tailWord_1711698
  simp only [CollatzResearch.WordTrace]
  refine ⟨15607688738204488897387937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41620503301878637059701165 15607688738204488897387937)
  ·
    refine ⟨11705766553653366673040953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15607688738204488897387937 11705766553653366673040953)
    ·
      refine ⟨8779324915240025004780715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11705766553653366673040953 8779324915240025004780715)
      ·
        refine ⟨13168987372860037507171073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8779324915240025004780715 13168987372860037507171073)
        ·
          refine ⟨9876740529645028130378305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13168987372860037507171073 9876740529645028130378305)
          ·
            refine ⟨7407555397233771097783729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9876740529645028130378305 7407555397233771097783729)
            ·
              refine ⟨5555666547925328323337797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7407555397233771097783729 5555666547925328323337797)
              ·
                refine ⟨1041687477735999060625837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5555666547925328323337797 1041687477735999060625837)
                ·
                  refine ⟨390632804150999647734689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041687477735999060625837 390632804150999647734689)
                  ·
                    rfl

theorem cell21_1711698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_1711698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1711698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1711698 prefixEnd_1711698 := by exact prefixLift 1711698
  have htrace : WordTrace (prefixWord ++ tailWord_1711698) baseStart_1711698 baseEnd_1711698 := by
    simpa [prefixWord, tailWord_1711698, baseEnd_1711698] using wordTrace_append hprefix tailTrace_1711698
  have hstable : (prefixWord ++ tailWord_1711698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711698).length < 2 ^ (prefixWord ++ tailWord_1711698).sum := by decide
  have hdescent : baseEnd_1711698 < baseStart_1711698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711816 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 5]
def baseStart_1711816 : Nat := 118140960795 + 1711816 * 2 ^ 59
def prefixEnd_1711816 : Nat := 4983230072969 + 3 ^ 40 * 1711816 * 2
def baseEnd_1711816 : Nat := 390659733358657664767781

theorem tailTrace_1711816 : CollatzResearch.WordTrace tailWord_1711816 prefixEnd_1711816 390659733358657664767781 := by
  unfold tailWord_1711816
  simp only [CollatzResearch.WordTrace]
  refine ⟨31217529383195230871173651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41623372510926974494898201 31217529383195230871173651)
  ·
    refine ⟨46826294074792846306760477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31217529383195230871173651 46826294074792846306760477)
    ·
      refine ⟨17559860278047317365035179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46826294074792846306760477 17559860278047317365035179)
      ·
        refine ⟨26339790417070976047552769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17559860278047317365035179 26339790417070976047552769)
        ·
          refine ⟨19754842812803232035664577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26339790417070976047552769 19754842812803232035664577)
          ·
            refine ⟨14816132109602424026748433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19754842812803232035664577 14816132109602424026748433)
            ·
              refine ⟨11112099082201818020061325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14816132109602424026748433 11112099082201818020061325)
              ·
                refine ⟨4167037155825681757522997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11112099082201818020061325 4167037155825681757522997)
                ·
                  refine ⟨390659733358657664767781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4167037155825681757522997 390659733358657664767781)
                  ·
                    rfl

theorem cell21_1711816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_1711816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1711816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1711816 prefixEnd_1711816 := by exact prefixLift 1711816
  have htrace : WordTrace (prefixWord ++ tailWord_1711816) baseStart_1711816 baseEnd_1711816 := by
    simpa [prefixWord, tailWord_1711816, baseEnd_1711816] using wordTrace_append hprefix tailTrace_1711816
  have hstable : (prefixWord ++ tailWord_1711816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711816).length < 2 ^ (prefixWord ++ tailWord_1711816).sum := by decide
  have hdescent : baseEnd_1711816 < baseStart_1711816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711836 : List Nat := [2, 2, 5, 1, 2, 1, 3, 5]
def baseStart_1711836 : Nat := 118140960795 + 1711836 * 2 ^ 59
def prefixEnd_1711836 : Nat := 4983230072969 + 3 ^ 40 * 1711836 * 2
def baseEnd_1711836 : Nat := 130221432543714024811469

theorem tailTrace_1711836 : CollatzResearch.WordTrace tailWord_1711836 prefixEnd_1711836 130221432543714024811469 := by
  unfold tailWord_1711836
  simp only [CollatzResearch.WordTrace]
  refine ⟨31217894113159002579037681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41623858817545336772050241 31217894113159002579037681)
  ·
    refine ⟨23413420584869251934278261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31217894113159002579037681 23413420584869251934278261)
    ·
      refine ⟨2195008179831492368838587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23413420584869251934278261 2195008179831492368838587)
      ·
        refine ⟨3292512269747238553257881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2195008179831492368838587 3292512269747238553257881)
        ·
          refine ⟨2469384202310428914943411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3292512269747238553257881 2469384202310428914943411)
          ·
            refine ⟨3704076303465643372415117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2469384202310428914943411 3704076303465643372415117)
            ·
              refine ⟨1389028613799616264655669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3704076303465643372415117 1389028613799616264655669)
              ·
                refine ⟨130221432543714024811469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1389028613799616264655669 130221432543714024811469)
                ·
                  rfl

theorem cell21_1711836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 5].length) (baseStart_1711836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1711836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1711836 prefixEnd_1711836 := by exact prefixLift 1711836
  have htrace : WordTrace (prefixWord ++ tailWord_1711836) baseStart_1711836 baseEnd_1711836 := by
    simpa [prefixWord, tailWord_1711836, baseEnd_1711836] using wordTrace_append hprefix tailTrace_1711836
  have hstable : (prefixWord ++ tailWord_1711836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711836).length < 2 ^ (prefixWord ++ tailWord_1711836).sum := by decide
  have hdescent : baseEnd_1711836 < baseStart_1711836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711895 : List Nat := [1, 1, 3, 4, 2, 3, 2, 5]
def baseStart_1711895 : Nat := 118140960795 + 1711895 * 2 ^ 59
def prefixEnd_1711895 : Nat := 4983230072969 + 3 ^ 40 * 1711895 * 2
def baseEnd_1711895 : Nat := 130225920744990360983651

theorem tailTrace_1711895 : CollatzResearch.WordTrace tailWord_1711895 prefixEnd_1711895 130225920744990360983651 := by
  unfold tailWord_1711895
  simp only [CollatzResearch.WordTrace]
  refine ⟨62437940133104258234473139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41625293422069505489648759 62437940133104258234473139)
  ·
    refine ⟨93656910199656387351709709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62437940133104258234473139 93656910199656387351709709)
    ·
      refine ⟨35121341324871145256891141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93656910199656387351709709 35121341324871145256891141)
      ·
        refine ⟨6585251498413339735667089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35121341324871145256891141 6585251498413339735667089)
        ·
          refine ⟨4938938623810004801750317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6585251498413339735667089 4938938623810004801750317)
          ·
            refine ⟨1852101983928751800656369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4938938623810004801750317 1852101983928751800656369)
            ·
              refine ⟨1389076487946563850492277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1852101983928751800656369 1389076487946563850492277)
              ·
                refine ⟨130225920744990360983651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1389076487946563850492277 130225920744990360983651)
                ·
                  rfl

theorem cell21_1711895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 5].length) (baseStart_1711895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1711895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1711895 prefixEnd_1711895 := by exact prefixLift 1711895
  have htrace : WordTrace (prefixWord ++ tailWord_1711895) baseStart_1711895 baseEnd_1711895 := by
    simpa [prefixWord, tailWord_1711895, baseEnd_1711895] using wordTrace_append hprefix tailTrace_1711895
  have hstable : (prefixWord ++ tailWord_1711895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711895).length < 2 ^ (prefixWord ++ tailWord_1711895).sum := by decide
  have hdescent : baseEnd_1711895 < baseStart_1711895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711926 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_1711926 : Nat := 118140960795 + 1711926 * 2 ^ 59
def prefixEnd_1711926 : Nat := 4983230072969 + 3 ^ 40 * 1711926 * 2
def baseEnd_1711926 : Nat := 390684836857321917934223

theorem tailTrace_1711926 : CollatzResearch.WordTrace tailWord_1711926 prefixEnd_1711926 390684836857321917934223 := by
  unfold tailWord_1711926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3902441924749496908053227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41626047197327967019234421 3902441924749496908053227)
  ·
    refine ⟨5853662887124245362079841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3902441924749496908053227 5853662887124245362079841)
    ·
      refine ⟨4390247165343184021559881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5853662887124245362079841 4390247165343184021559881)
      ·
        refine ⟨3292685374007388016169911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4390247165343184021559881 3292685374007388016169911)
        ·
          refine ⟨4939028061011082024254867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3292685374007388016169911 4939028061011082024254867)
          ·
            refine ⟨7408542091516623036382301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4939028061011082024254867 7408542091516623036382301)
            ·
              refine ⟨2778203284318733638643363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7408542091516623036382301 2778203284318733638643363)
              ·
                refine ⟨4167304926478100457965045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778203284318733638643363 4167304926478100457965045)
                ·
                  refine ⟨390684836857321917934223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4167304926478100457965045 390684836857321917934223)
                  ·
                    rfl

theorem cell21_1711926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_1711926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1711926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1711926 prefixEnd_1711926 := by exact prefixLift 1711926
  have htrace : WordTrace (prefixWord ++ tailWord_1711926) baseStart_1711926 baseEnd_1711926 := by
    simpa [prefixWord, tailWord_1711926, baseEnd_1711926] using wordTrace_append hprefix tailTrace_1711926
  have hstable : (prefixWord ++ tailWord_1711926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711926).length < 2 ^ (prefixWord ++ tailWord_1711926).sum := by decide
  have hdescent : baseEnd_1711926 < baseStart_1711926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711985 : List Nat := [1, 2, 2, 2, 1, 3, 3, 4, 3]
def baseStart_1711985 : Nat := 118140960795 + 1711985 * 2 ^ 59
def prefixEnd_1711985 : Nat := 4983230072969 + 3 ^ 40 * 1711985 * 2
def baseEnd_1711985 : Nat := 390698301461150926450769

theorem tailTrace_1711985 : CollatzResearch.WordTrace tailWord_1711985 prefixEnd_1711985 390698301461150926450769 := by
  unfold tailWord_1711985
  simp only [CollatzResearch.WordTrace]
  refine ⟨62441222702778203605249409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41627481801852135736832939 62441222702778203605249409)
  ·
    refine ⟨46830917027083652703937057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62441222702778203605249409 46830917027083652703937057)
    ·
      refine ⟨35123187770312739527952793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46830917027083652703937057 35123187770312739527952793)
      ·
        refine ⟨26342390827734554645964595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35123187770312739527952793 26342390827734554645964595)
        ·
          refine ⟨39513586241601831968946893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26342390827734554645964595 39513586241601831968946893)
          ·
            refine ⟨14817594840600686988355085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39513586241601831968946893 14817594840600686988355085)
            ·
              refine ⟨5556598065225257620633157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14817594840600686988355085 5556598065225257620633157)
              ·
                refine ⟨1041862137229735803868717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5556598065225257620633157 1041862137229735803868717)
                ·
                  refine ⟨390698301461150926450769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041862137229735803868717 390698301461150926450769)
                  ·
                    rfl

theorem cell21_1711985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 3].length) (baseStart_1711985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1711985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1711985 prefixEnd_1711985 := by exact prefixLift 1711985
  have htrace : WordTrace (prefixWord ++ tailWord_1711985) baseStart_1711985 baseEnd_1711985 := by
    simpa [prefixWord, tailWord_1711985, baseEnd_1711985] using wordTrace_append hprefix tailTrace_1711985
  have hstable : (prefixWord ++ tailWord_1711985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711985).length < 2 ^ (prefixWord ++ tailWord_1711985).sum := by decide
  have hdescent : baseEnd_1711985 < baseStart_1711985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712033 : List Nat := [1, 2, 3, 4, 2, 2, 1, 2, 4]
def baseStart_1712033 : Nat := 118140960795 + 1712033 * 2 ^ 59
def prefixEnd_1712033 : Nat := 4983230072969 + 3 ^ 40 * 1712033 * 2
def baseEnd_1712033 : Nat := 390709255715113509650671

theorem tailTrace_1712033 : CollatzResearch.WordTrace tailWord_1712033 prefixEnd_1712033 390709255715113509650671 := by
  unfold tailWord_1712033
  simp only [CollatzResearch.WordTrace]
  refine ⟨62442973406604307802996753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41628648937736205201997835 62442973406604307802996753)
  ·
    refine ⟨46832230054953230852247565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62442973406604307802996753 46832230054953230852247565)
    ·
      refine ⟨17562086270607461569592837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46832230054953230852247565 17562086270607461569592837)
      ·
        refine ⟨3292891175738899044298657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17562086270607461569592837 3292891175738899044298657)
        ·
          refine ⟨2469668381804174283223993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3292891175738899044298657 2469668381804174283223993)
          ·
            refine ⟨1852251286353130712417995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2469668381804174283223993 1852251286353130712417995)
            ·
              refine ⟨2778376929529696068626993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852251286353130712417995 2778376929529696068626993)
              ·
                refine ⟨2083782697147272051470245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2778376929529696068626993 2083782697147272051470245)
                ·
                  refine ⟨390709255715113509650671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2083782697147272051470245 390709255715113509650671)
                  ·
                    rfl

theorem cell21_1712033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_1712033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712033 prefixEnd_1712033 := by exact prefixLift 1712033
  have htrace : WordTrace (prefixWord ++ tailWord_1712033) baseStart_1712033 baseEnd_1712033 := by
    simpa [prefixWord, tailWord_1712033, baseEnd_1712033] using wordTrace_append hprefix tailTrace_1712033
  have hstable : (prefixWord ++ tailWord_1712033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712033).length < 2 ^ (prefixWord ++ tailWord_1712033).sum := by decide
  have hdescent : baseEnd_1712033 < baseStart_1712033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712109 : List Nat := [1, 5, 1, 4, 1, 1, 1, 3, 4]
def baseStart_1712109 : Nat := 118140960795 + 1712109 * 2 ^ 59
def prefixEnd_1712109 : Nat := 4983230072969 + 3 ^ 40 * 1712109 * 2
def baseEnd_1712109 : Nat := 390726599950554266383849

theorem tailTrace_1712109 : CollatzResearch.WordTrace tailWord_1712109 prefixEnd_1712109 390726599950554266383849 := by
  unfold tailWord_1712109
  simp only [CollatzResearch.WordTrace]
  refine ⟨62445745354328972782763381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41630496902885981855175587 62445745354328972782763381)
  ·
    refine ⟨5854288626968341198384067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62445745354328972782763381 5854288626968341198384067)
    ·
      refine ⟨8781432940452511797576101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5854288626968341198384067 8781432940452511797576101)
      ·
        refine ⟨1646518676334845962045519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8781432940452511797576101 1646518676334845962045519)
        ·
          refine ⟨2469778014502268943068279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1646518676334845962045519 2469778014502268943068279)
          ·
            refine ⟨3704667021753403414602419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2469778014502268943068279 3704667021753403414602419)
            ·
              refine ⟨5557000532630105121903629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3704667021753403414602419 5557000532630105121903629)
              ·
                refine ⟨2083875199736289420713861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5557000532630105121903629 2083875199736289420713861)
                ·
                  refine ⟨390726599950554266383849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2083875199736289420713861 390726599950554266383849)
                  ·
                    rfl

theorem cell21_1712109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_1712109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712109 prefixEnd_1712109 := by exact prefixLift 1712109
  have htrace : WordTrace (prefixWord ++ tailWord_1712109) baseStart_1712109 baseEnd_1712109 := by
    simpa [prefixWord, tailWord_1712109, baseEnd_1712109] using wordTrace_append hprefix tailTrace_1712109
  have hstable : (prefixWord ++ tailWord_1712109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712109).length < 2 ^ (prefixWord ++ tailWord_1712109).sum := by decide
  have hdescent : baseEnd_1712109 < baseStart_1712109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712154 : List Nat := [3, 1, 1, 3, 1, 3, 4, 2, 3]
def baseStart_1712154 : Nat := 118140960795 + 1712154 * 2 ^ 59
def prefixEnd_1712154 : Nat := 4983230072969 + 3 ^ 40 * 1712154 * 2
def baseEnd_1712154 : Nat := 390736869563644188133757

theorem tailTrace_1712154 : CollatzResearch.WordTrace tailWord_1712154 prefixEnd_1712154 390736869563644188133757 := by
  unfold tailWord_1712154
  simp only [CollatzResearch.WordTrace]
  refine ⟨15611846659791486367037879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41631591092777296978767677 15611846659791486367037879)
  ·
    refine ⟨23417769989687229550556819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15611846659791486367037879 23417769989687229550556819)
    ·
      refine ⟨35126654984530844325835229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23417769989687229550556819 35126654984530844325835229)
      ·
        refine ⟨13172495619199066622188211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35126654984530844325835229 13172495619199066622188211)
        ·
          refine ⟨19758743428798599933282317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13172495619199066622188211 19758743428798599933282317)
          ·
            refine ⟨7409528785799474974980869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19758743428798599933282317 7409528785799474974980869)
            ·
              refine ⟨1389286647337401557808913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7409528785799474974980869 1389286647337401557808913)
              ·
                refine ⟨1041964985503051168356685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1389286647337401557808913 1041964985503051168356685)
                ·
                  refine ⟨390736869563644188133757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041964985503051168356685 390736869563644188133757)
                  ·
                    rfl

theorem cell21_1712154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_1712154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712154 prefixEnd_1712154 := by exact prefixLift 1712154
  have htrace : WordTrace (prefixWord ++ tailWord_1712154) baseStart_1712154 baseEnd_1712154 := by
    simpa [prefixWord, tailWord_1712154, baseEnd_1712154] using wordTrace_append hprefix tailTrace_1712154
  have hstable : (prefixWord ++ tailWord_1712154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712154).length < 2 ^ (prefixWord ++ tailWord_1712154).sum := by decide
  have hdescent : baseEnd_1712154 < baseStart_1712154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712165 : List Nat := [1, 3, 1, 2, 2, 3, 3, 6]
def baseStart_1712165 : Nat := 118140960795 + 1712165 * 2 ^ 59
def prefixEnd_1712165 : Nat := 4983230072969 + 3 ^ 40 * 1712165 * 2
def baseEnd_1712165 : Nat := 130246459971170204483467

theorem tailTrace_1712165 : CollatzResearch.WordTrace tailWord_1712165 prefixEnd_1712165 130246459971170204483467 := by
  unfold tailWord_1712165
  simp only [CollatzResearch.WordTrace]
  refine ⟨62447787842126094346801949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41631858561417396231201299 62447787842126094346801949)
  ·
    refine ⟨23417920440797285380050731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62447787842126094346801949 23417920440797285380050731)
    ·
      refine ⟨35126880661195928070076097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23417920440797285380050731 35126880661195928070076097)
      ·
        refine ⟨26345160495896946052557073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35126880661195928070076097 26345160495896946052557073)
        ·
          refine ⟨19758870371922709539417805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26345160495896946052557073 19758870371922709539417805)
          ·
            refine ⟨7409576389471016077281677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19758870371922709539417805 7409576389471016077281677)
            ·
              refine ⟨2778591146051631028980629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7409576389471016077281677 2778591146051631028980629)
              ·
                refine ⟨130246459971170204483467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2778591146051631028980629 130246459971170204483467)
                ·
                  rfl

theorem cell21_1712165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 6].length) (baseStart_1712165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712165 prefixEnd_1712165 := by exact prefixLift 1712165
  have htrace : WordTrace (prefixWord ++ tailWord_1712165) baseStart_1712165 baseEnd_1712165 := by
    simpa [prefixWord, tailWord_1712165, baseEnd_1712165] using wordTrace_append hprefix tailTrace_1712165
  have hstable : (prefixWord ++ tailWord_1712165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712165).length < 2 ^ (prefixWord ++ tailWord_1712165).sum := by decide
  have hdescent : baseEnd_1712165 < baseStart_1712165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712179 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 7]
def baseStart_1712179 : Nat := 118140960795 + 1712179 * 2 ^ 59
def prefixEnd_1712179 : Nat := 4983230072969 + 3 ^ 40 * 1712179 * 2
def baseEnd_1712179 : Nat := 390742574904249700217039

theorem tailTrace_1712179 : CollatzResearch.WordTrace tailWord_1712179 prefixEnd_1712179 390742574904249700217039 := by
  unfold tailWord_1712179
  simp only [CollatzResearch.WordTrace]
  refine ⟨62448298464075374737811591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41632198976050249825207727 62448298464075374737811591)
  ·
    refine ⟨93672447696113062106717387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62448298464075374737811591 93672447696113062106717387)
    ·
      refine ⟨140508671544169593160076081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93672447696113062106717387 140508671544169593160076081)
      ·
        refine ⟨105381503658127194870057061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140508671544169593160076081 105381503658127194870057061)
        ·
          refine ⟨19759031935898849038135699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105381503658127194870057061 19759031935898849038135699)
          ·
            refine ⟨29638547903848273557203549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19759031935898849038135699 29638547903848273557203549)
            ·
              refine ⟨11114455463943102583951331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29638547903848273557203549 11114455463943102583951331)
              ·
                refine ⟨16671683195914653875926997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11114455463943102583951331 16671683195914653875926997)
                ·
                  refine ⟨390742574904249700217039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16671683195914653875926997 390742574904249700217039)
                  ·
                    rfl

theorem cell21_1712179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 7].length) (baseStart_1712179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712179 prefixEnd_1712179 := by exact prefixLift 1712179
  have htrace : WordTrace (prefixWord ++ tailWord_1712179) baseStart_1712179 baseEnd_1712179 := by
    simpa [prefixWord, tailWord_1712179, baseEnd_1712179] using wordTrace_append hprefix tailTrace_1712179
  have hstable : (prefixWord ++ tailWord_1712179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712179).length < 2 ^ (prefixWord ++ tailWord_1712179).sum := by decide
  have hdescent : baseEnd_1712179 < baseStart_1712179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712213 : List Nat := [1, 3, 2, 2, 1, 3, 2, 4, 3]
def baseStart_1712213 : Nat := 118140960795 + 1712213 * 2 ^ 59
def prefixEnd_1712213 : Nat := 4983230072969 + 3 ^ 40 * 1712213 * 2
def baseEnd_1712213 : Nat := 390750334167473196650303

theorem tailTrace_1712213 : CollatzResearch.WordTrace tailWord_1712213 prefixEnd_1712213 390750334167473196650303 := by
  unfold tailWord_1712213
  simp only [CollatzResearch.WordTrace]
  refine ⟨62449538545952198544549293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41633025697301465696366195 62449538545952198544549293)
  ·
    refine ⟨23418576954732074454205985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62449538545952198544549293 23418576954732074454205985)
    ·
      refine ⟨17563932716049055840654489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23418576954732074454205985 17563932716049055840654489)
      ·
        refine ⟨13172949537036791880490867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17563932716049055840654489 13172949537036791880490867)
        ·
          refine ⟨19759424305555187820736301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13172949537036791880490867 19759424305555187820736301)
          ·
            refine ⟨7409784114583195432776113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19759424305555187820736301 7409784114583195432776113)
            ·
              refine ⟨5557338085937396574582085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7409784114583195432776113 5557338085937396574582085)
              ·
                refine ⟨1042000891113261857734141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5557338085937396574582085 1042000891113261857734141)
                ·
                  refine ⟨390750334167473196650303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1042000891113261857734141 390750334167473196650303)
                  ·
                    rfl

theorem cell21_1712213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_1712213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712213 prefixEnd_1712213 := by exact prefixLift 1712213
  have htrace : WordTrace (prefixWord ++ tailWord_1712213) baseStart_1712213 baseEnd_1712213 := by
    simpa [prefixWord, tailWord_1712213, baseEnd_1712213] using wordTrace_append hprefix tailTrace_1712213
  have hstable : (prefixWord ++ tailWord_1712213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712213).length < 2 ^ (prefixWord ++ tailWord_1712213).sum := by decide
  have hdescent : baseEnd_1712213 < baseStart_1712213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712331 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 5]
def baseStart_1712331 : Nat := 118140960795 + 1712331 * 2 ^ 59
def prefixEnd_1712331 : Nat := 4983230072969 + 3 ^ 40 * 1712331 * 2
def baseEnd_1712331 : Nat := 390777263375131213683395

theorem tailTrace_1712331 : CollatzResearch.WordTrace tailWord_1712331 prefixEnd_1712331 390777263375131213683395 := by
  unfold tailWord_1712331
  simp only [CollatzResearch.WordTrace]
  refine ⟨62453842359524704697344847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41635894906349803131563231 62453842359524704697344847)
  ·
    refine ⟨93680763539287057046017271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62453842359524704697344847 93680763539287057046017271)
    ·
      refine ⟨140521145308930585569025907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93680763539287057046017271 140521145308930585569025907)
      ·
        refine ⟨210781717963395878353538861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140521145308930585569025907 210781717963395878353538861)
        ·
          refine ⟨79043144236273454382577073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210781717963395878353538861 79043144236273454382577073)
          ·
            refine ⟨59282358177205090786932805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79043144236273454382577073 59282358177205090786932805)
            ·
              refine ⟨11115442158225954522549901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59282358177205090786932805 11115442158225954522549901)
              ·
                refine ⟨4168290809334732945956213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11115442158225954522549901 4168290809334732945956213)
                ·
                  refine ⟨390777263375131213683395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4168290809334732945956213 390777263375131213683395)
                  ·
                    rfl

theorem cell21_1712331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 5].length) (baseStart_1712331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712331 prefixEnd_1712331 := by exact prefixLift 1712331
  have htrace : WordTrace (prefixWord ++ tailWord_1712331) baseStart_1712331 baseEnd_1712331 := by
    simpa [prefixWord, tailWord_1712331, baseEnd_1712331] using wordTrace_append hprefix tailTrace_1712331
  have hstable : (prefixWord ++ tailWord_1712331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712331).length < 2 ^ (prefixWord ++ tailWord_1712331).sum := by decide
  have hdescent : baseEnd_1712331 < baseStart_1712331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712334 : List Nat := [4, 1, 1, 1, 4, 3, 1, 6]
def baseStart_1712334 : Nat := 118140960795 + 1712334 * 2 ^ 59
def prefixEnd_1712334 : Nat := 4983230072969 + 3 ^ 40 * 1712334 * 2
def baseEnd_1712334 : Nat := 130259316005334625044463

theorem tailTrace_1712334 : CollatzResearch.WordTrace tailWord_1712334 prefixEnd_1712334 130259316005334625044463 := by
  unfold tailWord_1712334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7806743972314229526213007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41635967852342557473136037 7806743972314229526213007)
  ·
    refine ⟨11710115958471344289319511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7806743972314229526213007 11710115958471344289319511)
    ·
      refine ⟨17565173937707016433979267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11710115958471344289319511 17565173937707016433979267)
      ·
        refine ⟨26347760906560524650968901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17565173937707016433979267 26347760906560524650968901)
        ·
          refine ⟨4940205169980098372056669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26347760906560524650968901 4940205169980098372056669)
          ·
            refine ⟨1852576938742536889521251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4940205169980098372056669 1852576938742536889521251)
            ·
              refine ⟨2778865408113805334281877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852576938742536889521251 2778865408113805334281877)
              ·
                refine ⟨130259316005334625044463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2778865408113805334281877 130259316005334625044463)
                ·
                  rfl

theorem cell21_1712334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_1712334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712334 prefixEnd_1712334 := by exact prefixLift 1712334
  have htrace : WordTrace (prefixWord ++ tailWord_1712334) baseStart_1712334 baseEnd_1712334 := by
    simpa [prefixWord, tailWord_1712334, baseEnd_1712334] using wordTrace_append hprefix tailTrace_1712334
  have hstable : (prefixWord ++ tailWord_1712334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712334).length < 2 ^ (prefixWord ++ tailWord_1712334).sum := by decide
  have hdescent : baseEnd_1712334 < baseStart_1712334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712362 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 6]
def baseStart_1712362 : Nat := 118140960795 + 1712362 * 2 ^ 59
def prefixEnd_1712362 : Nat := 4983230072969 + 3 ^ 40 * 1712362 * 2
def baseEnd_1712362 : Nat := 390784337997482048666665

theorem tailTrace_1712362 : CollatzResearch.WordTrace tailWord_1712362 prefixEnd_1712362 390784337997482048666665 := by
  unfold tailWord_1712362
  simp only [CollatzResearch.WordTrace]
  refine ⟨15613743255603099247930835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41636648681608264661148893 15613743255603099247930835)
  ·
    refine ⟨23420614883404648871896253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15613743255603099247930835 23420614883404648871896253)
    ·
      refine ⟨8782730581276743326961095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23420614883404648871896253 8782730581276743326961095)
      ·
        refine ⟨13174095871915114990441643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8782730581276743326961095 13174095871915114990441643)
        ·
          refine ⟨19761143807872672485662465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13174095871915114990441643 19761143807872672485662465)
          ·
            refine ⟨14820857855904504364246849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19761143807872672485662465 14820857855904504364246849)
            ·
              refine ⟨11115643391928378273185137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14820857855904504364246849 11115643391928378273185137)
              ·
                refine ⟨8336732543946283704888853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11115643391928378273185137 8336732543946283704888853)
                ·
                  refine ⟨390784337997482048666665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8336732543946283704888853 390784337997482048666665)
                  ·
                    rfl

theorem cell21_1712362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_1712362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712362 prefixEnd_1712362 := by exact prefixLift 1712362
  have htrace : WordTrace (prefixWord ++ tailWord_1712362) baseStart_1712362 baseEnd_1712362 := by
    simpa [prefixWord, tailWord_1712362, baseEnd_1712362] using wordTrace_append hprefix tailTrace_1712362
  have hstable : (prefixWord ++ tailWord_1712362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712362).length < 2 ^ (prefixWord ++ tailWord_1712362).sum := by decide
  have hdescent : baseEnd_1712362 < baseStart_1712362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712441 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 5]
def baseStart_1712441 : Nat := 118140960795 + 1712441 * 2 ^ 59
def prefixEnd_1712441 : Nat := 4983230072969 + 3 ^ 40 * 1712441 * 2
def baseEnd_1712441 : Nat := 390802366873795466849837

theorem tailTrace_1712441 : CollatzResearch.WordTrace tailWord_1712441 prefixEnd_1712441 390802366873795466849837 := by
  unfold tailWord_1712441
  simp only [CollatzResearch.WordTrace]
  refine ⟨62457854389126193483849177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41638569592750795655899451 62457854389126193483849177)
  ·
    refine ⟨46843390791844645112886883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62457854389126193483849177 46843390791844645112886883)
    ·
      refine ⟨70265086187766967669330325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46843390791844645112886883 70265086187766967669330325)
      ·
        refine ⟨3293675915051576609499859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70265086187766967669330325 3293675915051576609499859)
        ·
          refine ⟨4940513872577364914249789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3293675915051576609499859 4940513872577364914249789)
          ·
            refine ⟨1852692702216511842843671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4940513872577364914249789 1852692702216511842843671)
            ·
              refine ⟨2779039053324767764265507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852692702216511842843671 2779039053324767764265507)
              ·
                refine ⟨4168558579987151646398261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2779039053324767764265507 4168558579987151646398261)
                ·
                  refine ⟨390802366873795466849837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4168558579987151646398261 390802366873795466849837)
                  ·
                    rfl

theorem cell21_1712441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_1712441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712441 prefixEnd_1712441 := by exact prefixLift 1712441
  have htrace : WordTrace (prefixWord ++ tailWord_1712441) baseStart_1712441 baseEnd_1712441 := by
    simpa [prefixWord, tailWord_1712441, baseEnd_1712441] using wordTrace_append hprefix tailTrace_1712441
  have hstable : (prefixWord ++ tailWord_1712441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712441).length < 2 ^ (prefixWord ++ tailWord_1712441).sum := by decide
  have hdescent : baseEnd_1712441 < baseStart_1712441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712621 : List Nat := [1, 5, 1, 3, 1, 1, 1, 8]
def baseStart_1712621 : Nat := 118140960795 + 1712621 * 2 ^ 59
def prefixEnd_1712621 : Nat := 4983230072969 + 3 ^ 40 * 1712621 * 2
def baseEnd_1712621 : Nat := 130281148442051717949823

theorem tailTrace_1712621 : CollatzResearch.WordTrace tailWord_1712621 prefixEnd_1712621 130281148442051717949823 := by
  unfold tailWord_1712621
  simp only [CollatzResearch.WordTrace]
  refine ⟨62464419528474084225401717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41642946352316056150267811 62464419528474084225401717)
  ·
    refine ⟨5856039330794445396131411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62464419528474084225401717 5856039330794445396131411)
    ·
      refine ⟨8784058996191668094197117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5856039330794445396131411 8784058996191668094197117)
      ·
        refine ⟨3294022123571875535323919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8784058996191668094197117 3294022123571875535323919)
        ·
          refine ⟨4941033185357813302985879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3294022123571875535323919 4941033185357813302985879)
          ·
            refine ⟨7411549778036719954478819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4941033185357813302985879 7411549778036719954478819)
            ·
              refine ⟨11117324667055079931718229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7411549778036719954478819 11117324667055079931718229)
              ·
                refine ⟨130281148442051717949823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11117324667055079931718229 130281148442051717949823)
                ·
                  rfl

theorem cell21_1712621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 8].length) (baseStart_1712621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712621 prefixEnd_1712621 := by exact prefixLift 1712621
  have htrace : WordTrace (prefixWord ++ tailWord_1712621) baseStart_1712621 baseEnd_1712621 := by
    simpa [prefixWord, tailWord_1712621, baseEnd_1712621] using wordTrace_append hprefix tailTrace_1712621
  have hstable : (prefixWord ++ tailWord_1712621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712621).length < 2 ^ (prefixWord ++ tailWord_1712621).sum := by decide
  have hdescent : baseEnd_1712621 < baseStart_1712621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712649 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 6]
def baseStart_1712649 : Nat := 118140960795 + 1712649 * 2 ^ 59
def prefixEnd_1712649 : Nat := 4983230072969 + 3 ^ 40 * 1712649 * 2
def baseEnd_1712649 : Nat := 390849835307633327382745

theorem tailTrace_1712649 : CollatzResearch.WordTrace tailWord_1712649 prefixEnd_1712649 390849835307633327382745 := by
  unfold tailWord_1712649
  simp only [CollatzResearch.WordTrace]
  refine ⟨62465440772372645007421001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41643627181581763338280667 62465440772372645007421001)
  ·
    refine ⟨46849080579279483755565751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62465440772372645007421001 46849080579279483755565751)
    ·
      refine ⟨70273620868919225633348627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46849080579279483755565751 70273620868919225633348627)
      ·
        refine ⟨105410431303378838450022941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70273620868919225633348627 105410431303378838450022941)
        ·
          refine ⟨39528911738767064418758603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105410431303378838450022941 39528911738767064418758603)
          ·
            refine ⟨59293367608150596628137905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39528911738767064418758603 59293367608150596628137905)
            ·
              refine ⟨44470025706112947471103429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59293367608150596628137905 44470025706112947471103429)
              ·
                refine ⟨8338129819896177650831893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44470025706112947471103429 8338129819896177650831893)
                ·
                  refine ⟨390849835307633327382745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8338129819896177650831893 390849835307633327382745)
                  ·
                    rfl

theorem cell21_1712649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_1712649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712649 prefixEnd_1712649 := by exact prefixLift 1712649
  have htrace : WordTrace (prefixWord ++ tailWord_1712649) baseStart_1712649 baseEnd_1712649 := by
    simpa [prefixWord, tailWord_1712649, baseEnd_1712649] using wordTrace_append hprefix tailTrace_1712649
  have hstable : (prefixWord ++ tailWord_1712649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712649).length < 2 ^ (prefixWord ++ tailWord_1712649).sum := by decide
  have hdescent : baseEnd_1712649 < baseStart_1712649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712666 : List Nat := [3, 1, 1, 3, 1, 1, 3, 4, 4]
def baseStart_1712666 : Nat := 118140960795 + 1712666 * 2 ^ 59
def prefixEnd_1712666 : Nat := 4983230072969 + 3 ^ 40 * 1712666 * 2
def baseEnd_1712666 : Nat := 390853714939245075599377

theorem tailTrace_1712666 : CollatzResearch.WordTrace tailWord_1712666 prefixEnd_1712666 390853714939245075599377 := by
  unfold tailWord_1712666
  simp only [CollatzResearch.WordTrace]
  refine ⟨15616515203327764227697463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41644040542207371273859901 15616515203327764227697463)
  ·
    refine ⟨23424772804991646341546195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15616515203327764227697463 23424772804991646341546195)
    ·
      refine ⟨35137159207487469512319293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23424772804991646341546195 35137159207487469512319293)
      ·
        refine ⟨13176434702807801067119735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35137159207487469512319293 13176434702807801067119735)
        ·
          refine ⟨19764652054211701600679603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13176434702807801067119735 19764652054211701600679603)
          ·
            refine ⟨29646978081317552401019405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19764652054211701600679603 29646978081317552401019405)
            ·
              refine ⟨11117616780494082150382277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29646978081317552401019405 11117616780494082150382277)
              ·
                refine ⟨2084553146342640403196677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11117616780494082150382277 2084553146342640403196677)
                ·
                  refine ⟨390853714939245075599377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2084553146342640403196677 390853714939245075599377)
                  ·
                    rfl

theorem cell21_1712666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_1712666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712666 prefixEnd_1712666 := by exact prefixLift 1712666
  have htrace : WordTrace (prefixWord ++ tailWord_1712666) baseStart_1712666 baseEnd_1712666 := by
    simpa [prefixWord, tailWord_1712666, baseEnd_1712666] using wordTrace_append hprefix tailTrace_1712666
  have hstable : (prefixWord ++ tailWord_1712666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712666).length < 2 ^ (prefixWord ++ tailWord_1712666).sum := by decide
  have hdescent : baseEnd_1712666 < baseStart_1712666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712669 : List Nat := [1, 4, 2, 2, 1, 3, 1, 4, 3]
def baseStart_1712669 : Nat := 118140960795 + 1712669 * 2 ^ 59
def prefixEnd_1712669 : Nat := 4983230072969 + 3 ^ 40 * 1712669 * 2
def baseEnd_1712669 : Nat := 390854399580117737049371

theorem tailTrace_1712669 : CollatzResearch.WordTrace tailWord_1712669 prefixEnd_1712669 390854399580117737049371 := by
  unfold tailWord_1712669
  simp only [CollatzResearch.WordTrace]
  refine ⟨62466170232300188423149061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41644113488200125615432707 62466170232300188423149061)
  ·
    refine ⟨11712406918556285329340449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62466170232300188423149061 11712406918556285329340449)
    ·
      refine ⟨8784305188917213997005337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11712406918556285329340449 8784305188917213997005337)
      ·
        refine ⟨6588228891687910497754003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8784305188917213997005337 6588228891687910497754003)
        ·
          refine ⟨9882343337531865746631005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6588228891687910497754003 9882343337531865746631005)
          ·
            refine ⟨3705878751574449654986627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9882343337531865746631005 3705878751574449654986627)
            ·
              refine ⟨5558818127361674482479941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3705878751574449654986627 5558818127361674482479941)
              ·
                refine ⟨1042278398880313965464989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5558818127361674482479941 1042278398880313965464989)
                ·
                  refine ⟨390854399580117737049371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1042278398880313965464989 390854399580117737049371)
                  ·
                    rfl

theorem cell21_1712669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_1712669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712669 prefixEnd_1712669 := by exact prefixLift 1712669
  have htrace : WordTrace (prefixWord ++ tailWord_1712669) baseStart_1712669 baseEnd_1712669 := by
    simpa [prefixWord, tailWord_1712669, baseEnd_1712669] using wordTrace_append hprefix tailTrace_1712669
  have hstable : (prefixWord ++ tailWord_1712669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712669).length < 2 ^ (prefixWord ++ tailWord_1712669).sum := by decide
  have hdescent : baseEnd_1712669 < baseStart_1712669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712697 : List Nat := [1, 2, 1, 5, 1, 1, 5, 5]
def baseStart_1712697 : Nat := 118140960795 + 1712697 * 2 ^ 59
def prefixEnd_1712697 : Nat := 4983230072969 + 3 ^ 40 * 1712697 * 2
def baseEnd_1712697 : Nat := 130286929853865303527549

theorem tailTrace_1712697 : CollatzResearch.WordTrace tailWord_1712697 prefixEnd_1712697 130286929853865303527549 := by
  unfold tailWord_1712697
  simp only [CollatzResearch.WordTrace]
  refine ⟨62467191476198749205168345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41644794317465832803445563 62467191476198749205168345)
  ·
    refine ⟨46850393607149061903876259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62467191476198749205168345 46850393607149061903876259)
    ·
      refine ⟨70275590410723592855814389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46850393607149061903876259 70275590410723592855814389)
      ·
        refine ⟨6588336601005336830232599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70275590410723592855814389 6588336601005336830232599)
        ·
          refine ⟨9882504901508005245348899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6588336601005336830232599 9882504901508005245348899)
          ·
            refine ⟨14823757352262007868023349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9882504901508005245348899 14823757352262007868023349)
            ·
              refine ⟨1389727251774563237627189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14823757352262007868023349 1389727251774563237627189)
              ·
                refine ⟨130286929853865303527549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1389727251774563237627189 130286929853865303527549)
                ·
                  rfl

theorem cell21_1712697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 5].length) (baseStart_1712697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712697 prefixEnd_1712697 := by exact prefixLift 1712697
  have htrace : WordTrace (prefixWord ++ tailWord_1712697) baseStart_1712697 baseEnd_1712697 := by
    simpa [prefixWord, tailWord_1712697, baseEnd_1712697] using wordTrace_append hprefix tailTrace_1712697
  have hstable : (prefixWord ++ tailWord_1712697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712697).length < 2 ^ (prefixWord ++ tailWord_1712697).sum := by decide
  have hdescent : baseEnd_1712697 < baseStart_1712697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712728 : List Nat := [2, 1, 2, 2, 1, 2, 4, 4, 3]
def baseStart_1712728 : Nat := 118140960795 + 1712728 * 2 ^ 59
def prefixEnd_1712728 : Nat := 4983230072969 + 3 ^ 40 * 1712728 * 2
def baseEnd_1712728 : Nat := 390867864183946745565917

theorem tailTrace_1712728 : CollatzResearch.WordTrace tailWord_1712728 prefixEnd_1712728 390867864183946745565917 := by
  unfold tailWord_1712728
  simp only [CollatzResearch.WordTrace]
  refine ⟨31234161069543220749773419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41645548092724294333031225 31234161069543220749773419)
  ·
    refine ⟨46851241604314831124660129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31234161069543220749773419 46851241604314831124660129)
    ·
      refine ⟨35138431203236123343495097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46851241604314831124660129 35138431203236123343495097)
      ·
        refine ⟨26353823402427092507621323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35138431203236123343495097 26353823402427092507621323)
        ·
          refine ⟨39530735103640638761431985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26353823402427092507621323 39530735103640638761431985)
          ·
            refine ⟨29648051327730479071073989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39530735103640638761431985 29648051327730479071073989)
            ·
              refine ⟨5559009623949464825826373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29648051327730479071073989 5559009623949464825826373)
              ·
                refine ⟨1042314304490524654842445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5559009623949464825826373 1042314304490524654842445)
                ·
                  refine ⟨390867864183946745565917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1042314304490524654842445 390867864183946745565917)
                  ·
                    rfl

theorem cell21_1712728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 3].length) (baseStart_1712728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712728 prefixEnd_1712728 := by exact prefixLift 1712728
  have htrace : WordTrace (prefixWord ++ tailWord_1712728) baseStart_1712728 baseEnd_1712728 := by
    simpa [prefixWord, tailWord_1712728, baseEnd_1712728] using wordTrace_append hprefix tailTrace_1712728
  have hstable : (prefixWord ++ tailWord_1712728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712728).length < 2 ^ (prefixWord ++ tailWord_1712728).sum := by decide
  have hdescent : baseEnd_1712728 < baseStart_1712728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712863 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 5]
def baseStart_1712863 : Nat := 118140960795 + 1712863 * 2 ^ 59
def prefixEnd_1712863 : Nat := 4983230072969 + 3 ^ 40 * 1712863 * 2
def baseEnd_1712863 : Nat := 390898673023216510815641

theorem tailTrace_1712863 : CollatzResearch.WordTrace tailWord_1712863 prefixEnd_1712863 390898673023216510815641 := by
  unfold tailWord_1712863
  simp only [CollatzResearch.WordTrace]
  refine ⟨62473245993597359555711243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41648830662398239703807495 62473245993597359555711243)
  ·
    refine ⟨93709868990396039333566865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62473245993597359555711243 93709868990396039333566865)
    ·
      refine ⟨70282401742797029500175149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93709868990396039333566865 70282401742797029500175149)
      ·
        refine ⟨26355900653548886062565681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70282401742797029500175149 26355900653548886062565681)
        ·
          refine ⟨19766925490161664546924261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26355900653548886062565681 19766925490161664546924261)
          ·
            refine ⟨3706298529405312102548299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19766925490161664546924261 3706298529405312102548299)
            ·
              refine ⟨5559447794107968153822449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3706298529405312102548299 5559447794107968153822449)
              ·
                refine ⟨4169585845580976115366837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5559447794107968153822449 4169585845580976115366837)
                ·
                  refine ⟨390898673023216510815641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4169585845580976115366837 390898673023216510815641)
                  ·
                    rfl

theorem cell21_1712863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 5].length) (baseStart_1712863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712863 prefixEnd_1712863 := by exact prefixLift 1712863
  have htrace : WordTrace (prefixWord ++ tailWord_1712863) baseStart_1712863 baseEnd_1712863 := by
    simpa [prefixWord, tailWord_1712863, baseEnd_1712863] using wordTrace_append hprefix tailTrace_1712863
  have hstable : (prefixWord ++ tailWord_1712863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712863).length < 2 ^ (prefixWord ++ tailWord_1712863).sum := by decide
  have hdescent : baseEnd_1712863 < baseStart_1712863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712880 : List Nat := [2, 1, 1, 1, 3, 1, 6, 3, 3]
def baseStart_1712880 : Nat := 118140960795 + 1712880 * 2 ^ 59
def prefixEnd_1712880 : Nat := 4983230072969 + 3 ^ 40 * 1712880 * 2
def baseEnd_1712880 : Nat := 390902552654828259032273

theorem tailTrace_1712880 : CollatzResearch.WordTrace tailWord_1712880 prefixEnd_1712880 390902552654828259032273 := by
  unfold tailWord_1712880
  simp only [CollatzResearch.WordTrace]
  refine ⟨31236933017267885729540047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41649244023023847639386729 31236933017267885729540047)
  ·
    refine ⟨46855399525901828594310071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31236933017267885729540047 46855399525901828594310071)
    ·
      refine ⟨70283099288852742891465107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46855399525901828594310071 70283099288852742891465107)
      ·
        refine ⟨105424648933279114337197661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70283099288852742891465107 105424648933279114337197661)
        ·
          refine ⟨39534243349979667876449123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105424648933279114337197661 39534243349979667876449123)
          ·
            refine ⟨59301365024969501814673685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39534243349979667876449123 59301365024969501814673685)
            ·
              refine ⟨2779751485545445397562829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59301365024969501814673685 2779751485545445397562829)
              ·
                refine ⟨1042406807079542024086061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2779751485545445397562829 1042406807079542024086061)
                ·
                  refine ⟨390902552654828259032273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1042406807079542024086061 390902552654828259032273)
                  ·
                    rfl

theorem cell21_1712880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 3].length) (baseStart_1712880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1712880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1712880 prefixEnd_1712880 := by exact prefixLift 1712880
  have htrace : WordTrace (prefixWord ++ tailWord_1712880) baseStart_1712880 baseEnd_1712880 := by
    simpa [prefixWord, tailWord_1712880, baseEnd_1712880] using wordTrace_append hprefix tailTrace_1712880
  have hstable : (prefixWord ++ tailWord_1712880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712880).length < 2 ^ (prefixWord ++ tailWord_1712880).sum := by decide
  have hdescent : baseEnd_1712880 < baseStart_1712880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713125 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 5]
def baseStart_1713125 : Nat := 118140960795 + 1713125 * 2 ^ 59
def prefixEnd_1713125 : Nat := 4983230072969 + 3 ^ 40 * 1713125 * 2
def baseEnd_1713125 : Nat := 390958464992762277448439

theorem tailTrace_1713125 : CollatzResearch.WordTrace tailWord_1713125 prefixEnd_1713125 390958464992762277448439 := by
  unfold tailWord_1713125
  simp only [CollatzResearch.WordTrace]
  refine ⟨62482801918648178301748829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41655201279098785534499219 62482801918648178301748829)
  ·
    refine ⟨23431050719493066863155811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62482801918648178301748829 23431050719493066863155811)
    ·
      refine ⟨35146576079239600294733717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23431050719493066863155811 35146576079239600294733717)
      ·
        refine ⟨1647495753714356263815643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35146576079239600294733717 1647495753714356263815643)
        ·
          refine ⟨2471243630571534395723465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1647495753714356263815643 2471243630571534395723465)
          ·
            refine ⟨1853432722928650796792599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2471243630571534395723465 1853432722928650796792599)
            ·
              refine ⟨2780149084392976195188899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1853432722928650796792599 2780149084392976195188899)
              ·
                refine ⟨4170223626589464292783349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2780149084392976195188899 4170223626589464292783349)
                ·
                  refine ⟨390958464992762277448439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4170223626589464292783349 390958464992762277448439)
                  ·
                    rfl

theorem cell21_1713125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_1713125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713125 prefixEnd_1713125 := by exact prefixLift 1713125
  have htrace : WordTrace (prefixWord ++ tailWord_1713125) baseStart_1713125 baseEnd_1713125 := by
    simpa [prefixWord, tailWord_1713125, baseEnd_1713125] using wordTrace_append hprefix tailTrace_1713125
  have hstable : (prefixWord ++ tailWord_1713125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713125).length < 2 ^ (prefixWord ++ tailWord_1713125).sum := by decide
  have hdescent : baseEnd_1713125 < baseStart_1713125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713170 : List Nat := [3, 2, 5, 1, 1, 9]
def baseStart_1713170 : Nat := 118140960795 + 1713170 * 2 ^ 59
def prefixEnd_1713170 : Nat := 4983230072969 + 3 ^ 40 * 1713170 * 2
def baseEnd_1713170 : Nat := 14480323503920451822161

theorem tailTrace_1713170 : CollatzResearch.WordTrace tailWord_1713170 prefixEnd_1713170 14480323503920451822161 := by
  unfold tailWord_1713170
  simp only [CollatzResearch.WordTrace]
  refine ⟨15621110800871287746784241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41656295468990100658091309 15621110800871287746784241)
  ·
    refine ⟨11715833100653465810088181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15621110800871287746784241 11715833100653465810088181)
    ·
      refine ⟨1098359353186262419695767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11715833100653465810088181 1098359353186262419695767)
      ·
        refine ⟨1647539029779393629543651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098359353186262419695767 1647539029779393629543651)
        ·
          refine ⟨2471308544669090444315477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1647539029779393629543651 2471308544669090444315477)
          ·
            refine ⟨14480323503920451822161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2471308544669090444315477 14480323503920451822161)
            ·
              rfl

theorem cell21_1713170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 9].length) (baseStart_1713170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713170 prefixEnd_1713170 := by exact prefixLift 1713170
  have htrace : WordTrace (prefixWord ++ tailWord_1713170) baseStart_1713170 baseEnd_1713170 := by
    simpa [prefixWord, tailWord_1713170, baseEnd_1713170] using wordTrace_append hprefix tailTrace_1713170
  have hstable : (prefixWord ++ tailWord_1713170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713170).length < 2 ^ (prefixWord ++ tailWord_1713170).sum := by decide
  have hdescent : baseEnd_1713170 < baseStart_1713170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713198 : List Nat := [4, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_1713198 : Nat := 118140960795 + 1713198 * 2 ^ 59
def prefixEnd_1713198 : Nat := 4983230072969 + 3 ^ 40 * 1713198 * 2
def baseEnd_1713198 : Nat := 390975124587330372731623

theorem tailTrace_1713198 : CollatzResearch.WordTrace tailWord_1713198 prefixEnd_1713198 390975124587330372731623 := by
  unfold tailWord_1713198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7810683055922963971144531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41656976298255807846104165 7810683055922963971144531)
  ·
    refine ⟨11716024583884445956716797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7810683055922963971144531 11716024583884445956716797)
    ·
      refine ⟨4393509218956667233768799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11716024583884445956716797 4393509218956667233768799)
      ·
        refine ⟨6590263828435000850653199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4393509218956667233768799 6590263828435000850653199)
        ·
          refine ⟨9885395742652501275979799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6590263828435000850653199 9885395742652501275979799)
          ·
            refine ⟨14828093613978751913969699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9885395742652501275979799 14828093613978751913969699)
            ·
              refine ⟨22242140420968127870954549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14828093613978751913969699 22242140420968127870954549)
              ·
                refine ⟨2085200664465761987901989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22242140420968127870954549 2085200664465761987901989)
                ·
                  refine ⟨390975124587330372731623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2085200664465761987901989 390975124587330372731623)
                  ·
                    rfl

theorem cell21_1713198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_1713198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713198 prefixEnd_1713198 := by exact prefixLift 1713198
  have htrace : WordTrace (prefixWord ++ tailWord_1713198) baseStart_1713198 baseEnd_1713198 := by
    simpa [prefixWord, tailWord_1713198, baseEnd_1713198] using wordTrace_append hprefix tailTrace_1713198
  have hstable : (prefixWord ++ tailWord_1713198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713198).length < 2 ^ (prefixWord ++ tailWord_1713198).sum := by decide
  have hdescent : baseEnd_1713198 < baseStart_1713198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713271 : List Nat := [1, 1, 3, 1, 1, 4, 3, 7]
def baseStart_1713271 : Nat := 118140960795 + 1713271 * 2 ^ 59
def prefixEnd_1713271 : Nat := 4983230072969 + 3 ^ 40 * 1713271 * 2
def baseEnd_1713271 : Nat := 130330594727299489338269

theorem tailTrace_1713271 : CollatzResearch.WordTrace tailWord_1713271 prefixEnd_1713271 130330594727299489338269 := by
  unfold tailWord_1713271
  simp only [CollatzResearch.WordTrace]
  refine ⟨62488126976119245236563667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41658751317412830157709111 62488126976119245236563667)
  ·
    refine ⟨93732190464178867854845501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62488126976119245236563667 93732190464178867854845501)
    ·
      refine ⟨35149571424067075445567063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93732190464178867854845501 35149571424067075445567063)
      ·
        refine ⟨52724357136100613168350595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35149571424067075445567063 52724357136100613168350595)
        ·
          refine ⟨79086535704150919752525893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52724357136100613168350595 79086535704150919752525893)
          ·
            refine ⟨14828725444528297453598605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79086535704150919752525893 14828725444528297453598605)
            ·
              refine ⟨5560772041698111545099477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14828725444528297453598605 5560772041698111545099477)
              ·
                refine ⟨130330594727299489338269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5560772041698111545099477 130330594727299489338269)
                ·
                  rfl

theorem cell21_1713271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 7].length) (baseStart_1713271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713271 prefixEnd_1713271 := by exact prefixLift 1713271
  have htrace : WordTrace (prefixWord ++ tailWord_1713271) baseStart_1713271 baseEnd_1713271 := by
    simpa [prefixWord, tailWord_1713271, baseEnd_1713271] using wordTrace_append hprefix tailTrace_1713271
  have hstable : (prefixWord ++ tailWord_1713271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713271).length < 2 ^ (prefixWord ++ tailWord_1713271).sum := by decide
  have hdescent : baseEnd_1713271 < baseStart_1713271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713381 : List Nat := [1, 3, 1, 4, 3, 1, 3, 5]
def baseStart_1713381 : Nat := 118140960795 + 1713381 * 2 ^ 59
def prefixEnd_1713381 : Nat := 4983230072969 + 3 ^ 40 * 1713381 * 2
def baseEnd_1713381 : Nat := 130338962560187573727083

theorem tailTrace_1713381 : CollatzResearch.WordTrace tailWord_1713381 prefixEnd_1713381 130338962560187573727083 := by
  unfold tailWord_1713381
  simp only [CollatzResearch.WordTrace]
  refine ⟨62492139005720734023067997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41661426003813822682045331 62492139005720734023067997)
  ·
    refine ⟨23434552127145275258650499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62492139005720734023067997 23434552127145275258650499)
    ·
      refine ⟨35151828190717912887975749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23434552127145275258650499 35151828190717912887975749)
      ·
        refine ⟨6590967785759608666495453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35151828190717912887975749 6590967785759608666495453)
        ·
          refine ⟨2471612919659853249935795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6590967785759608666495453 2471612919659853249935795)
          ·
            refine ⟨3707419379489779874903693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2471612919659853249935795 3707419379489779874903693)
            ·
              refine ⟨1390282267308667453088885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3707419379489779874903693 1390282267308667453088885)
              ·
                refine ⟨130338962560187573727083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1390282267308667453088885 130338962560187573727083)
                ·
                  rfl

theorem cell21_1713381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 5].length) (baseStart_1713381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713381 prefixEnd_1713381 := by exact prefixLift 1713381
  have htrace : WordTrace (prefixWord ++ tailWord_1713381) baseStart_1713381 baseEnd_1713381 := by
    simpa [prefixWord, tailWord_1713381, baseEnd_1713381] using wordTrace_append hprefix tailTrace_1713381
  have hstable : (prefixWord ++ tailWord_1713381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713381).length < 2 ^ (prefixWord ++ tailWord_1713381).sum := by decide
  have hdescent : baseEnd_1713381 < baseStart_1713381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713395 : List Nat := [1, 1, 1, 2, 2, 5, 1, 5, 3]
def baseStart_1713395 : Nat := 118140960795 + 1713395 * 2 ^ 59
def prefixEnd_1713395 : Nat := 4983230072969 + 3 ^ 40 * 1713395 * 2
def baseEnd_1713395 : Nat := 391020082671301807947887

theorem tailTrace_1713395 : CollatzResearch.WordTrace tailWord_1713395 prefixEnd_1713395 391020082671301807947887 := by
  unfold tailWord_1713395
  simp only [CollatzResearch.WordTrace]
  refine ⟨62492649627670014414077639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41661766418446676276051759 62492649627670014414077639)
  ·
    refine ⟨93738974441505021621116459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62492649627670014414077639 93738974441505021621116459)
    ·
      refine ⟨140608461662257532431674689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93738974441505021621116459 140608461662257532431674689)
      ·
        refine ⟨105456346246693149323756017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140608461662257532431674689 105456346246693149323756017)
        ·
          refine ⟨79092259685019861992817013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105456346246693149323756017 79092259685019861992817013)
          ·
            refine ⟨7414899345470612061826595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79092259685019861992817013 7414899345470612061826595)
            ·
              refine ⟨11122349018205918092739893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7414899345470612061826595 11122349018205918092739893)
              ·
                refine ⟨1042720220456804821194365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11122349018205918092739893 1042720220456804821194365)
                ·
                  refine ⟨391020082671301807947887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1042720220456804821194365 391020082671301807947887)
                  ·
                    rfl

theorem cell21_1713395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 3].length) (baseStart_1713395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713395 prefixEnd_1713395 := by exact prefixLift 1713395
  have htrace : WordTrace (prefixWord ++ tailWord_1713395) baseStart_1713395 baseEnd_1713395 := by
    simpa [prefixWord, tailWord_1713395, baseEnd_1713395] using wordTrace_append hprefix tailTrace_1713395
  have hstable : (prefixWord ++ tailWord_1713395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713395).length < 2 ^ (prefixWord ++ tailWord_1713395).sum := by decide
  have hdescent : baseEnd_1713395 < baseStart_1713395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713409 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 6]
def baseStart_1713409 : Nat := 118140960795 + 1713409 * 2 ^ 59
def prefixEnd_1713409 : Nat := 4983230072969 + 3 ^ 40 * 1713409 * 2
def baseEnd_1713409 : Nat := 391023277662040894714525

theorem tailTrace_1713409 : CollatzResearch.WordTrace tailWord_1713409 prefixEnd_1713409 391023277662040894714525 := by
  unfold tailWord_1713409
  simp only [CollatzResearch.WordTrace]
  refine ⟨62493160249619294805087281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41662106833079529870058187 62493160249619294805087281)
  ·
    refine ⟨46869870187214471103815461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62493160249619294805087281 46869870187214471103815461)
    ·
      refine ⟨8788100660102713331965399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46869870187214471103815461 8788100660102713331965399)
      ·
        refine ⟨13182150990154069997948099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8788100660102713331965399 13182150990154069997948099)
        ·
          refine ⟨19773226485231104996922149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13182150990154069997948099 19773226485231104996922149)
          ·
            refine ⟨3707479965980832186922903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19773226485231104996922149 3707479965980832186922903)
            ·
              refine ⟨5561219948971248280384355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3707479965980832186922903 5561219948971248280384355)
              ·
                refine ⟨8341829923456872420576533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5561219948971248280384355 8341829923456872420576533)
                ·
                  refine ⟨391023277662040894714525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8341829923456872420576533 391023277662040894714525)
                  ·
                    rfl

theorem cell21_1713409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_1713409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713409 prefixEnd_1713409 := by exact prefixLift 1713409
  have htrace : WordTrace (prefixWord ++ tailWord_1713409) baseStart_1713409 baseEnd_1713409 := by
    simpa [prefixWord, tailWord_1713409, baseEnd_1713409] using wordTrace_append hprefix tailTrace_1713409
  have hstable : (prefixWord ++ tailWord_1713409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713409).length < 2 ^ (prefixWord ++ tailWord_1713409).sum := by decide
  have hdescent : baseEnd_1713409 < baseStart_1713409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713412 : List Nat := [2, 3, 2, 2, 2, 1, 2, 4, 3]
def baseStart_1713412 : Nat := 118140960795 + 1713412 * 2 ^ 59
def prefixEnd_1713412 : Nat := 4983230072969 + 3 ^ 40 * 1713412 * 2
def baseEnd_1713412 : Nat := 391023962302913556164519

theorem tailTrace_1713412 : CollatzResearch.WordTrace tailWord_1713412 prefixEnd_1713412 391023962302913556164519 := by
  unfold tailWord_1713412
  simp only [CollatzResearch.WordTrace]
  refine ⟨31246634834304213158723245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41662179779072284211630993 31246634834304213158723245)
  ·
    refine ⟨11717488062864079934521217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31246634834304213158723245 11717488062864079934521217)
    ·
      refine ⟨8788116047148059950890913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11717488062864079934521217 8788116047148059950890913)
      ·
        refine ⟨6591087035361044963168185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8788116047148059950890913 6591087035361044963168185)
        ·
          refine ⟨4943315276520783722376139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6591087035361044963168185 4943315276520783722376139)
          ·
            refine ⟨7414972914781175583564209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4943315276520783722376139 7414972914781175583564209)
            ·
              refine ⟨5561229686085881687673157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7414972914781175583564209 5561229686085881687673157)
              ·
                refine ⟨1042730566141102816438717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5561229686085881687673157 1042730566141102816438717)
                ·
                  refine ⟨391023962302913556164519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1042730566141102816438717 391023962302913556164519)
                  ·
                    rfl

theorem cell21_1713412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_1713412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713412 prefixEnd_1713412 := by exact prefixLift 1713412
  have htrace : WordTrace (prefixWord ++ tailWord_1713412) baseStart_1713412 baseEnd_1713412 := by
    simpa [prefixWord, tailWord_1713412, baseEnd_1713412] using wordTrace_append hprefix tailTrace_1713412
  have hstable : (prefixWord ++ tailWord_1713412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713412).length < 2 ^ (prefixWord ++ tailWord_1713412).sum := by decide
  have hdescent : baseEnd_1713412 < baseStart_1713412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713440 : List Nat := [2, 1, 1, 5, 3, 1, 1, 7]
def baseStart_1713440 : Nat := 118140960795 + 1713440 * 2 ^ 59
def prefixEnd_1713440 : Nat := 4983230072969 + 3 ^ 40 * 1713440 * 2
def baseEnd_1713440 : Nat := 130343450761463909899265

theorem tailTrace_1713440 : CollatzResearch.WordTrace tailWord_1713440 prefixEnd_1713440 130343450761463909899265 := by
  unfold tailWord_1713440
  simp only [CollatzResearch.WordTrace]
  refine ⟨31247145456253493549732887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41662860608337991399643849 31247145456253493549732887)
  ·
    refine ⟨46870718184380240324599331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31247145456253493549732887 46870718184380240324599331)
    ·
      refine ⟨70306077276570360486898997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46870718184380240324599331 70306077276570360486898997)
      ·
        refine ⟨6591194744678471295646781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70306077276570360486898997 6591194744678471295646781)
        ·
          refine ⟨2471698029254426735867543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6591194744678471295646781 2471698029254426735867543)
          ·
            refine ⟨3707547043881640103801315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2471698029254426735867543 3707547043881640103801315)
            ·
              refine ⟨5561320565822460155701973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3707547043881640103801315 5561320565822460155701973)
              ·
                refine ⟨130343450761463909899265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5561320565822460155701973 130343450761463909899265)
                ·
                  rfl

theorem cell21_1713440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 7].length) (baseStart_1713440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713440 prefixEnd_1713440 := by exact prefixLift 1713440
  have htrace : WordTrace (prefixWord ++ tailWord_1713440) baseStart_1713440 baseEnd_1713440 := by
    simpa [prefixWord, tailWord_1713440, baseEnd_1713440] using wordTrace_append hprefix tailTrace_1713440
  have hstable : (prefixWord ++ tailWord_1713440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713440).length < 2 ^ (prefixWord ++ tailWord_1713440).sum := by decide
  have hdescent : baseEnd_1713440 < baseStart_1713440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713471 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 5]
def baseStart_1713471 : Nat := 118140960795 + 1713471 * 2 ^ 59
def prefixEnd_1713471 : Nat := 4983230072969 + 3 ^ 40 * 1713471 * 2
def baseEnd_1713471 : Nat := 391037426906742564681065

theorem tailTrace_1713471 : CollatzResearch.WordTrace tailWord_1713471 prefixEnd_1713471 391037426906742564681065 := by
  unfold tailWord_1713471
  simp only [CollatzResearch.WordTrace]
  refine ⟨62495421575394679393844267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41663614383596452929229511 62495421575394679393844267)
  ·
    refine ⟨93743132363092019090766401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62495421575394679393844267 93743132363092019090766401)
    ·
      refine ⟨70307349272319014318074801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93743132363092019090766401 70307349272319014318074801)
      ·
        refine ⟨52730511954239260738556101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70307349272319014318074801 52730511954239260738556101)
        ·
          refine ⟨9886970991419861388479269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52730511954239260738556101 9886970991419861388479269)
          ·
            refine ⟨1853807060891224010339863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9886970991419861388479269 1853807060891224010339863)
            ·
              refine ⟨2780710591336836015509795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1853807060891224010339863 2780710591336836015509795)
              ·
                refine ⟨4171065887005254023264693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2780710591336836015509795 4171065887005254023264693)
                ·
                  refine ⟨391037426906742564681065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4171065887005254023264693 391037426906742564681065)
                  ·
                    rfl

theorem cell21_1713471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 5].length) (baseStart_1713471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713471 prefixEnd_1713471 := by exact prefixLift 1713471
  have htrace : WordTrace (prefixWord ++ tailWord_1713471) baseStart_1713471 baseEnd_1713471 := by
    simpa [prefixWord, tailWord_1713471, baseEnd_1713471] using wordTrace_append hprefix tailTrace_1713471
  have hstable : (prefixWord ++ tailWord_1713471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713471).length < 2 ^ (prefixWord ++ tailWord_1713471).sum := by decide
  have hdescent : baseEnd_1713471 < baseStart_1713471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713513 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 9]
def baseStart_1713513 : Nat := 118140960795 + 1713513 * 2 ^ 59
def prefixEnd_1713513 : Nat := 4983230072969 + 3 ^ 40 * 1713513 * 2
def baseEnd_1713513 : Nat := 391047011878959824980979

theorem tailTrace_1713513 : CollatzResearch.WordTrace tailWord_1713513 prefixEnd_1713513 391047011878959824980979 := by
  unfold tailWord_1713513
  simp only [CollatzResearch.WordTrace]
  refine ⟨62496953441242520566873193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41664635627495013711248795 62496953441242520566873193)
  ·
    refine ⟨46872715080931890425154895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62496953441242520566873193 46872715080931890425154895)
    ·
      refine ⟨70309072621397835637732343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46872715080931890425154895 70309072621397835637732343)
      ·
        refine ⟨105463608932096753456598515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70309072621397835637732343 105463608932096753456598515)
        ·
          refine ⟨158195413398145130184897773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105463608932096753456598515 158195413398145130184897773)
          ·
            refine ⟨59323280024304423819336665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158195413398145130184897773 59323280024304423819336665)
            ·
              refine ⟨44492460018228317864502499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59323280024304423819336665 44492460018228317864502499)
              ·
                refine ⟨66738690027342476796753749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44492460018228317864502499 66738690027342476796753749)
                ·
                  refine ⟨391047011878959824980979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66738690027342476796753749 391047011878959824980979)
                  ·
                    rfl

theorem cell21_1713513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_1713513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713513 prefixEnd_1713513 := by exact prefixLift 1713513
  have htrace : WordTrace (prefixWord ++ tailWord_1713513) baseStart_1713513 baseEnd_1713513 := by
    simpa [prefixWord, tailWord_1713513, baseEnd_1713513] using wordTrace_append hprefix tailTrace_1713513
  have hstable : (prefixWord ++ tailWord_1713513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713513).length < 2 ^ (prefixWord ++ tailWord_1713513).sum := by decide
  have hdescent : baseEnd_1713513 < baseStart_1713513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713575 : List Nat := [1, 1, 6, 1, 1, 1, 10]
def baseStart_1713575 : Nat := 118140960795 + 1713575 * 2 ^ 59
def prefixEnd_1713575 : Nat := 4983230072969 + 3 ^ 40 * 1713575 * 2
def baseEnd_1713575 : Nat := 43451240124851277216391

theorem tailTrace_1713575 : CollatzResearch.WordTrace tailWord_1713575 prefixEnd_1713575 43451240124851277216391 := by
  unfold tailWord_1713575
  simp only [CollatzResearch.WordTrace]
  refine ⟨62499214767017905155630179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41666143178011936770420119 62499214767017905155630179)
  ·
    refine ⟨93748822150526857733445269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62499214767017905155630179 93748822150526857733445269)
    ·
      refine ⟨4394476038305946456255247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93748822150526857733445269 4394476038305946456255247)
      ·
        refine ⟨6591714057458919684382871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4394476038305946456255247 6591714057458919684382871)
        ·
          refine ⟨9887571086188379526574307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6591714057458919684382871 9887571086188379526574307)
          ·
            refine ⟨14831356629282569289861461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9887571086188379526574307 14831356629282569289861461)
            ·
              refine ⟨43451240124851277216391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14831356629282569289861461 43451240124851277216391)
              ·
                rfl

theorem cell21_1713575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 10].length) (baseStart_1713575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713575 prefixEnd_1713575 := by exact prefixLift 1713575
  have htrace : WordTrace (prefixWord ++ tailWord_1713575) baseStart_1713575 baseEnd_1713575 := by
    simpa [prefixWord, tailWord_1713575, baseEnd_1713575] using wordTrace_append hprefix tailTrace_1713575
  have hstable : (prefixWord ++ tailWord_1713575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713575).length < 2 ^ (prefixWord ++ tailWord_1713575).sum := by decide
  have hdescent : baseEnd_1713575 < baseStart_1713575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713637 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 6]
def baseStart_1713637 : Nat := 118140960795 + 1713637 * 2 ^ 59
def prefixEnd_1713637 : Nat := 4983230072969 + 3 ^ 40 * 1713637 * 2
def baseEnd_1713637 : Nat := 391075310368363164914059

theorem tailTrace_1713637 : CollatzResearch.WordTrace tailWord_1713637 prefixEnd_1713637 391075310368363164914059 := by
  unfold tailWord_1713637
  simp only [CollatzResearch.WordTrace]
  refine ⟨62501476092793289744387165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41667650728528859829591443 62501476092793289744387165)
  ·
    refine ⟨23438053534797483654145187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62501476092793289744387165 23438053534797483654145187)
    ·
      refine ⟨35157080302196225481217781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23438053534797483654145187 35157080302196225481217781)
      ·
        refine ⟨3295976278330896138864167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35157080302196225481217781 3295976278330896138864167)
        ·
          refine ⟨4943964417496344208296251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3295976278330896138864167 4943964417496344208296251)
          ·
            refine ⟨7415946626244516312444377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4943964417496344208296251 7415946626244516312444377)
            ·
              refine ⟨5561959969683387234333283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7415946626244516312444377 5561959969683387234333283)
              ·
                refine ⟨8342939954525080851499925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5561959969683387234333283 8342939954525080851499925)
                ·
                  refine ⟨391075310368363164914059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8342939954525080851499925 391075310368363164914059)
                  ·
                    rfl

theorem cell21_1713637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_1713637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713637 prefixEnd_1713637 := by exact prefixLift 1713637
  have htrace : WordTrace (prefixWord ++ tailWord_1713637) baseStart_1713637 baseEnd_1713637 := by
    simpa [prefixWord, tailWord_1713637, baseEnd_1713637] using wordTrace_append hprefix tailTrace_1713637
  have hstable : (prefixWord ++ tailWord_1713637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713637).length < 2 ^ (prefixWord ++ tailWord_1713637).sum := by decide
  have hdescent : baseEnd_1713637 < baseStart_1713637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713640 : List Nat := [2, 1, 4, 1, 1, 2, 5, 2, 3]
def baseStart_1713640 : Nat := 118140960795 + 1713640 * 2 ^ 59
def prefixEnd_1713640 : Nat := 4983230072969 + 3 ^ 40 * 1713640 * 2
def baseEnd_1713640 : Nat := 391075995009235826364053

theorem tailTrace_1713640 : CollatzResearch.WordTrace tailWord_1713640 prefixEnd_1713640 391075995009235826364053 := by
  unfold tailWord_1713640
  simp only [CollatzResearch.WordTrace]
  refine ⟨31250792755891210628373187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41667723674521614171164249 31250792755891210628373187)
  ·
    refine ⟨46876189133836815942559781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31250792755891210628373187 46876189133836815942559781)
    ·
      refine ⟨8789285462594402989229959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46876189133836815942559781 8789285462594402989229959)
      ·
        refine ⟨13183928193891604483844939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8789285462594402989229959 13183928193891604483844939)
        ·
          refine ⟨19775892290837406725767409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13183928193891604483844939 19775892290837406725767409)
          ·
            refine ⟨14831919218128055044325557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19775892290837406725767409 14831919218128055044325557)
            ·
              refine ⟨1390492426699505160405521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14831919218128055044325557 1390492426699505160405521)
              ·
                refine ⟨1042869320024628870304141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1390492426699505160405521 1042869320024628870304141)
                ·
                  refine ⟨391075995009235826364053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1042869320024628870304141 391075995009235826364053)
                  ·
                    rfl

theorem cell21_1713640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 3].length) (baseStart_1713640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713640 prefixEnd_1713640 := by exact prefixLift 1713640
  have htrace : WordTrace (prefixWord ++ tailWord_1713640) baseStart_1713640 baseEnd_1713640 := by
    simpa [prefixWord, tailWord_1713640, baseEnd_1713640] using wordTrace_append hprefix tailTrace_1713640
  have hstable : (prefixWord ++ tailWord_1713640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713640).length < 2 ^ (prefixWord ++ tailWord_1713640).sum := by decide
  have hdescent : baseEnd_1713640 < baseStart_1713640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713654 : List Nat := [5, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_1713654 : Nat := 118140960795 + 1713654 * 2 ^ 59
def prefixEnd_1713654 : Nat := 4983230072969 + 3 ^ 40 * 1713654 * 2
def baseEnd_1713654 : Nat := 391079189999974913130691

theorem tailTrace_1713654 : CollatzResearch.WordTrace tailWord_1713654 prefixEnd_1713654 391079189999974913130691 := by
  unfold tailWord_1713654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3906381008358231352984751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41668064089154467765170677 3906381008358231352984751)
  ·
    refine ⟨5859571512537347029477127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3906381008358231352984751 5859571512537347029477127)
    ·
      refine ⟨8789357268806020544215691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5859571512537347029477127 8789357268806020544215691)
      ·
        refine ⟨13184035903209030816323537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8789357268806020544215691 13184035903209030816323537)
        ·
          refine ⟨9888026927406773112242653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13184035903209030816323537 9888026927406773112242653)
          ·
            refine ⟨3708010097777539917090995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9888026927406773112242653 3708010097777539917090995)
            ·
              refine ⟨5562015146666309875636493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708010097777539917090995 5562015146666309875636493)
              ·
                refine ⟨2085755679999866203363685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5562015146666309875636493 2085755679999866203363685)
                ·
                  refine ⟨391079189999974913130691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2085755679999866203363685 391079189999974913130691)
                  ·
                    rfl

theorem cell21_1713654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_1713654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713654 prefixEnd_1713654 := by exact prefixLift 1713654
  have htrace : WordTrace (prefixWord ++ tailWord_1713654) baseStart_1713654 baseEnd_1713654 := by
    simpa [prefixWord, tailWord_1713654, baseEnd_1713654] using wordTrace_append hprefix tailTrace_1713654
  have hstable : (prefixWord ++ tailWord_1713654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713654).length < 2 ^ (prefixWord ++ tailWord_1713654).sum := by decide
  have hdescent : baseEnd_1713654 < baseStart_1713654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713817 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 5]
def baseStart_1713817 : Nat := 118140960795 + 1713817 * 2 ^ 59
def prefixEnd_1713817 : Nat := 4983230072969 + 3 ^ 40 * 1713817 * 2
def baseEnd_1713817 : Nat := 391116388820722851913691

theorem tailTrace_1713817 : CollatzResearch.WordTrace tailWord_1713817 prefixEnd_1713817 391116388820722851913691 := by
  unfold tailWord_1713817
  simp only [CollatzResearch.WordTrace]
  refine ⟨62508041232141180485939705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41672027488094120323959803 62508041232141180485939705)
  ·
    refine ⟨46881030924105885364454779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62508041232141180485939705 46881030924105885364454779)
    ·
      refine ⟨70321546386158828046682169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46881030924105885364454779 70321546386158828046682169)
      ·
        refine ⟨52741159789619121035011627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70321546386158828046682169 52741159789619121035011627)
        ·
          refine ⟨79111739684428681552517441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52741159789619121035011627 79111739684428681552517441)
          ·
            refine ⟨59333804763321511164388081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79111739684428681552517441 59333804763321511164388081)
            ·
              refine ⟨44500353572491133373291061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59333804763321511164388081 44500353572491133373291061)
              ·
                refine ⟨4171908147421043753746037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44500353572491133373291061 4171908147421043753746037)
                ·
                  refine ⟨391116388820722851913691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4171908147421043753746037 391116388820722851913691)
                  ·
                    rfl

theorem cell21_1713817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_1713817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713817 prefixEnd_1713817 := by exact prefixLift 1713817
  have htrace : WordTrace (prefixWord ++ tailWord_1713817) baseStart_1713817 baseEnd_1713817 := by
    simpa [prefixWord, tailWord_1713817, baseEnd_1713817] using wordTrace_append hprefix tailTrace_1713817
  have hstable : (prefixWord ++ tailWord_1713817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713817).length < 2 ^ (prefixWord ++ tailWord_1713817).sum := by decide
  have hdescent : baseEnd_1713817 < baseStart_1713817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713820 : List Nat := [2, 2, 3, 2, 3, 1, 2, 6]
def baseStart_1713820 : Nat := 118140960795 + 1713820 * 2 ^ 59
def prefixEnd_1713820 : Nat := 4983230072969 + 3 ^ 40 * 1713820 * 2
def baseEnd_1713820 : Nat := 130372357820531837787895

theorem tailTrace_1713820 : CollatzResearch.WordTrace tailWord_1713820 prefixEnd_1713820 130372357820531837787895 := by
  unfold tailWord_1713820
  simp only [CollatzResearch.WordTrace]
  refine ⟨31254075325565155999149457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41672100434086874665532609 31254075325565155999149457)
  ·
    refine ⟨23440556494173866999362093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31254075325565155999149457 23440556494173866999362093)
    ·
      refine ⟨8790208685315200124760785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23440556494173866999362093 8790208685315200124760785)
      ·
        refine ⟨6592656513986400093570589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8790208685315200124760785 6592656513986400093570589)
        ·
          refine ⟨2472246192744900035088971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6592656513986400093570589 2472246192744900035088971)
          ·
            refine ⟨3708369289117350052633457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472246192744900035088971 3708369289117350052633457)
            ·
              refine ⟨2781276966838012539475093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3708369289117350052633457 2781276966838012539475093)
              ·
                refine ⟨130372357820531837787895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2781276966838012539475093 130372357820531837787895)
                ·
                  rfl

theorem cell21_1713820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 6].length) (baseStart_1713820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713820 prefixEnd_1713820 := by exact prefixLift 1713820
  have htrace : WordTrace (prefixWord ++ tailWord_1713820) baseStart_1713820 baseEnd_1713820 := by
    simpa [prefixWord, tailWord_1713820, baseEnd_1713820] using wordTrace_append hprefix tailTrace_1713820
  have hstable : (prefixWord ++ tailWord_1713820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713820).length < 2 ^ (prefixWord ++ tailWord_1713820).sum := by decide
  have hdescent : baseEnd_1713820 < baseStart_1713820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713868 : List Nat := [2, 2, 1, 5, 2, 1, 1, 4, 3]
def baseStart_1713868 : Nat := 118140960795 + 1713868 * 2 ^ 59
def prefixEnd_1713868 : Nat := 4983230072969 + 3 ^ 40 * 1713868 * 2
def baseEnd_1713868 : Nat := 391128027715558096563587

theorem tailTrace_1713868 : CollatzResearch.WordTrace tailWord_1713868 prefixEnd_1713868 391128027715558096563587 := by
  unfold tailWord_1713868
  simp only [CollatzResearch.WordTrace]
  refine ⟨31254950677478208098023129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41673267569970944130697505 31254950677478208098023129)
  ·
    refine ⟨23441213008108656073517347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31254950677478208098023129 23441213008108656073517347)
    ·
      refine ⟨35161819512162984110276021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23441213008108656073517347 35161819512162984110276021)
      ·
        refine ⟨3296420579265279760338377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35161819512162984110276021 3296420579265279760338377)
        ·
          refine ⟨2472315434448959820253783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3296420579265279760338377 2472315434448959820253783)
          ·
            refine ⟨3708473151673439730380675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472315434448959820253783 3708473151673439730380675)
            ·
              refine ⟨5562709727510159595571013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708473151673439730380675 5562709727510159595571013)
              ·
                refine ⟨1043008073908154924169565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5562709727510159595571013 1043008073908154924169565)
                ·
                  refine ⟨391128027715558096563587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043008073908154924169565 391128027715558096563587)
                  ·
                    rfl

theorem cell21_1713868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_1713868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713868 prefixEnd_1713868 := by exact prefixLift 1713868
  have htrace : WordTrace (prefixWord ++ tailWord_1713868) baseStart_1713868 baseEnd_1713868 := by
    simpa [prefixWord, tailWord_1713868, baseEnd_1713868] using wordTrace_append hprefix tailTrace_1713868
  have hstable : (prefixWord ++ tailWord_1713868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713868).length < 2 ^ (prefixWord ++ tailWord_1713868).sum := by decide
  have hdescent : baseEnd_1713868 < baseStart_1713868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713896 : List Nat := [2, 1, 4, 1, 3, 2, 3, 5]
def baseStart_1713896 : Nat := 118140960795 + 1713896 * 2 ^ 59
def prefixEnd_1713896 : Nat := 4983230072969 + 3 ^ 40 * 1713896 * 2
def baseEnd_1713896 : Nat := 130378139232345423365621

theorem tailTrace_1713896 : CollatzResearch.WordTrace tailWord_1713896 prefixEnd_1713896 130378139232345423365621 := by
  unfold tailWord_1713896
  simp only [CollatzResearch.WordTrace]
  refine ⟨31255461299427488489032771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41673948399236651318710361 31255461299427488489032771)
  ·
    refine ⟨46883191949141232733549157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31255461299427488489032771 46883191949141232733549157)
    ·
      refine ⟨8790598490463981137540467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46883191949141232733549157 8790598490463981137540467)
      ·
        refine ⟨13185897735695971706310701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8790598490463981137540467 13185897735695971706310701)
        ·
          refine ⟨4944711650885989389866513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13185897735695971706310701 4944711650885989389866513)
          ·
            refine ⟨3708533738164492042399885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4944711650885989389866513 3708533738164492042399885)
            ·
              refine ⟨1390700151811684515899957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3708533738164492042399885 1390700151811684515899957)
              ·
                refine ⟨130378139232345423365621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1390700151811684515899957 130378139232345423365621)
                ·
                  rfl

theorem cell21_1713896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 5].length) (baseStart_1713896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713896 prefixEnd_1713896 := by exact prefixLift 1713896
  have htrace : WordTrace (prefixWord ++ tailWord_1713896) baseStart_1713896 baseEnd_1713896 := by
    simpa [prefixWord, tailWord_1713896, baseEnd_1713896] using wordTrace_append hprefix tailTrace_1713896
  have hstable : (prefixWord ++ tailWord_1713896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713896).length < 2 ^ (prefixWord ++ tailWord_1713896).sum := by decide
  have hdescent : baseEnd_1713896 < baseStart_1713896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713927 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 5]
def baseStart_1713927 : Nat := 118140960795 + 1713927 * 2 ^ 59
def prefixEnd_1713927 : Nat := 4983230072969 + 3 ^ 40 * 1713927 * 2
def baseEnd_1713927 : Nat := 391141492319387105080133

theorem tailTrace_1713927 : CollatzResearch.WordTrace tailWord_1713927 prefixEnd_1713927 391141492319387105080133 := by
  unfold tailWord_1713927
  simp only [CollatzResearch.WordTrace]
  refine ⟨62512053261742669272444035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41674702174495112848296023 62512053261742669272444035)
  ·
    refine ⟨93768079892614003908666053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62512053261742669272444035 93768079892614003908666053)
    ·
      refine ⟨17581514979865125732874885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93768079892614003908666053 17581514979865125732874885)
      ·
        refine ⟨3296534058724711074914041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17581514979865125732874885 3296534058724711074914041)
        ·
          refine ⟨2472400544043533306185531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3296534058724711074914041 2472400544043533306185531)
          ·
            refine ⟨3708600816065299959278297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472400544043533306185531 3708600816065299959278297)
            ·
              refine ⟨2781450612048974969458723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3708600816065299959278297 2781450612048974969458723)
              ·
                refine ⟨4172175918073462454188085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2781450612048974969458723 4172175918073462454188085)
                ·
                  refine ⟨391141492319387105080133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4172175918073462454188085 391141492319387105080133)
                  ·
                    rfl

theorem cell21_1713927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 5].length) (baseStart_1713927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713927 prefixEnd_1713927 := by exact prefixLift 1713927
  have htrace : WordTrace (prefixWord ++ tailWord_1713927) baseStart_1713927 baseEnd_1713927 := by
    simpa [prefixWord, tailWord_1713927, baseEnd_1713927] using wordTrace_append hprefix tailTrace_1713927
  have hstable : (prefixWord ++ tailWord_1713927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713927).length < 2 ^ (prefixWord ++ tailWord_1713927).sum := by decide
  have hdescent : baseEnd_1713927 < baseStart_1713927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713955 : List Nat := [1, 1, 1, 4, 2, 1, 6, 5]
def baseStart_1713955 : Nat := 118140960795 + 1713955 * 2 ^ 59
def prefixEnd_1713955 : Nat := 4983230072969 + 3 ^ 40 * 1713955 * 2
def baseEnd_1713955 : Nat := 130382627433621759537803

theorem tailTrace_1713955 : CollatzResearch.WordTrace tailWord_1713955 prefixEnd_1713955 130382627433621759537803 := by
  unfold tailWord_1713955
  simp only [CollatzResearch.WordTrace]
  refine ⟨62513074505641230054463319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41675383003760820036308879 62513074505641230054463319)
  ·
    refine ⟨93769611758461845081694979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62513074505641230054463319 93769611758461845081694979)
    ·
      refine ⟨140654417637692767622542469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93769611758461845081694979 140654417637692767622542469)
      ·
        refine ⟨26372703307067393929226713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140654417637692767622542469 26372703307067393929226713)
        ·
          refine ⟨19779527480300545446920035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26372703307067393929226713 19779527480300545446920035)
          ·
            refine ⟨29669291220450818170380053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19779527480300545446920035 29669291220450818170380053)
            ·
              refine ⟨1390748025958632101736565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29669291220450818170380053 1390748025958632101736565)
              ·
                refine ⟨130382627433621759537803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1390748025958632101736565 130382627433621759537803)
                ·
                  rfl

theorem cell21_1713955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 5].length) (baseStart_1713955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713955 prefixEnd_1713955 := by exact prefixLift 1713955
  have htrace : WordTrace (prefixWord ++ tailWord_1713955) baseStart_1713955 baseEnd_1713955 := by
    simpa [prefixWord, tailWord_1713955, baseEnd_1713955] using wordTrace_append hprefix tailTrace_1713955
  have hstable : (prefixWord ++ tailWord_1713955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713955).length < 2 ^ (prefixWord ++ tailWord_1713955).sum := by decide
  have hdescent : baseEnd_1713955 < baseStart_1713955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713972 : List Nat := [2, 5, 1, 1, 2, 3, 7]
def baseStart_1713972 : Nat := 118140960795 + 1713972 * 2 ^ 59
def prefixEnd_1713972 : Nat := 4983230072969 + 3 ^ 40 * 1713972 * 2
def baseEnd_1713972 : Nat := 43461306881386336314449

theorem tailTrace_1713972 : CollatzResearch.WordTrace tailWord_1713972 prefixEnd_1713972 43461306881386336314449 := by
  unfold tailWord_1713972
  simp only [CollatzResearch.WordTrace]
  refine ⟨31256847273289820978916085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41675796364386427971888113 31256847273289820978916085)
  ·
    refine ⟨2930329431870920716773383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31256847273289820978916085 2930329431870920716773383)
    ·
      refine ⟨4395494147806381075160075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2930329431870920716773383 4395494147806381075160075)
      ·
        refine ⟨6593241221709571612740113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4395494147806381075160075 6593241221709571612740113)
        ·
          refine ⟨4944930916282178709555085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6593241221709571612740113 4944930916282178709555085)
          ·
            refine ⟨1854349093605817016083157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4944930916282178709555085 1854349093605817016083157)
            ·
              refine ⟨43461306881386336314449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1854349093605817016083157 43461306881386336314449)
              ·
                rfl

theorem cell21_1713972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 7].length) (baseStart_1713972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1713972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1713972 prefixEnd_1713972 := by exact prefixLift 1713972
  have htrace : WordTrace (prefixWord ++ tailWord_1713972) baseStart_1713972 baseEnd_1713972 := by
    simpa [prefixWord, tailWord_1713972, baseEnd_1713972] using wordTrace_append hprefix tailTrace_1713972
  have hstable : (prefixWord ++ tailWord_1713972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713972).length < 2 ^ (prefixWord ++ tailWord_1713972).sum := by decide
  have hdescent : baseEnd_1713972 < baseStart_1713972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714045 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 5]
def baseStart_1714045 : Nat := 118140960795 + 1714045 * 2 ^ 59
def prefixEnd_1714045 : Nat := 4983230072969 + 3 ^ 40 * 1714045 * 2
def baseEnd_1714045 : Nat := 391168421527045122113225

theorem tailTrace_1714045 : CollatzResearch.WordTrace tailWord_1714045 prefixEnd_1714045 391168421527045122113225 := by
  unfold tailWord_1714045
  simp only [CollatzResearch.WordTrace]
  refine ⟨62516357075315175425239589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41677571383543450283493059 62516357075315175425239589)
  ·
    refine ⟨11721816951621595392232423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62516357075315175425239589 11721816951621595392232423)
    ·
      refine ⟨17582725427432393088348635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11721816951621595392232423 17582725427432393088348635)
      ·
        refine ⟨26374088141148589632522953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17582725427432393088348635 26374088141148589632522953)
        ·
          refine ⟨19780566105861442224392215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26374088141148589632522953 19780566105861442224392215)
          ·
            refine ⟨29670849158792163336588323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19780566105861442224392215 29670849158792163336588323)
            ·
              refine ⟨44506273738188245004882485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29670849158792163336588323 44506273738188245004882485)
              ·
                refine ⟨4172463162955147969207733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44506273738188245004882485 4172463162955147969207733)
                ·
                  refine ⟨391168421527045122113225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4172463162955147969207733 391168421527045122113225)
                  ·
                    rfl

theorem cell21_1714045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_1714045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714045 prefixEnd_1714045 := by exact prefixLift 1714045
  have htrace : WordTrace (prefixWord ++ tailWord_1714045) baseStart_1714045 baseEnd_1714045 := by
    simpa [prefixWord, tailWord_1714045, baseEnd_1714045] using wordTrace_append hprefix tailTrace_1714045
  have hstable : (prefixWord ++ tailWord_1714045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714045).length < 2 ^ (prefixWord ++ tailWord_1714045).sum := by decide
  have hdescent : baseEnd_1714045 < baseStart_1714045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714059 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 8]
def baseStart_1714059 : Nat := 118140960795 + 1714059 * 2 ^ 59
def prefixEnd_1714059 : Nat := 4983230072969 + 3 ^ 40 * 1714059 * 2
def baseEnd_1714059 : Nat := 391171616517784208879863

theorem tailTrace_1714059 : CollatzResearch.WordTrace tailWord_1714059 prefixEnd_1714059 391171616517784208879863 := by
  unfold tailWord_1714059
  simp only [CollatzResearch.WordTrace]
  refine ⟨62516867697264455816249231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41677911798176303877499487 62516867697264455816249231)
  ·
    refine ⟨93775301545896683724373847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62516867697264455816249231 93775301545896683724373847)
    ·
      refine ⟨140662952318845025586560771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93775301545896683724373847 140662952318845025586560771)
      ·
        refine ⟨210994428478267538379841157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140662952318845025586560771 210994428478267538379841157)
        ·
          refine ⟨39561455339675163446220217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210994428478267538379841157 39561455339675163446220217)
          ·
            refine ⟨29671091504756372584665163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39561455339675163446220217 29671091504756372584665163)
            ·
              refine ⟨44506637257134558876997745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29671091504756372584665163 44506637257134558876997745)
              ·
                refine ⟨33379977942850919157748309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44506637257134558876997745 33379977942850919157748309)
                ·
                  refine ⟨391171616517784208879863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33379977942850919157748309 391171616517784208879863)
                  ·
                    rfl

theorem cell21_1714059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 8].length) (baseStart_1714059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714059 prefixEnd_1714059 := by exact prefixLift 1714059
  have htrace : WordTrace (prefixWord ++ tailWord_1714059) baseStart_1714059 baseEnd_1714059 := by
    simpa [prefixWord, tailWord_1714059, baseEnd_1714059] using wordTrace_append hprefix tailTrace_1714059
  have hstable : (prefixWord ++ tailWord_1714059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714059).length < 2 ^ (prefixWord ++ tailWord_1714059).sum := by decide
  have hdescent : baseEnd_1714059 < baseStart_1714059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714110 : List Nat := [4, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_1714110 : Nat := 118140960795 + 1714110 * 2 ^ 59
def prefixEnd_1714110 : Nat := 4983230072969 + 3 ^ 40 * 1714110 * 2
def baseEnd_1714110 : Nat := 391183255412619453529759

theorem tailTrace_1714110 : CollatzResearch.WordTrace tailWord_1714110 prefixEnd_1714110 391183255412619453529759 := by
  unfold tailWord_1714110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7814840977509961440794473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41679151880053127684237189 7814840977509961440794473)
  ·
    refine ⟨5861130733132471080595855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7814840977509961440794473 5861130733132471080595855)
    ·
      refine ⟨8791696099698706620893783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5861130733132471080595855 8791696099698706620893783)
      ·
        refine ⟨13187544149548059931340675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8791696099698706620893783 13187544149548059931340675)
        ·
          refine ⟨19781316224322089897011013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13187544149548059931340675 19781316224322089897011013)
          ·
            refine ⟨3708996792060391855689565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19781316224322089897011013 3708996792060391855689565)
            ·
              refine ⟨1390873797022646945883587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3708996792060391855689565 1390873797022646945883587)
              ·
                refine ⟨2086310695533970418825381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1390873797022646945883587 2086310695533970418825381)
                ·
                  refine ⟨391183255412619453529759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2086310695533970418825381 391183255412619453529759)
                  ·
                    rfl

theorem cell21_1714110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_1714110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714110 prefixEnd_1714110 := by exact prefixLift 1714110
  have htrace : WordTrace (prefixWord ++ tailWord_1714110) baseStart_1714110 baseEnd_1714110 := by
    simpa [prefixWord, tailWord_1714110, baseEnd_1714110] using wordTrace_append hprefix tailTrace_1714110
  have hstable : (prefixWord ++ tailWord_1714110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714110).length < 2 ^ (prefixWord ++ tailWord_1714110).sum := by decide
  have hdescent : baseEnd_1714110 < baseStart_1714110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714124 : List Nat := [2, 2, 1, 4, 1, 4, 2, 5]
def baseStart_1714124 : Nat := 118140960795 + 1714124 * 2 ^ 59
def prefixEnd_1714124 : Nat := 4983230072969 + 3 ^ 40 * 1714124 * 2
def baseEnd_1714124 : Nat := 130395483467786180098799

theorem tailTrace_1714124 : CollatzResearch.WordTrace tailWord_1714124 prefixEnd_1714124 130395483467786180098799 := by
  unfold tailWord_1714124
  simp only [CollatzResearch.WordTrace]
  refine ⟨31259619221014485958682713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41679492294685981278243617 31259619221014485958682713)
  ·
    refine ⟨23444714415760864469012035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31259619221014485958682713 23444714415760864469012035)
    ·
      refine ⟨35167071623641296703518053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23444714415760864469012035 35167071623641296703518053)
      ·
        refine ⟨6593825929432743131909635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35167071623641296703518053 6593825929432743131909635)
        ·
          refine ⟨9890738894149114697864453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6593825929432743131909635 9890738894149114697864453)
          ·
            refine ⟨1854513542652959005849585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9890738894149114697864453 1854513542652959005849585)
            ·
              refine ⟨1390885156989719254387189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1854513542652959005849585 1390885156989719254387189)
              ·
                refine ⟨130395483467786180098799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1390885156989719254387189 130395483467786180098799)
                ·
                  rfl

theorem cell21_1714124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 5].length) (baseStart_1714124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714124 prefixEnd_1714124 := by exact prefixLift 1714124
  have htrace : WordTrace (prefixWord ++ tailWord_1714124) baseStart_1714124 baseEnd_1714124 := by
    simpa [prefixWord, tailWord_1714124, baseEnd_1714124] using wordTrace_append hprefix tailTrace_1714124
  have hstable : (prefixWord ++ tailWord_1714124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714124).length < 2 ^ (prefixWord ++ tailWord_1714124).sum := by decide
  have hdescent : baseEnd_1714124 < baseStart_1714124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714135 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 8]
def baseStart_1714135 : Nat := 118140960795 + 1714135 * 2 ^ 59
def prefixEnd_1714135 : Nat := 4983230072969 + 3 ^ 40 * 1714135 * 2
def baseEnd_1714135 : Nat := 391188960753224965613041

theorem tailTrace_1714135 : CollatzResearch.WordTrace tailWord_1714135 prefixEnd_1714135 391188960753224965613041 := by
  unfold tailWord_1714135
  simp only [CollatzResearch.WordTrace]
  refine ⟨62519639644989120796015859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41679759763326080530677239 62519639644989120796015859)
  ·
    refine ⟨93779459467483681194023789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62519639644989120796015859 93779459467483681194023789)
    ·
      refine ⟨35167297300306380447758921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93779459467483681194023789 35167297300306380447758921)
      ·
        refine ⟨26375472975229785335819191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35167297300306380447758921 26375472975229785335819191)
        ·
          refine ⟨39563209462844678003728787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26375472975229785335819191 39563209462844678003728787)
          ·
            refine ⟨59344814194267017005593181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39563209462844678003728787 59344814194267017005593181)
            ·
              refine ⟨22254305322850131377097443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59344814194267017005593181 22254305322850131377097443)
              ·
                refine ⟨33381457984275197065646165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22254305322850131377097443 33381457984275197065646165)
                ·
                  refine ⟨391188960753224965613041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33381457984275197065646165 391188960753224965613041)
                  ·
                    rfl

theorem cell21_1714135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 8].length) (baseStart_1714135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714135 prefixEnd_1714135 := by exact prefixLift 1714135
  have htrace : WordTrace (prefixWord ++ tailWord_1714135) baseStart_1714135 baseEnd_1714135 := by
    simpa [prefixWord, tailWord_1714135, baseEnd_1714135] using wordTrace_append hprefix tailTrace_1714135
  have hstable : (prefixWord ++ tailWord_1714135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714135).length < 2 ^ (prefixWord ++ tailWord_1714135).sum := by decide
  have hdescent : baseEnd_1714135 < baseStart_1714135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714152 : List Nat := [2, 1, 4, 1, 1, 1, 1, 6, 4]
def baseStart_1714152 : Nat := 118140960795 + 1714152 * 2 ^ 59
def prefixEnd_1714152 : Nat := 4983230072969 + 3 ^ 40 * 1714152 * 2
def baseEnd_1714152 : Nat := 391192840384836713829673

theorem tailTrace_1714152 : CollatzResearch.WordTrace tailWord_1714152 prefixEnd_1714152 391192840384836713829673 := by
  unfold tailWord_1714152
  simp only [CollatzResearch.WordTrace]
  refine ⟨31260129842963766349692355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41680173123951688466256473 31260129842963766349692355)
  ·
    refine ⟨46890194764445649524538533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31260129842963766349692355 46890194764445649524538533)
    ·
      refine ⟨8791911518333559285850975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46890194764445649524538533 8791911518333559285850975)
      ·
        refine ⟨13187867277500338928776463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8791911518333559285850975 13187867277500338928776463)
        ·
          refine ⟨19781800916250508393164695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13187867277500338928776463 19781800916250508393164695)
          ·
            refine ⟨29672701374375762589747043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19781800916250508393164695 29672701374375762589747043)
            ·
              refine ⟨44509052061563643884620565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29672701374375762589747043 44509052061563643884620565)
              ·
                refine ⟨2086361815385795807091589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44509052061563643884620565 2086361815385795807091589)
                ·
                  refine ⟨391192840384836713829673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2086361815385795807091589 391192840384836713829673)
                  ·
                    rfl

theorem cell21_1714152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_1714152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714152 prefixEnd_1714152 := by exact prefixLift 1714152
  have htrace : WordTrace (prefixWord ++ tailWord_1714152) baseStart_1714152 baseEnd_1714152 := by
    simpa [prefixWord, tailWord_1714152, baseEnd_1714152] using wordTrace_append hprefix tailTrace_1714152
  have hstable : (prefixWord ++ tailWord_1714152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714152).length < 2 ^ (prefixWord ++ tailWord_1714152).sum := by decide
  have hdescent : baseEnd_1714152 < baseStart_1714152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714169 : List Nat := [1, 2, 1, 3, 1, 4, 4, 1, 4]
def baseStart_1714169 : Nat := 118140960795 + 1714169 * 2 ^ 59
def prefixEnd_1714169 : Nat := 4983230072969 + 3 ^ 40 * 1714169 * 2
def baseEnd_1714169 : Nat := 391196720016448462046305

theorem tailTrace_1714169 : CollatzResearch.WordTrace tailWord_1714169 prefixEnd_1714169 391196720016448462046305 := by
  unfold tailWord_1714169
  simp only [CollatzResearch.WordTrace]
  refine ⟨62520879726865944602753561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41680586484577296401835707 62520879726865944602753561)
  ·
    refine ⟨46890659795149458452065171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62520879726865944602753561 46890659795149458452065171)
    ·
      refine ⟨70335989692724187678097757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46890659795149458452065171 70335989692724187678097757)
      ·
        refine ⟨26375996134771570379286659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70335989692724187678097757 26375996134771570379286659)
        ·
          refine ⟨39563994202157355568929989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26375996134771570379286659 39563994202157355568929989)
          ·
            refine ⟨7418248912904504169174373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39563994202157355568929989 7418248912904504169174373)
            ·
              refine ⟨1390921671169594531720195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7418248912904504169174373 1390921671169594531720195)
              ·
                refine ⟨2086382506754391797580293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1390921671169594531720195 2086382506754391797580293)
                ·
                  refine ⟨391196720016448462046305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2086382506754391797580293 391196720016448462046305)
                  ·
                    rfl

theorem cell21_1714169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 4].length) (baseStart_1714169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714169 prefixEnd_1714169 := by exact prefixLift 1714169
  have htrace : WordTrace (prefixWord ++ tailWord_1714169) baseStart_1714169 baseEnd_1714169 := by
    simpa [prefixWord, tailWord_1714169, baseEnd_1714169] using wordTrace_append hprefix tailTrace_1714169
  have hstable : (prefixWord ++ tailWord_1714169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714169).length < 2 ^ (prefixWord ++ tailWord_1714169).sum := by decide
  have hdescent : baseEnd_1714169 < baseStart_1714169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714262 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1714262 : Nat := 118140960795 + 1714262 * 2 ^ 59
def prefixEnd_1714262 : Nat := 4983230072969 + 3 ^ 40 * 1714262 * 2
def baseEnd_1714262 : Nat := 391217943883500966996115

theorem tailTrace_1714262 : CollatzResearch.WordTrace tailWord_1714262 prefixEnd_1714262 391217943883500966996115 := by
  unfold tailWord_1714262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3907766982220563842868065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41682847810352680990592693 3907766982220563842868065)
  ·
    refine ⟨2930825236665422882151049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3907766982220563842868065 2930825236665422882151049)
    ·
      refine ⟨2198118927499067161613287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2930825236665422882151049 2198118927499067161613287)
      ·
        refine ⟨3297178391248600742419931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2198118927499067161613287 3297178391248600742419931)
        ·
          refine ⟨4945767586872901113629897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3297178391248600742419931 4945767586872901113629897)
          ·
            refine ⟨3709325690154675835222423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4945767586872901113629897 3709325690154675835222423)
            ·
              refine ⟨5563988535232013752833635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3709325690154675835222423 5563988535232013752833635)
              ·
                refine ⟨8345982802848020629250453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5563988535232013752833635 8345982802848020629250453)
                ·
                  refine ⟨391217943883500966996115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8345982802848020629250453 391217943883500966996115)
                  ·
                    rfl

theorem cell21_1714262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1714262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714262 prefixEnd_1714262 := by exact prefixLift 1714262
  have htrace : WordTrace (prefixWord ++ tailWord_1714262) baseStart_1714262 baseEnd_1714262 := by
    simpa [prefixWord, tailWord_1714262, baseEnd_1714262] using wordTrace_append hprefix tailTrace_1714262
  have hstable : (prefixWord ++ tailWord_1714262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714262).length < 2 ^ (prefixWord ++ tailWord_1714262).sum := by decide
  have hdescent : baseEnd_1714262 < baseStart_1714262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714307 : List Nat := [1, 1, 1, 3, 3, 5, 1, 3, 3]
def baseStart_1714307 : Nat := 118140960795 + 1714307 * 2 ^ 59
def prefixEnd_1714307 : Nat := 4983230072969 + 3 ^ 40 * 1714307 * 2
def baseEnd_1714307 : Nat := 391228213496590888746023

theorem tailTrace_1714307 : CollatzResearch.WordTrace tailWord_1714307 prefixEnd_1714307 391228213496590888746023 := by
  unfold tailWord_1714307
  simp only [CollatzResearch.WordTrace]
  refine ⟨62525913000365994171277175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41683942000243996114184783 62525913000365994171277175)
  ·
    refine ⟨93788869500548991256915763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62525913000365994171277175 93788869500548991256915763)
    ·
      refine ⟨140683304250823486885373645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93788869500548991256915763 140683304250823486885373645)
      ·
        refine ⟨52756239094058807582015117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140683304250823486885373645 52756239094058807582015117)
        ·
          refine ⟨19783589660272052843255669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52756239094058807582015117 19783589660272052843255669)
          ·
            refine ⟨1854711530650504954055219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19783589660272052843255669 1854711530650504954055219)
            ·
              refine ⟨2782067295975757431082829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854711530650504954055219 2782067295975757431082829)
              ·
                refine ⟨1043275235990909036656061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2782067295975757431082829 1043275235990909036656061)
                ·
                  refine ⟨391228213496590888746023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043275235990909036656061 391228213496590888746023)
                  ·
                    rfl

theorem cell21_1714307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 3].length) (baseStart_1714307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714307 prefixEnd_1714307 := by exact prefixLift 1714307
  have htrace : WordTrace (prefixWord ++ tailWord_1714307) baseStart_1714307 baseEnd_1714307 := by
    simpa [prefixWord, tailWord_1714307, baseEnd_1714307] using wordTrace_append hprefix tailTrace_1714307
  have hstable : (prefixWord ++ tailWord_1714307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714307).length < 2 ^ (prefixWord ++ tailWord_1714307).sum := by decide
  have hdescent : baseEnd_1714307 < baseStart_1714307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714324 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 5]
def baseStart_1714324 : Nat := 118140960795 + 1714324 * 2 ^ 59
def prefixEnd_1714324 : Nat := 4983230072969 + 3 ^ 40 * 1714324 * 2
def baseEnd_1714324 : Nat := 391232093128202636962655

theorem tailTrace_1714324 : CollatzResearch.WordTrace tailWord_1714324 prefixEnd_1714324 391232093128202636962655 := by
  unfold tailWord_1714324
  simp only [CollatzResearch.WordTrace]
  refine ⟨31263266520652203037323013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41684355360869604049764017 31263266520652203037323013)
  ·
    refine ⟨5861862472622288069498065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31263266520652203037323013 5861862472622288069498065)
    ·
      refine ⟨4396396854466716052123549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5861862472622288069498065 4396396854466716052123549)
      ·
        refine ⟨1648648820425018519546331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4396396854466716052123549 1648648820425018519546331)
        ·
          refine ⟨2472973230637527779319497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648648820425018519546331 2472973230637527779319497)
          ·
            refine ⟨1854729922978145834489623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2472973230637527779319497 1854729922978145834489623)
            ·
              refine ⟨2782094884467218751734435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854729922978145834489623 2782094884467218751734435)
              ·
                refine ⟨4173142326700828127601653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2782094884467218751734435 4173142326700828127601653)
                ·
                  refine ⟨391232093128202636962655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4173142326700828127601653 391232093128202636962655)
                  ·
                    rfl

theorem cell21_1714324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_1714324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714324 prefixEnd_1714324 := by exact prefixLift 1714324
  have htrace : WordTrace (prefixWord ++ tailWord_1714324) baseStart_1714324 baseEnd_1714324 := by
    simpa [prefixWord, tailWord_1714324, baseEnd_1714324] using wordTrace_append hprefix tailTrace_1714324
  have hstable : (prefixWord ++ tailWord_1714324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714324).length < 2 ^ (prefixWord ++ tailWord_1714324).sum := by decide
  have hdescent : baseEnd_1714324 < baseStart_1714324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714335 : List Nat := [1, 1, 2, 6, 1, 2, 2, 6]
def baseStart_1714335 : Nat := 118140960795 + 1714335 * 2 ^ 59
def prefixEnd_1714335 : Nat := 4983230072969 + 3 ^ 40 * 1714335 * 2
def baseEnd_1714335 : Nat := 130411534492689687426433

theorem tailTrace_1714335 : CollatzResearch.WordTrace tailWord_1714335 prefixEnd_1714335 130411534492689687426433 := by
  unfold tailWord_1714335
  simp only [CollatzResearch.WordTrace]
  refine ⟨62526934244264554953296459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41684622829509703302197639 62526934244264554953296459)
  ·
    refine ⟨93790401366396832429944689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62526934244264554953296459 93790401366396832429944689)
    ·
      refine ⟨70342801024797624322458517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93790401366396832429944689 70342801024797624322458517)
      ·
        refine ⟨3297318798037388640115243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70342801024797624322458517 3297318798037388640115243)
        ·
          refine ⟨4945978197056082960172865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3297318798037388640115243 4945978197056082960172865)
          ·
            refine ⟨3709483647792062220129649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4945978197056082960172865 3709483647792062220129649)
            ·
              refine ⟨2782112735844046665097237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3709483647792062220129649 2782112735844046665097237)
              ·
                refine ⟨130411534492689687426433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2782112735844046665097237 130411534492689687426433)
                ·
                  rfl

theorem cell21_1714335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 6].length) (baseStart_1714335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714335 prefixEnd_1714335 := by exact prefixLift 1714335
  have htrace : WordTrace (prefixWord ++ tailWord_1714335) baseStart_1714335 baseEnd_1714335 := by
    simpa [prefixWord, tailWord_1714335, baseEnd_1714335] using wordTrace_append hprefix tailTrace_1714335
  have hstable : (prefixWord ++ tailWord_1714335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714335).length < 2 ^ (prefixWord ++ tailWord_1714335).sum := by decide
  have hdescent : baseEnd_1714335 < baseStart_1714335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714338 : List Nat := [3, 3, 1, 3, 1, 1, 4, 1, 4]
def baseStart_1714338 : Nat := 118140960795 + 1714338 * 2 ^ 59
def prefixEnd_1714338 : Nat := 4983230072969 + 3 ^ 40 * 1714338 * 2
def baseEnd_1714338 : Nat := 391235288118941723729293

theorem tailTrace_1714338 : CollatzResearch.WordTrace tailWord_1714338 prefixEnd_1714338 391235288118941723729293 := by
  unfold tailWord_1714338
  simp only [CollatzResearch.WordTrace]
  refine ⟨15631760915813421616413917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41684695775502457643770445 15631760915813421616413917)
  ·
    refine ⟨5861910343430033106155219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15631760915813421616413917 5861910343430033106155219)
    ·
      refine ⟨8792865515145049659232829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5861910343430033106155219 8792865515145049659232829)
      ·
        refine ⟨3297324568179393622212311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8792865515145049659232829 3297324568179393622212311)
        ·
          refine ⟨4945986852269090433318467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3297324568179393622212311 4945986852269090433318467)
          ·
            refine ⟨7418980278403635649977701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4945986852269090433318467 7418980278403635649977701)
            ·
              refine ⟨1391058802200681684370819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7418980278403635649977701 1391058802200681684370819)
              ·
                refine ⟨2086588203301022526556229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391058802200681684370819 2086588203301022526556229)
                ·
                  refine ⟨391235288118941723729293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2086588203301022526556229 391235288118941723729293)
                  ·
                    rfl

theorem cell21_1714338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_1714338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714338 prefixEnd_1714338 := by exact prefixLift 1714338
  have htrace : WordTrace (prefixWord ++ tailWord_1714338) baseStart_1714338 baseEnd_1714338 := by
    simpa [prefixWord, tailWord_1714338, baseEnd_1714338] using wordTrace_append hprefix tailTrace_1714338
  have hstable : (prefixWord ++ tailWord_1714338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714338).length < 2 ^ (prefixWord ++ tailWord_1714338).sum := by decide
  have hdescent : baseEnd_1714338 < baseStart_1714338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714394 : List Nat := [3, 1, 1, 2, 2, 1, 5, 6]
def baseStart_1714394 : Nat := 118140960795 + 1714394 * 2 ^ 59
def prefixEnd_1714394 : Nat := 4983230072969 + 3 ^ 40 * 1714394 * 2
def baseEnd_1714394 : Nat := 130416022693966023598615

theorem tailTrace_1714394 : CollatzResearch.WordTrace tailWord_1714394 prefixEnd_1714394 130416022693966023598615 := by
  unfold tailWord_1714394
  simp only [CollatzResearch.WordTrace]
  refine ⟨15632271537762702007423559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41686057434033872019796157 15632271537762702007423559)
  ·
    refine ⟨23448407306644053011135339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15632271537762702007423559 23448407306644053011135339)
    ·
      refine ⟨35172610959966079516703009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23448407306644053011135339 35172610959966079516703009)
      ·
        refine ⟨26379458219974559637527257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35172610959966079516703009 26379458219974559637527257)
        ·
          refine ⟨19784593664980919728145443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26379458219974559637527257 19784593664980919728145443)
          ·
            refine ⟨29676890497471379592218165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19784593664980919728145443 29676890497471379592218165)
            ·
              refine ⟨2782208484137941836770453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29676890497471379592218165 2782208484137941836770453)
              ·
                refine ⟨130416022693966023598615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2782208484137941836770453 130416022693966023598615)
                ·
                  rfl

theorem cell21_1714394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_1714394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714394 prefixEnd_1714394 := by exact prefixLift 1714394
  have htrace : WordTrace (prefixWord ++ tailWord_1714394) baseStart_1714394 baseEnd_1714394 := by
    simpa [prefixWord, tailWord_1714394, baseEnd_1714394] using wordTrace_append hprefix tailTrace_1714394
  have hstable : (prefixWord ++ tailWord_1714394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714394).length < 2 ^ (prefixWord ++ tailWord_1714394).sum := by decide
  have hdescent : baseEnd_1714394 < baseStart_1714394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714397 : List Nat := [1, 4, 3, 2, 1, 1, 2, 3, 4]
def baseStart_1714397 : Nat := 118140960795 + 1714397 * 2 ^ 59
def prefixEnd_1714397 : Nat := 4983230072969 + 3 ^ 40 * 1714397 * 2
def baseEnd_1714397 : Nat := 391248752722770732245839

theorem tailTrace_1714397 : CollatzResearch.WordTrace tailWord_1714397 prefixEnd_1714397 391248752722770732245839 := by
  unfold tailWord_1714397
  simp only [CollatzResearch.WordTrace]
  refine ⟨62529195570039939542053445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41686130380026626361368963 62529195570039939542053445)
  ·
    refine ⟨11724224169382488664135021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62529195570039939542053445 11724224169382488664135021)
    ·
      refine ⟨4396584063518433249050633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11724224169382488664135021 4396584063518433249050633)
      ·
        refine ⟨3297438047638824936787975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4396584063518433249050633 3297438047638824936787975)
        ·
          refine ⟨4946157071458237405181963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3297438047638824936787975 4946157071458237405181963)
          ·
            refine ⟨7419235607187356107772945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4946157071458237405181963 7419235607187356107772945)
            ·
              refine ⟨5564426705390517080829709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7419235607187356107772945 5564426705390517080829709)
              ·
                refine ⟨2086660014521443905311141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5564426705390517080829709 2086660014521443905311141)
                ·
                  refine ⟨391248752722770732245839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2086660014521443905311141 391248752722770732245839)
                  ·
                    rfl

theorem cell21_1714397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_1714397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714397 prefixEnd_1714397 := by exact prefixLift 1714397
  have htrace : WordTrace (prefixWord ++ tailWord_1714397) baseStart_1714397 baseEnd_1714397 := by
    simpa [prefixWord, tailWord_1714397, baseEnd_1714397] using wordTrace_append hprefix tailTrace_1714397
  have hstable : (prefixWord ++ tailWord_1714397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714397).length < 2 ^ (prefixWord ++ tailWord_1714397).sum := by decide
  have hdescent : baseEnd_1714397 < baseStart_1714397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714442 : List Nat := [3, 1, 2, 2, 1, 1, 4, 4, 3]
def baseStart_1714442 : Nat := 118140960795 + 1714442 * 2 ^ 59
def prefixEnd_1714442 : Nat := 4983230072969 + 3 ^ 40 * 1714442 * 2
def baseEnd_1714442 : Nat := 391259022335860653995747

theorem tailTrace_1714442 : CollatzResearch.WordTrace tailWord_1714442 prefixEnd_1714442 391259022335860653995747 := by
  unfold tailWord_1714442
  simp only [CollatzResearch.WordTrace]
  refine ⟨15632709213719228056860395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41687224569917941484961053 15632709213719228056860395)
  ·
    refine ⟨23449063820578842085290593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15632709213719228056860395 23449063820578842085290593)
    ·
      refine ⟨17586797865434131563967945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23449063820578842085290593 17586797865434131563967945)
      ·
        refine ⟨13190098399075598672975959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17586797865434131563967945 13190098399075598672975959)
        ·
          refine ⟨19785147598613398009463939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13190098399075598672975959 19785147598613398009463939)
          ·
            refine ⟨29677721397920097014195909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19785147598613398009463939 29677721397920097014195909)
            ·
              refine ⟨5564572762110018190161733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29677721397920097014195909 5564572762110018190161733)
              ·
                refine ⟨1043357392895628410655325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5564572762110018190161733 1043357392895628410655325)
                ·
                  refine ⟨391259022335860653995747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043357392895628410655325 391259022335860653995747)
                  ·
                    rfl

theorem cell21_1714442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_1714442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714442 prefixEnd_1714442 := by exact prefixLift 1714442
  have htrace : WordTrace (prefixWord ++ tailWord_1714442) baseStart_1714442 baseEnd_1714442 := by
    simpa [prefixWord, tailWord_1714442, baseEnd_1714442] using wordTrace_append hprefix tailTrace_1714442
  have hstable : (prefixWord ++ tailWord_1714442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714442).length < 2 ^ (prefixWord ++ tailWord_1714442).sum := by decide
  have hdescent : baseEnd_1714442 < baseStart_1714442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714549 : List Nat := [1, 3, 4, 1, 2, 2, 2, 2, 4]
def baseStart_1714549 : Nat := 118140960795 + 1714549 * 2 ^ 59
def prefixEnd_1714549 : Nat := 4983230072969 + 3 ^ 40 * 1714549 * 2
def baseEnd_1714549 : Nat := 391283441193652245712195

theorem tailTrace_1714549 : CollatzResearch.WordTrace tailWord_1714549 prefixEnd_1714549 391283441193652245712195 := by
  unfold tailWord_1714549
  simp only [CollatzResearch.WordTrace]
  refine ⟨62534739465489269501586701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41689826310326179667724467 62534739465489269501586701)
  ·
    refine ⟨23450527299558476063095013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62534739465489269501586701 23450527299558476063095013)
    ·
      refine ⟨4396973868667214261830315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23450527299558476063095013 4396973868667214261830315)
      ·
        refine ⟨6595460803000821392745473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4396973868667214261830315 6595460803000821392745473)
        ·
          refine ⟨4946595602250616044559105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6595460803000821392745473 4946595602250616044559105)
          ·
            refine ⟨3709946701687962033419329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4946595602250616044559105 3709946701687962033419329)
            ·
              refine ⟨2782460026265971525064497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3709946701687962033419329 2782460026265971525064497)
              ·
                refine ⟨2086845019699478643798373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2782460026265971525064497 2086845019699478643798373)
                ·
                  refine ⟨391283441193652245712195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2086845019699478643798373 391283441193652245712195)
                  ·
                    rfl

theorem cell21_1714549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_1714549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714549 prefixEnd_1714549 := by exact prefixLift 1714549
  have htrace : WordTrace (prefixWord ++ tailWord_1714549) baseStart_1714549 baseEnd_1714549 := by
    simpa [prefixWord, tailWord_1714549, baseEnd_1714549] using wordTrace_append hprefix tailTrace_1714549
  have hstable : (prefixWord ++ tailWord_1714549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714549).length < 2 ^ (prefixWord ++ tailWord_1714549).sum := by decide
  have hdescent : baseEnd_1714549 < baseStart_1714549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714563 : List Nat := [1, 1, 1, 3, 6, 2, 1, 6]
def baseStart_1714563 : Nat := 118140960795 + 1714563 * 2 ^ 59
def prefixEnd_1714563 : Nat := 4983230072969 + 3 ^ 40 * 1714563 * 2
def baseEnd_1714563 : Nat := 130428878728130444159611

theorem tailTrace_1714563 : CollatzResearch.WordTrace tailWord_1714563 prefixEnd_1714563 130428878728130444159611 := by
  unfold tailWord_1714563
  simp only [CollatzResearch.WordTrace]
  refine ⟨62535250087438549892596343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41690166724959033261730895 62535250087438549892596343)
  ·
    refine ⟨93802875131157824838894515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62535250087438549892596343 93802875131157824838894515)
    ·
      refine ⟨140704312696736737258341773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93802875131157824838894515 140704312696736737258341773)
      ·
        refine ⟨52764117261276276471878165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140704312696736737258341773 52764117261276276471878165)
        ·
          refine ⟨2473317996622325459619289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52764117261276276471878165 2473317996622325459619289)
          ·
            refine ⟨1854988497466744094714467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2473317996622325459619289 1854988497466744094714467)
            ·
              refine ⟨2782482746200116142071701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854988497466744094714467 2782482746200116142071701)
              ·
                refine ⟨130428878728130444159611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2782482746200116142071701 130428878728130444159611)
                ·
                  rfl

theorem cell21_1714563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 6].length) (baseStart_1714563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714563 prefixEnd_1714563 := by exact prefixLift 1714563
  have htrace : WordTrace (prefixWord ++ tailWord_1714563) baseStart_1714563 baseEnd_1714563 := by
    simpa [prefixWord, tailWord_1714563, baseEnd_1714563] using wordTrace_append hprefix tailTrace_1714563
  have hstable : (prefixWord ++ tailWord_1714563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714563).length < 2 ^ (prefixWord ++ tailWord_1714563).sum := by decide
  have hdescent : baseEnd_1714563 < baseStart_1714563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714580 : List Nat := [2, 4, 2, 1, 3, 1, 3, 5]
def baseStart_1714580 : Nat := 118140960795 + 1714580 * 2 ^ 59
def prefixEnd_1714580 : Nat := 4983230072969 + 3 ^ 40 * 1714580 * 2
def baseEnd_1714580 : Nat := 130430171938667693565155

theorem tailTrace_1714580 : CollatzResearch.WordTrace tailWord_1714580 prefixEnd_1714580 130430171938667693565155 := by
  unfold tailWord_1714580
  simp only [CollatzResearch.WordTrace]
  refine ⟨31267935064188480897982597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41690580085584641197310129 31267935064188480897982597)
  ·
    refine ⟨5862737824535340168371737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31267935064188480897982597 5862737824535340168371737)
    ·
      refine ⟨4397053368401505126278803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5862737824535340168371737 4397053368401505126278803)
      ·
        refine ⟨6595580052602257689418205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4397053368401505126278803 6595580052602257689418205)
        ·
          refine ⟨2473342519725846633531827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6595580052602257689418205 2473342519725846633531827)
          ·
            refine ⟨3710013779588769950297741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2473342519725846633531827 3710013779588769950297741)
            ·
              refine ⟨1391255167345788731361653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3710013779588769950297741 1391255167345788731361653)
              ·
                refine ⟨130430171938667693565155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1391255167345788731361653 130430171938667693565155)
                ·
                  rfl

theorem cell21_1714580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 5].length) (baseStart_1714580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714580 prefixEnd_1714580 := by exact prefixLift 1714580
  have htrace : WordTrace (prefixWord ++ tailWord_1714580) baseStart_1714580 baseEnd_1714580 := by
    simpa [prefixWord, tailWord_1714580, baseEnd_1714580] using wordTrace_append hprefix tailTrace_1714580
  have hstable : (prefixWord ++ tailWord_1714580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714580).length < 2 ^ (prefixWord ++ tailWord_1714580).sum := by decide
  have hdescent : baseEnd_1714580 < baseStart_1714580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714591 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 6]
def baseStart_1714591 : Nat := 118140960795 + 1714591 * 2 ^ 59
def prefixEnd_1714591 : Nat := 4983230072969 + 3 ^ 40 * 1714591 * 2
def baseEnd_1714591 : Nat := 391293026165869506012109

theorem tailTrace_1714591 : CollatzResearch.WordTrace tailWord_1714591 prefixEnd_1714591 391293026165869506012109 := by
  unfold tailWord_1714591
  simp only [CollatzResearch.WordTrace]
  refine ⟨62536271331337110674615627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41690847554224740449743751 62536271331337110674615627)
  ·
    refine ⟨93804406997005666011923441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62536271331337110674615627 93804406997005666011923441)
    ·
      refine ⟨70353305247754249508942581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93804406997005666011923441 70353305247754249508942581)
      ·
        refine ⟨6595622366976960891463367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70353305247754249508942581 6595622366976960891463367)
        ·
          refine ⟨9893433550465441337195051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6595622366976960891463367 9893433550465441337195051)
          ·
            refine ⟨14840150325698162005792577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9893433550465441337195051 14840150325698162005792577)
            ·
              refine ⟨11130112744273621504344433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14840150325698162005792577 11130112744273621504344433)
              ·
                refine ⟨8347584558205216128258325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11130112744273621504344433 8347584558205216128258325)
                ·
                  refine ⟨391293026165869506012109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8347584558205216128258325 391293026165869506012109)
                  ·
                    rfl

theorem cell21_1714591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 6].length) (baseStart_1714591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714591 prefixEnd_1714591 := by exact prefixLift 1714591
  have htrace : WordTrace (prefixWord ++ tailWord_1714591) baseStart_1714591 baseEnd_1714591 := by
    simpa [prefixWord, tailWord_1714591, baseEnd_1714591] using wordTrace_append hprefix tailTrace_1714591
  have hstable : (prefixWord ++ tailWord_1714591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714591).length < 2 ^ (prefixWord ++ tailWord_1714591).sum := by decide
  have hdescent : baseEnd_1714591 < baseStart_1714591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714667 : List Nat := [1, 1, 1, 1, 2, 3, 4, 4, 4]
def baseStart_1714667 : Nat := 118140960795 + 1714667 * 2 ^ 59
def prefixEnd_1714667 : Nat := 4983230072969 + 3 ^ 40 * 1714667 * 2
def baseEnd_1714667 : Nat := 391310370401310262745287

theorem tailTrace_1714667 : CollatzResearch.WordTrace tailWord_1714667 prefixEnd_1714667 391310370401310262745287 := by
  unfold tailWord_1714667
  simp only [CollatzResearch.WordTrace]
  refine ⟨62539043279061775654382255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41692695519374517102921503 62539043279061775654382255)
  ·
    refine ⟨93808564918592663481573383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62539043279061775654382255 93808564918592663481573383)
    ·
      refine ⟨140712847377888995222360075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93808564918592663481573383 140712847377888995222360075)
      ·
        refine ⟨211069271066833492833540113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140712847377888995222360075 211069271066833492833540113)
        ·
          refine ⟨158301953300125119625155085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211069271066833492833540113 158301953300125119625155085)
          ·
            refine ⟨59363232487546919859433157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158301953300125119625155085 59363232487546919859433157)
            ·
              refine ⟨11130606091415047473643717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59363232487546919859433157 11130606091415047473643717)
              ·
                refine ⟨2086988642140321401308197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11130606091415047473643717 2086988642140321401308197)
                ·
                  refine ⟨391310370401310262745287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2086988642140321401308197 391310370401310262745287)
                  ·
                    rfl

theorem cell21_1714667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 4].length) (baseStart_1714667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714667 prefixEnd_1714667 := by exact prefixLift 1714667
  have htrace : WordTrace (prefixWord ++ tailWord_1714667) baseStart_1714667 baseEnd_1714667 := by
    simpa [prefixWord, tailWord_1714667, baseEnd_1714667] using wordTrace_append hprefix tailTrace_1714667
  have hstable : (prefixWord ++ tailWord_1714667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714667).length < 2 ^ (prefixWord ++ tailWord_1714667).sum := by decide
  have hdescent : baseEnd_1714667 < baseStart_1714667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714670 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_1714670 : Nat := 118140960795 + 1714670 * 2 ^ 59
def prefixEnd_1714670 : Nat := 4983230072969 + 3 ^ 40 * 1714670 * 2
def baseEnd_1714670 : Nat := 391311055042182924195281

theorem tailTrace_1714670 : CollatzResearch.WordTrace tailWord_1714670 prefixEnd_1714670 391311055042182924195281 := by
  unfold tailWord_1714670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7817394087256363395842683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41692768465367271444494309 7817394087256363395842683)
  ·
    refine ⟨11726091130884545093764025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7817394087256363395842683 11726091130884545093764025)
    ·
      refine ⟨8794568348163408820323019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11726091130884545093764025 8794568348163408820323019)
      ·
        refine ⟨13191852522245113230484529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8794568348163408820323019 13191852522245113230484529)
        ·
          refine ⟨9893889391683834922863397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13191852522245113230484529 9893889391683834922863397)
          ·
            refine ⟨1855104260940719048036887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9893889391683834922863397 1855104260940719048036887)
            ·
              refine ⟨2782656391411078572055331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1855104260940719048036887 2782656391411078572055331)
              ·
                refine ⟨4173984587116617858082997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2782656391411078572055331 4173984587116617858082997)
                ·
                  refine ⟨391311055042182924195281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4173984587116617858082997 391311055042182924195281)
                  ·
                    rfl

theorem cell21_1714670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_1714670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714670 prefixEnd_1714670 := by exact prefixLift 1714670
  have htrace : WordTrace (prefixWord ++ tailWord_1714670) baseStart_1714670 baseEnd_1714670 := by
    simpa [prefixWord, tailWord_1714670, baseEnd_1714670] using wordTrace_append hprefix tailTrace_1714670
  have hstable : (prefixWord ++ tailWord_1714670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714670).length < 2 ^ (prefixWord ++ tailWord_1714670).sum := by decide
  have hdescent : baseEnd_1714670 < baseStart_1714670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714681 : List Nat := [1, 2, 1, 3, 1, 2, 3, 8]
def baseStart_1714681 : Nat := 118140960795 + 1714681 * 2 ^ 59
def prefixEnd_1714681 : Nat := 4983230072969 + 3 ^ 40 * 1714681 * 2
def baseEnd_1714681 : Nat := 130437855130683116503975

theorem tailTrace_1714681 : CollatzResearch.WordTrace tailWord_1714681 prefixEnd_1714681 130437855130683116503975 := by
  unfold tailWord_1714681
  simp only [CollatzResearch.WordTrace]
  refine ⟨62539553901011056045391897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41693035934007370696927931 62539553901011056045391897)
  ·
    refine ⟨46904665425758292034043923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62539553901011056045391897 46904665425758292034043923)
    ·
      refine ⟨70356998138637438051065885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46904665425758292034043923 70356998138637438051065885)
      ·
        refine ⟨26383874301989039269149707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70356998138637438051065885 26383874301989039269149707)
        ·
          refine ⟨39575811452983558903724561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26383874301989039269149707 39575811452983558903724561)
          ·
            refine ⟨29681858589737669177793421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39575811452983558903724561 29681858589737669177793421)
            ·
              refine ⟨11130696971151625941672533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29681858589737669177793421 11130696971151625941672533)
              ·
                refine ⟨130437855130683116503975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11130696971151625941672533 130437855130683116503975)
                ·
                  rfl

theorem cell21_1714681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 8].length) (baseStart_1714681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714681 prefixEnd_1714681 := by exact prefixLift 1714681
  have htrace : WordTrace (prefixWord ++ tailWord_1714681) baseStart_1714681 baseEnd_1714681 := by
    simpa [prefixWord, tailWord_1714681, baseEnd_1714681] using wordTrace_append hprefix tailTrace_1714681
  have hstable : (prefixWord ++ tailWord_1714681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714681).length < 2 ^ (prefixWord ++ tailWord_1714681).sum := by decide
  have hdescent : baseEnd_1714681 < baseStart_1714681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714743 : List Nat := [1, 1, 3, 1, 2, 3, 1, 5, 4]
def baseStart_1714743 : Nat := 118140960795 + 1714743 * 2 ^ 59
def prefixEnd_1714743 : Nat := 4983230072969 + 3 ^ 40 * 1714743 * 2
def baseEnd_1714743 : Nat := 391327714636751019478465

theorem tailTrace_1714743 : CollatzResearch.WordTrace tailWord_1714743 prefixEnd_1714743 391327714636751019478465 := by
  unfold tailWord_1714743
  simp only [CollatzResearch.WordTrace]
  refine ⟨62541815226786440634148883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41694543484524293756099255 62541815226786440634148883)
  ·
    refine ⟨93812722840179660951223325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62541815226786440634148883 93812722840179660951223325)
    ·
      refine ⟨35179771065067372856708747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93812722840179660951223325 35179771065067372856708747)
      ·
        refine ⟨52769656597601059285063121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35179771065067372856708747 52769656597601059285063121)
        ·
          refine ⟨39577242448200794463797341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52769656597601059285063121 39577242448200794463797341)
          ·
            refine ⟨14841465918075297923924003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39577242448200794463797341 14841465918075297923924003)
            ·
              refine ⟨22262198877112946885886005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14841465918075297923924003 22262198877112946885886005)
              ·
                refine ⟨2087081144729338770551813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22262198877112946885886005 2087081144729338770551813)
                ·
                  refine ⟨391327714636751019478465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2087081144729338770551813 391327714636751019478465)
                  ·
                    rfl

theorem cell21_1714743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 4].length) (baseStart_1714743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714743 prefixEnd_1714743 := by exact prefixLift 1714743
  have htrace : WordTrace (prefixWord ++ tailWord_1714743) baseStart_1714743 baseEnd_1714743 := by
    simpa [prefixWord, tailWord_1714743, baseEnd_1714743] using wordTrace_append hprefix tailTrace_1714743
  have hstable : (prefixWord ++ tailWord_1714743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714743).length < 2 ^ (prefixWord ++ tailWord_1714743).sum := by decide
  have hdescent : baseEnd_1714743 < baseStart_1714743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714836 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 6]
def baseStart_1714836 : Nat := 118140960795 + 1714836 * 2 ^ 59
def prefixEnd_1714836 : Nat := 4983230072969 + 3 ^ 40 * 1714836 * 2
def baseEnd_1714836 : Nat := 391348938503803524428275

theorem tailTrace_1714836 : CollatzResearch.WordTrace tailWord_1714836 prefixEnd_1714836 391348938503803524428275 := by
  unfold tailWord_1714836
  simp only [CollatzResearch.WordTrace]
  refine ⟨31272603607724758758642181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41696804810299678344856241 31272603607724758758642181)
  ·
    refine ⟨5863613176448392267245409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31272603607724758758642181 5863613176448392267245409)
    ·
      refine ⟨4397709882336294200434057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5863613176448392267245409 4397709882336294200434057)
      ·
        refine ⟨3298282411752220650325543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4397709882336294200434057 3298282411752220650325543)
        ·
          refine ⟨4947423617628330975488315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3298282411752220650325543 4947423617628330975488315)
          ·
            refine ⟨7421135426442496463232473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4947423617628330975488315 7421135426442496463232473)
            ·
              refine ⟨5565851569831872347424355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7421135426442496463232473 5565851569831872347424355)
              ·
                refine ⟨8348777354747808521136533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565851569831872347424355 8348777354747808521136533)
                ·
                  refine ⟨391348938503803524428275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8348777354747808521136533 391348938503803524428275)
                  ·
                    rfl

theorem cell21_1714836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_1714836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1714836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1714836 prefixEnd_1714836 := by exact prefixLift 1714836
  have htrace : WordTrace (prefixWord ++ tailWord_1714836) baseStart_1714836 baseEnd_1714836 := by
    simpa [prefixWord, tailWord_1714836, baseEnd_1714836] using wordTrace_append hprefix tailTrace_1714836
  have hstable : (prefixWord ++ tailWord_1714836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714836).length < 2 ^ (prefixWord ++ tailWord_1714836).sum := by decide
  have hdescent : baseEnd_1714836 < baseStart_1714836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715002 : List Nat := [3, 1, 1, 1, 6, 2, 7]
def baseStart_1715002 : Nat := 118140960795 + 1715002 * 2 ^ 59
def prefixEnd_1715002 : Nat := 4983230072969 + 3 ^ 40 * 1715002 * 2
def baseEnd_1715002 : Nat := 43487424662824902740141

theorem tailTrace_1715002 : CollatzResearch.WordTrace tailWord_1715002 prefixEnd_1715002 43487424662824902740141 := by
  unfold tailWord_1715002
  simp only [CollatzResearch.WordTrace]
  refine ⟨15637815433212031966956815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41700841155232085245218173 15637815433212031966956815)
  ·
    refine ⟨23456723149818047950435223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15637815433212031966956815 23456723149818047950435223)
    ·
      refine ⟨35185084724727071925652835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23456723149818047950435223 35185084724727071925652835)
      ·
        refine ⟨52777627087090607888479253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35185084724727071925652835 52777627087090607888479253)
        ·
          refine ⟨2473951269707372244772465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52777627087090607888479253 2473951269707372244772465)
          ·
            refine ⟨1855463452280529183579349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2473951269707372244772465 1855463452280529183579349)
            ·
              refine ⟨43487424662824902740141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1855463452280529183579349 43487424662824902740141)
              ·
                rfl

theorem cell21_1715002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 7].length) (baseStart_1715002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1715002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1715002 prefixEnd_1715002 := by exact prefixLift 1715002
  have htrace : WordTrace (prefixWord ++ tailWord_1715002) baseStart_1715002 baseEnd_1715002 := by
    simpa [prefixWord, tailWord_1715002, baseEnd_1715002] using wordTrace_append hprefix tailTrace_1715002
  have hstable : (prefixWord ++ tailWord_1715002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715002).length < 2 ^ (prefixWord ++ tailWord_1715002).sum := by decide
  have hdescent : baseEnd_1715002 < baseStart_1715002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715061 : List Nat := [1, 3, 4, 1, 1, 11]
def baseStart_1715061 : Nat := 118140960795 + 1715061 * 2 ^ 59
def prefixEnd_1715061 : Nat := 4983230072969 + 3 ^ 40 * 1715061 * 2
def baseEnd_1715061 : Nat := 14496306909972338265845

theorem tailTrace_1715061 : CollatzResearch.WordTrace tailWord_1715061 prefixEnd_1715061 14496306909972338265845 := by
  unfold tailWord_1715061
  simp only [CollatzResearch.WordTrace]
  refine ⟨62553413639634380944225037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41702275759756253962816691 62553413639634380944225037)
  ·
    refine ⟨23457530114862892854084389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62553413639634380944225037 23457530114862892854084389)
    ·
      refine ⟨4398286896536792410140823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23457530114862892854084389 4398286896536792410140823)
      ·
        refine ⟨6597430344805188615211235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4398286896536792410140823 6597430344805188615211235)
        ·
          refine ⟨9896145517207782922816853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6597430344805188615211235 9896145517207782922816853)
          ·
            refine ⟨14496306909972338265845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9896145517207782922816853 14496306909972338265845)
            ·
              rfl

theorem cell21_1715061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 11].length) (baseStart_1715061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1715061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1715061 prefixEnd_1715061 := by exact prefixLift 1715061
  have htrace : WordTrace (prefixWord ++ tailWord_1715061) baseStart_1715061 baseEnd_1715061 := by
    simpa [prefixWord, tailWord_1715061, baseEnd_1715061] using wordTrace_append hprefix tailTrace_1715061
  have hstable : (prefixWord ++ tailWord_1715061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715061).length < 2 ^ (prefixWord ++ tailWord_1715061).sum := by decide
  have hdescent : baseEnd_1715061 < baseStart_1715061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715154 : List Nat := [3, 2, 2, 3, 1, 2, 1, 7]
def baseStart_1715154 : Nat := 118140960795 + 1715154 * 2 ^ 59
def prefixEnd_1715154 : Nat := 4983230072969 + 3 ^ 40 * 1715154 * 2
def baseEnd_1715154 : Nat := 130473836812101879375875

theorem tailTrace_1715154 : CollatzResearch.WordTrace tailWord_1715154 prefixEnd_1715154 130473836812101879375875 := by
  unfold tailWord_1715154
  simp only [CollatzResearch.WordTrace]
  refine ⟨15639201407074364456840129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41704537085531638551573677 15639201407074364456840129)
  ·
    refine ⟨11729401055305773342630097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15639201407074364456840129 11729401055305773342630097)
    ·
      refine ⟨8797050791479330006972573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11729401055305773342630097 8797050791479330006972573)
      ·
        refine ⟨3298894046804748752614715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8797050791479330006972573 3298894046804748752614715)
        ·
          refine ⟨4948341070207123128922073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3298894046804748752614715 4948341070207123128922073)
          ·
            refine ⟨3711255802655342346691555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4948341070207123128922073 3711255802655342346691555)
            ·
              refine ⟨5566883703983013520037333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3711255802655342346691555 5566883703983013520037333)
              ·
                refine ⟨130473836812101879375875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5566883703983013520037333 130473836812101879375875)
                ·
                  rfl

theorem cell21_1715154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_1715154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1715154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1715154 prefixEnd_1715154 := by exact prefixLift 1715154
  have htrace : WordTrace (prefixWord ++ tailWord_1715154) baseStart_1715154 baseEnd_1715154 := by
    simpa [prefixWord, tailWord_1715154, baseEnd_1715154] using wordTrace_append hprefix tailTrace_1715154
  have hstable : (prefixWord ++ tailWord_1715154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715154).length < 2 ^ (prefixWord ++ tailWord_1715154).sum := by decide
  have hdescent : baseEnd_1715154 < baseStart_1715154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715185 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 5]
def baseStart_1715185 : Nat := 118140960795 + 1715185 * 2 ^ 59
def prefixEnd_1715185 : Nat := 4983230072969 + 3 ^ 40 * 1715185 * 2
def baseEnd_1715185 : Nat := 391428585058656473110895

theorem tailTrace_1715185 : CollatzResearch.WordTrace tailWord_1715185 prefixEnd_1715185 391428585058656473110895 := by
  unfold tailWord_1715185
  simp only [CollatzResearch.WordTrace]
  refine ⟨62557936291185150121739009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41705290860790100081159339 62557936291185150121739009)
  ·
    refine ⟨46918452218388862591304257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62557936291185150121739009 46918452218388862591304257)
    ·
      refine ⟨35188839163791646943478193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46918452218388862591304257 35188839163791646943478193)
      ·
        refine ⟨26391629372843735207608645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35188839163791646943478193 26391629372843735207608645)
        ·
          refine ⟨4948430507408200351426621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26391629372843735207608645 4948430507408200351426621)
          ·
            refine ⟨1855661440278075131784983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4948430507408200351426621 1855661440278075131784983)
            ·
              refine ⟨2783492160417112697677475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1855661440278075131784983 2783492160417112697677475)
              ·
                refine ⟨4175238240625669046516213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2783492160417112697677475 4175238240625669046516213)
                ·
                  refine ⟨391428585058656473110895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4175238240625669046516213 391428585058656473110895)
                  ·
                    rfl

theorem cell21_1715185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_1715185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1715185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1715185 prefixEnd_1715185 := by exact prefixLift 1715185
  have htrace : WordTrace (prefixWord ++ tailWord_1715185) baseStart_1715185 baseEnd_1715185 := by
    simpa [prefixWord, tailWord_1715185, baseEnd_1715185] using wordTrace_append hprefix tailTrace_1715185
  have hstable : (prefixWord ++ tailWord_1715185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715185).length < 2 ^ (prefixWord ++ tailWord_1715185).sum := by decide
  have hdescent : baseEnd_1715185 < baseStart_1715185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715337 : List Nat := [1, 2, 1, 1, 4, 3, 3, 3, 3]
def baseStart_1715337 : Nat := 118140960795 + 1715337 * 2 ^ 59
def prefixEnd_1715337 : Nat := 4983230072969 + 3 ^ 40 * 1715337 * 2
def baseEnd_1715337 : Nat := 391463273529537986577251

theorem tailTrace_1715337 : CollatzResearch.WordTrace tailWord_1715337 prefixEnd_1715337 391463273529537986577251 := by
  unfold tailWord_1715337
  simp only [CollatzResearch.WordTrace]
  refine ⟨62563480186634480081272265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41708986791089653387514843 62563480186634480081272265)
  ·
    refine ⟨46922610139975860060954199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62563480186634480081272265 46922610139975860060954199)
    ·
      refine ⟨70383915209963790091431299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46922610139975860060954199 70383915209963790091431299)
      ·
        refine ⟨105575872814945685137146949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70383915209963790091431299 105575872814945685137146949)
        ·
          refine ⟨19795476152802315963215053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105575872814945685137146949 19795476152802315963215053)
          ·
            refine ⟨7423303557300868486205645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19795476152802315963215053 7423303557300868486205645)
            ·
              refine ⟨2783738833987825682327117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7423303557300868486205645 2783738833987825682327117)
              ·
                refine ⟨1043902062745434630872669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2783738833987825682327117 1043902062745434630872669)
                ·
                  refine ⟨391463273529537986577251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043902062745434630872669 391463273529537986577251)
                  ·
                    rfl

theorem cell21_1715337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 3].length) (baseStart_1715337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1715337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1715337 prefixEnd_1715337 := by exact prefixLift 1715337
  have htrace : WordTrace (prefixWord ++ tailWord_1715337) baseStart_1715337 baseEnd_1715337 := by
    simpa [prefixWord, tailWord_1715337, baseEnd_1715337] using wordTrace_append hprefix tailTrace_1715337
  have hstable : (prefixWord ++ tailWord_1715337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715337).length < 2 ^ (prefixWord ++ tailWord_1715337).sum := by decide
  have hdescent : baseEnd_1715337 < baseStart_1715337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715365 : List Nat := [1, 3, 1, 2, 1, 5, 2, 6]
def baseStart_1715365 : Nat := 118140960795 + 1715365 * 2 ^ 59
def prefixEnd_1715365 : Nat := 4983230072969 + 3 ^ 40 * 1715365 * 2
def baseEnd_1715365 : Nat := 130489887837005386703509

theorem tailTrace_1715365 : CollatzResearch.WordTrace tailWord_1715365 prefixEnd_1715365 130489887837005386703509 := by
  unfold tailWord_1715365
  simp only [CollatzResearch.WordTrace]
  refine ⟨62564501430533040863291549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41709667620355360575527699 62564501430533040863291549)
  ·
    refine ⟨23461688036449890323734331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62564501430533040863291549 23461688036449890323734331)
    ·
      refine ⟨35192532054674835485601497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23461688036449890323734331 35192532054674835485601497)
      ·
        refine ⟨26394399041006126614201123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35192532054674835485601497 26394399041006126614201123)
        ·
          refine ⟨39591598561509189921301685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26394399041006126614201123 39591598561509189921301685)
          ·
            refine ⟨3711712365141486555122033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39591598561509189921301685 3711712365141486555122033)
            ·
              refine ⟨2783784273856114916341525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3711712365141486555122033 2783784273856114916341525)
              ·
                refine ⟨130489887837005386703509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2783784273856114916341525 130489887837005386703509)
                ·
                  rfl

theorem cell21_1715365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 6].length) (baseStart_1715365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1715365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1715365 prefixEnd_1715365 := by exact prefixLift 1715365
  have htrace : WordTrace (prefixWord ++ tailWord_1715365) baseStart_1715365 baseEnd_1715365 := by
    simpa [prefixWord, tailWord_1715365, baseEnd_1715365] using wordTrace_append hprefix tailTrace_1715365
  have hstable : (prefixWord ++ tailWord_1715365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715365).length < 2 ^ (prefixWord ++ tailWord_1715365).sum := by decide
  have hdescent : baseEnd_1715365 < baseStart_1715365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715379 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 5]
def baseStart_1715379 : Nat := 118140960795 + 1715379 * 2 ^ 59
def prefixEnd_1715379 : Nat := 4983230072969 + 3 ^ 40 * 1715379 * 2
def baseEnd_1715379 : Nat := 391472858501755246877165

theorem tailTrace_1715379 : CollatzResearch.WordTrace tailWord_1715379 prefixEnd_1715379 391472858501755246877165 := by
  unfold tailWord_1715379
  simp only [CollatzResearch.WordTrace]
  refine ⟨62565012052482321254301191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41710008034988214169534127 62565012052482321254301191)
  ·
    refine ⟨93847518078723481881451787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62565012052482321254301191 93847518078723481881451787)
    ·
      refine ⟨140771277118085222822177681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93847518078723481881451787 140771277118085222822177681)
      ·
        refine ⟨105578457838563917116633261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140771277118085222822177681 105578457838563917116633261)
        ·
          refine ⟨39591921689461468918737473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105578457838563917116633261 39591921689461468918737473)
          ·
            refine ⟨29693941267096101689053105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39591921689461468918737473 29693941267096101689053105)
            ·
              refine ⟨22270455950322076266789829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29693941267096101689053105 22270455950322076266789829)
              ·
                refine ⟨4175710490685389300023093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22270455950322076266789829 4175710490685389300023093)
                ·
                  refine ⟨391472858501755246877165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4175710490685389300023093 391472858501755246877165)
                  ·
                    rfl

theorem cell21_1715379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 5].length) (baseStart_1715379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1715379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1715379 prefixEnd_1715379 := by exact prefixLift 1715379
  have htrace : WordTrace (prefixWord ++ tailWord_1715379) baseStart_1715379 baseEnd_1715379 := by
    simpa [prefixWord, tailWord_1715379, baseEnd_1715379] using wordTrace_append hprefix tailTrace_1715379
  have hstable : (prefixWord ++ tailWord_1715379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715379).length < 2 ^ (prefixWord ++ tailWord_1715379).sum := by decide
  have hdescent : baseEnd_1715379 < baseStart_1715379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715405 : List Nat := [1, 6, 2, 2, 1, 2, 2, 2, 3]
def baseStart_1715405 : Nat := 118140960795 + 1715405 * 2 ^ 59
def prefixEnd_1715405 : Nat := 4983230072969 + 3 ^ 40 * 1715405 * 2
def baseEnd_1715405 : Nat := 391478792055984979443779

theorem tailTrace_1715405 : CollatzResearch.WordTrace tailWord_1715405 prefixEnd_1715405 391478792055984979443779 := by
  unfold tailWord_1715405
  simp only [CollatzResearch.WordTrace]
  refine ⟨62565960350388127694747669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41710640233592085129831779 62565960350388127694747669)
  ·
    refine ⟨2932779391424443485691297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62565960350388127694747669 2932779391424443485691297)
    ·
      refine ⟨2199584543568332614268473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2932779391424443485691297 2199584543568332614268473)
      ·
        refine ⟨1649688407676249460701355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2199584543568332614268473 1649688407676249460701355)
        ·
          refine ⟨2474532611514374191052033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649688407676249460701355 2474532611514374191052033)
          ·
            refine ⟨1855899458635780643289025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2474532611514374191052033 1855899458635780643289025)
            ·
              refine ⟨1391924593976835482466769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1855899458635780643289025 1391924593976835482466769)
              ·
                refine ⟨1043943445482626611850077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1391924593976835482466769 1043943445482626611850077)
                ·
                  refine ⟨391478792055984979443779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043943445482626611850077 391478792055984979443779)
                  ·
                    rfl

theorem cell21_1715405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_1715405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1715405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1715405 prefixEnd_1715405 := by exact prefixLift 1715405
  have htrace : WordTrace (prefixWord ++ tailWord_1715405) baseStart_1715405 baseEnd_1715405 := by
    simpa [prefixWord, tailWord_1715405, baseEnd_1715405] using wordTrace_append hprefix tailTrace_1715405
  have hstable : (prefixWord ++ tailWord_1715405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715405).length < 2 ^ (prefixWord ++ tailWord_1715405).sum := by decide
  have hdescent : baseEnd_1715405 < baseStart_1715405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715458 : List Nat := [3, 4, 1, 1, 3, 1, 8]
def baseStart_1715458 : Nat := 118140960795 + 1715458 * 2 ^ 59
def prefixEnd_1715458 : Nat := 4983230072969 + 3 ^ 40 * 1715458 * 2
def baseEnd_1715458 : Nat := 43498987486452073895593

theorem tailTrace_1715458 : CollatzResearch.WordTrace tailWord_1715458 prefixEnd_1715458 43498987486452073895593 := by
  unfold tailWord_1715458
  simp only [CollatzResearch.WordTrace]
  refine ⟨15641973354799029436606757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41711928946130745164284685 15641973354799029436606757)
  ·
    refine ⟨2932870004024818019363767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15641973354799029436606757 2932870004024818019363767)
    ·
      refine ⟨4399305006037227029045651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2932870004024818019363767 4399305006037227029045651)
      ·
        refine ⟨6598957509055840543568477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4399305006037227029045651 6598957509055840543568477)
        ·
          refine ⟨2474609065895940203838179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6598957509055840543568477 2474609065895940203838179)
          ·
            refine ⟨3711913598843910305757269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474609065895940203838179 3711913598843910305757269)
            ·
              refine ⟨43498987486452073895593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3711913598843910305757269 43498987486452073895593)
              ·
                rfl

theorem cell21_1715458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 8].length) (baseStart_1715458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1715458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1715458 prefixEnd_1715458 := by exact prefixLift 1715458
  have htrace : WordTrace (prefixWord ++ tailWord_1715458) baseStart_1715458 baseEnd_1715458 := by
    simpa [prefixWord, tailWord_1715458, baseEnd_1715458] using wordTrace_append hprefix tailTrace_1715458
  have hstable : (prefixWord ++ tailWord_1715458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715458).length < 2 ^ (prefixWord ++ tailWord_1715458).sum := by decide
  have hdescent : baseEnd_1715458 < baseStart_1715458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715506 : List Nat := [3, 2, 1, 1, 4, 3, 1, 3, 3]
def baseStart_1715506 : Nat := 118140960795 + 1715506 * 2 ^ 59
def prefixEnd_1715506 : Nat := 4983230072969 + 3 ^ 40 * 1715506 * 2
def baseEnd_1715506 : Nat := 391501841632031248260239

theorem tailTrace_1715506 : CollatzResearch.WordTrace tailWord_1715506 prefixEnd_1715506 391501841632031248260239 := by
  unfold tailWord_1715506
  simp only [CollatzResearch.WordTrace]
  refine ⟨15642411030755555486043593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41713096082014814629449581 15642411030755555486043593)
  ·
    refine ⟨11731808273066666614532695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15642411030755555486043593 11731808273066666614532695)
    ·
      refine ⟨17597712409599999921799043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11731808273066666614532695 17597712409599999921799043)
      ·
        refine ⟨26396568614399999882698565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17597712409599999921799043 26396568614399999882698565)
        ·
          refine ⟨4949356615199999978005981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26396568614399999882698565 4949356615199999978005981)
          ·
            refine ⟨1856008730699999991752243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4949356615199999978005981 1856008730699999991752243)
            ·
              refine ⟨2784013096049999987628365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1856008730699999991752243 2784013096049999987628365)
              ·
                refine ⟨1044004911018749995360637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2784013096049999987628365 1044004911018749995360637)
                ·
                  refine ⟨391501841632031248260239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044004911018749995360637 391501841632031248260239)
                  ·
                    rfl

theorem cell21_1715506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_1715506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1715506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1715506 prefixEnd_1715506 := by exact prefixLift 1715506
  have htrace : WordTrace (prefixWord ++ tailWord_1715506) baseStart_1715506 baseEnd_1715506 := by
    simpa [prefixWord, tailWord_1715506, baseEnd_1715506] using wordTrace_append hprefix tailTrace_1715506
  have hstable : (prefixWord ++ tailWord_1715506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715506).length < 2 ^ (prefixWord ++ tailWord_1715506).sum := by decide
  have hdescent : baseEnd_1715506 < baseStart_1715506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715655 : List Nat := [1, 1, 4, 1, 1, 3, 5, 1, 4]
def baseStart_1715655 : Nat := 118140960795 + 1715655 * 2 ^ 59
def prefixEnd_1715655 : Nat := 4983230072969 + 3 ^ 40 * 1715655 * 2
def baseEnd_1715655 : Nat := 391535845462040100276601

theorem tailTrace_1715655 : CollatzResearch.WordTrace tailWord_1715655 prefixEnd_1715655 391535845462040100276601 := by
  unfold tailWord_1715655
  simp only [CollatzResearch.WordTrace]
  refine ⟨62575078599482420391348419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41716719066321613594232279 62575078599482420391348419)
  ·
    refine ⟨93862617899223630587022629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62575078599482420391348419 93862617899223630587022629)
    ·
      refine ⟨17599240856104430735066743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93862617899223630587022629 17599240856104430735066743)
      ·
        refine ⟨26398861284156646102600115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17599240856104430735066743 26398861284156646102600115)
        ·
          refine ⟨39598291926234969153900173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26398861284156646102600115 39598291926234969153900173)
          ·
            refine ⟨14849359472338113432712565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39598291926234969153900173 14849359472338113432712565)
            ·
              refine ⟨1392127450531698134316803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14849359472338113432712565 1392127450531698134316803)
              ·
                refine ⟨2088191175797547201475205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1392127450531698134316803 2088191175797547201475205)
                ·
                  refine ⟨391535845462040100276601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2088191175797547201475205 391535845462040100276601)
                  ·
                    rfl

theorem cell21_1715655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 4].length) (baseStart_1715655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1715655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1715655 prefixEnd_1715655 := by exact prefixLift 1715655
  have htrace : WordTrace (prefixWord ++ tailWord_1715655) baseStart_1715655 baseEnd_1715655 := by
    simpa [prefixWord, tailWord_1715655, baseEnd_1715655] using wordTrace_append hprefix tailTrace_1715655
  have hstable : (prefixWord ++ tailWord_1715655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715655).length < 2 ^ (prefixWord ++ tailWord_1715655).sum := by decide
  have hdescent : baseEnd_1715655 < baseStart_1715655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715849 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 6]
def baseStart_1715849 : Nat := 118140960795 + 1715849 * 2 ^ 59
def prefixEnd_1715849 : Nat := 4983230072969 + 3 ^ 40 * 1715849 * 2
def baseEnd_1715849 : Nat := 391580118905138874042871

theorem tailTrace_1715849 : CollatzResearch.WordTrace tailWord_1715849 prefixEnd_1715849 391580118905138874042871 := by
  unfold tailWord_1715849
  simp only [CollatzResearch.WordTrace]
  refine ⟨62582154360779591523910601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41721436240519727682607067 62582154360779591523910601)
  ·
    refine ⟨46936615770584693642932951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62582154360779591523910601 46936615770584693642932951)
    ·
      refine ⟨70404923655877040464399427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46936615770584693642932951 70404923655877040464399427)
      ·
        refine ⟨105607385483815560696599141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70404923655877040464399427 105607385483815560696599141)
        ·
          refine ⟨19801384778215417630612339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105607385483815560696599141 19801384778215417630612339)
          ·
            refine ⟨29702077167323126445918509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19801384778215417630612339 29702077167323126445918509)
            ·
              refine ⟨11138278937746172417219441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29702077167323126445918509 11138278937746172417219441)
              ·
                refine ⟨8353709203309629312914581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11138278937746172417219441 8353709203309629312914581)
                ·
                  refine ⟨391580118905138874042871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8353709203309629312914581 391580118905138874042871)
                  ·
                    rfl

theorem cell21_1715849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_1715849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1715849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1715849 prefixEnd_1715849 := by exact prefixLift 1715849
  have htrace : WordTrace (prefixWord ++ tailWord_1715849) baseStart_1715849 baseEnd_1715849 := by
    simpa [prefixWord, tailWord_1715849, baseEnd_1715849] using wordTrace_append hprefix tailTrace_1715849
  have hstable : (prefixWord ++ tailWord_1715849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715849).length < 2 ^ (prefixWord ++ tailWord_1715849).sum := by decide
  have hdescent : baseEnd_1715849 < baseStart_1715849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715928 : List Nat := [2, 1, 2, 2, 3, 1, 3, 4, 3]
def baseStart_1715928 : Nat := 118140960795 + 1715928 * 2 ^ 59
def prefixEnd_1715928 : Nat := 4983230072969 + 3 ^ 40 * 1715928 * 2
def baseEnd_1715928 : Nat := 391598147781452292226043

theorem tailTrace_1715928 : CollatzResearch.WordTrace tailWord_1715928 prefixEnd_1715928 391598147781452292226043 := by
  unfold tailWord_1715928
  simp only [CollatzResearch.WordTrace]
  refine ⟨31292517863746694008018219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41723357151662258677357625 31292517863746694008018219)
  ·
    refine ⟨46938776795620041012027329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31292517863746694008018219 46938776795620041012027329)
    ·
      refine ⟨35204082596715030759020497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46938776795620041012027329 35204082596715030759020497)
      ·
        refine ⟨26403061947536273069265373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35204082596715030759020497 26403061947536273069265373)
        ·
          refine ⟨9901148230326102400974515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26403061947536273069265373 9901148230326102400974515)
          ·
            refine ⟨14851722345489153601461773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9901148230326102400974515 14851722345489153601461773)
            ·
              refine ⟨5569395879558432600548165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14851722345489153601461773 5569395879558432600548165)
              ·
                refine ⟨1044261727417206112602781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5569395879558432600548165 1044261727417206112602781)
                ·
                  refine ⟨391598147781452292226043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044261727417206112602781 391598147781452292226043)
                  ·
                    rfl

theorem cell21_1715928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 3].length) (baseStart_1715928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1715928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1715928 prefixEnd_1715928 := by exact prefixLift 1715928
  have htrace : WordTrace (prefixWord ++ tailWord_1715928) baseStart_1715928 baseEnd_1715928 := by
    simpa [prefixWord, tailWord_1715928, baseEnd_1715928] using wordTrace_append hprefix tailTrace_1715928
  have hstable : (prefixWord ++ tailWord_1715928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715928).length < 2 ^ (prefixWord ++ tailWord_1715928).sum := by decide
  have hdescent : baseEnd_1715928 < baseStart_1715928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716015 : List Nat := [1, 1, 2, 1, 2, 1, 2, 11]
def baseStart_1716015 : Nat := 118140960795 + 1716015 * 2 ^ 59
def prefixEnd_1716015 : Nat := 4983230072969 + 3 ^ 40 * 1716015 * 2
def baseEnd_1716015 : Nat := 130539334122253158091955

theorem tailTrace_1716015 : CollatzResearch.WordTrace tailWord_1716015 prefixEnd_1716015 130539334122253158091955 := by
  unfold tailWord_1716015
  simp only [CollatzResearch.WordTrace]
  refine ⟨62588208878178201874453499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41725472585452134582968999 62588208878178201874453499)
  ·
    refine ⟨93882313317267302811680249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62588208878178201874453499 93882313317267302811680249)
    ·
      refine ⟨70411734987950477108760187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93882313317267302811680249 70411734987950477108760187)
      ·
        refine ⟨105617602481925715663140281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70411734987950477108760187 105617602481925715663140281)
        ·
          refine ⟨79213201861444286747355211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105617602481925715663140281 79213201861444286747355211)
          ·
            refine ⟨118819802792166430121032817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79213201861444286747355211 118819802792166430121032817)
            ·
              refine ⟨89114852094124822590774613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118819802792166430121032817 89114852094124822590774613)
              ·
                refine ⟨130539334122253158091955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 89114852094124822590774613 130539334122253158091955)
                ·
                  rfl

theorem cell21_1716015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 11].length) (baseStart_1716015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716015 prefixEnd_1716015 := by exact prefixLift 1716015
  have htrace : WordTrace (prefixWord ++ tailWord_1716015) baseStart_1716015 baseEnd_1716015 := by
    simpa [prefixWord, tailWord_1716015, baseEnd_1716015] using wordTrace_append hprefix tailTrace_1716015
  have hstable : (prefixWord ++ tailWord_1716015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716015).length < 2 ^ (prefixWord ++ tailWord_1716015).sum := by decide
  have hdescent : baseEnd_1716015 < baseStart_1716015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716038 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1716038 : Nat := 118140960795 + 1716038 * 2 ^ 59
def prefixEnd_1716038 : Nat := 4983230072969 + 3 ^ 40 * 1716038 * 2
def baseEnd_1716038 : Nat := 391623251280116545392485

theorem tailTrace_1716038 : CollatzResearch.WordTrace tailWord_1716038 prefixEnd_1716038 391623251280116545392485 := by
  unfold tailWord_1716038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1955907742409214900079399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41726031838063251201693845 1955907742409214900079399)
  ·
    refine ⟨2933861613613822350119099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1955907742409214900079399 2933861613613822350119099)
    ·
      refine ⟨4400792420420733525178649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2933861613613822350119099 4400792420420733525178649)
      ·
        refine ⟨3300594315315550143883987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4400792420420733525178649 3300594315315550143883987)
        ·
          refine ⟨4950891472973325215825981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3300594315315550143883987 4950891472973325215825981)
          ·
            refine ⟨1856584302364996955934743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4950891472973325215825981 1856584302364996955934743)
            ·
              refine ⟨2784876453547495433902115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1856584302364996955934743 2784876453547495433902115)
              ·
                refine ⟨4177314680321243150853173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2784876453547495433902115 4177314680321243150853173)
                ·
                  refine ⟨391623251280116545392485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4177314680321243150853173 391623251280116545392485)
                  ·
                    rfl

theorem cell21_1716038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1716038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716038 prefixEnd_1716038 := by exact prefixLift 1716038
  have htrace : WordTrace (prefixWord ++ tailWord_1716038) baseStart_1716038 baseEnd_1716038 := by
    simpa [prefixWord, tailWord_1716038, baseEnd_1716038] using wordTrace_append hprefix tailTrace_1716038
  have hstable : (prefixWord ++ tailWord_1716038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716038).length < 2 ^ (prefixWord ++ tailWord_1716038).sum := by decide
  have hdescent : baseEnd_1716038 < baseStart_1716038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716052 : List Nat := [2, 4, 1, 1, 3, 3, 2, 1, 4]
def baseStart_1716052 : Nat := 118140960795 + 1716052 * 2 ^ 59
def prefixEnd_1716052 : Nat := 4983230072969 + 3 ^ 40 * 1716052 * 2
def baseEnd_1716052 : Nat := 391626446270855632159123

theorem tailTrace_1716052 : CollatzResearch.WordTrace tailWord_1716052 prefixEnd_1716052 391626446270855632159123 := by
  unfold tailWord_1716052
  simp only [CollatzResearch.WordTrace]
  refine ⟨31294779189522078596775205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41726372252696104795700273 31294779189522078596775205)
  ·
    refine ⟨5867771098035389736895351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31294779189522078596775205 5867771098035389736895351)
    ·
      refine ⟨8801656647053084605343027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5867771098035389736895351 8801656647053084605343027)
      ·
        refine ⟨13202484970579626908014541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8801656647053084605343027 13202484970579626908014541)
        ·
          refine ⟨4950931863967360090505453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13202484970579626908014541 4950931863967360090505453)
          ·
            refine ⟨1856599448987760033939545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4950931863967360090505453 1856599448987760033939545)
            ·
              refine ⟨1392449586740820025454659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1856599448987760033939545 1392449586740820025454659)
              ·
                refine ⟨2088674380111230038181989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1392449586740820025454659 2088674380111230038181989)
                ·
                  refine ⟨391626446270855632159123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2088674380111230038181989 391626446270855632159123)
                  ·
                    rfl

theorem cell21_1716052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_1716052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716052 prefixEnd_1716052 := by exact prefixLift 1716052
  have htrace : WordTrace (prefixWord ++ tailWord_1716052) baseStart_1716052 baseEnd_1716052 := by
    simpa [prefixWord, tailWord_1716052, baseEnd_1716052] using wordTrace_append hprefix tailTrace_1716052
  have hstable : (prefixWord ++ tailWord_1716052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716052).length < 2 ^ (prefixWord ++ tailWord_1716052).sum := by decide
  have hdescent : baseEnd_1716052 < baseStart_1716052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716077 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 8]
def baseStart_1716077 : Nat := 118140960795 + 1716077 * 2 ^ 59
def prefixEnd_1716077 : Nat := 4983230072969 + 3 ^ 40 * 1716077 * 2
def baseEnd_1716077 : Nat := 391632151611461144242405

theorem tailTrace_1716077 : CollatzResearch.WordTrace tailWord_1716077 prefixEnd_1716077 391632151611461144242405 := by
  unfold tailWord_1716077
  simp only [CollatzResearch.WordTrace]
  refine ⟨62590470203953586463210485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41726980135969057642140323 62590470203953586463210485)
  ·
    refine ⟨5867856581620648730925983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62590470203953586463210485 5867856581620648730925983)
    ·
      refine ⟨8801784872430973096388975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5867856581620648730925983 8801784872430973096388975)
      ·
        refine ⟨13202677308646459644583463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8801784872430973096388975 13202677308646459644583463)
        ·
          refine ⟨19804015962969689466875195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13202677308646459644583463 19804015962969689466875195)
          ·
            refine ⟨29706023944454534200312793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19804015962969689466875195 29706023944454534200312793)
            ·
              refine ⟨22279517958340900650234595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29706023944454534200312793 22279517958340900650234595)
              ·
                refine ⟨33419276937511350975351893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22279517958340900650234595 33419276937511350975351893)
                ·
                  refine ⟨391632151611461144242405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33419276937511350975351893 391632151611461144242405)
                  ·
                    rfl

theorem cell21_1716077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_1716077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716077 prefixEnd_1716077 := by exact prefixLift 1716077
  have htrace : WordTrace (prefixWord ++ tailWord_1716077) baseStart_1716077 baseEnd_1716077 := by
    simpa [prefixWord, tailWord_1716077, baseEnd_1716077] using wordTrace_append hprefix tailTrace_1716077
  have hstable : (prefixWord ++ tailWord_1716077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716077).length < 2 ^ (prefixWord ++ tailWord_1716077).sum := by decide
  have hdescent : baseEnd_1716077 < baseStart_1716077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716125 : List Nat := [1, 4, 2, 1, 2, 3, 3, 5]
def baseStart_1716125 : Nat := 118140960795 + 1716125 * 2 ^ 59
def prefixEnd_1716125 : Nat := 4983230072969 + 3 ^ 40 * 1716125 * 2
def baseEnd_1716125 : Nat := 130547701955141242480769

theorem tailTrace_1716125 : CollatzResearch.WordTrace tailWord_1716125 prefixEnd_1716125 130547701955141242480769 := by
  unfold tailWord_1716125
  simp only [CollatzResearch.WordTrace]
  refine ⟨62592220907779690660957829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41728147271853127107305219 62592220907779690660957829)
  ·
    refine ⟨11736041420208691998929593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62592220907779690660957829 11736041420208691998929593)
    ·
      refine ⟨8802031065156518999197195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11736041420208691998929593 8802031065156518999197195)
      ·
        refine ⟨13203046597734778498795793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8802031065156518999197195 13203046597734778498795793)
        ·
          refine ⟨9902284948301083874096845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13203046597734778498795793 9902284948301083874096845)
          ·
            refine ⟨3713356855612906452786317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9902284948301083874096845 3713356855612906452786317)
            ·
              refine ⟨1392508820854839919794869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3713356855612906452786317 1392508820854839919794869)
              ·
                refine ⟨130547701955141242480769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1392508820854839919794869 130547701955141242480769)
                ·
                  rfl

theorem cell21_1716125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 5].length) (baseStart_1716125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716125 prefixEnd_1716125 := by exact prefixLift 1716125
  have htrace : WordTrace (prefixWord ++ tailWord_1716125) baseStart_1716125 baseEnd_1716125 := by
    simpa [prefixWord, tailWord_1716125, baseEnd_1716125] using wordTrace_append hprefix tailTrace_1716125
  have hstable : (prefixWord ++ tailWord_1716125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716125).length < 2 ^ (prefixWord ++ tailWord_1716125).sum := by decide
  have hdescent : baseEnd_1716125 < baseStart_1716125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716153 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 6]
def baseStart_1716153 : Nat := 118140960795 + 1716153 * 2 ^ 59
def prefixEnd_1716153 : Nat := 4983230072969 + 3 ^ 40 * 1716153 * 2
def baseEnd_1716153 : Nat := 391649495846901900975583

theorem tailTrace_1716153 : CollatzResearch.WordTrace tailWord_1716153 prefixEnd_1716153 391649495846901900975583 := by
  unfold tailWord_1716153
  simp only [CollatzResearch.WordTrace]
  refine ⟨62593242151678251442977113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41728828101118834295318075 62593242151678251442977113)
  ·
    refine ⟨46944931613758688582232835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62593242151678251442977113 46944931613758688582232835)
    ·
      refine ⟨70417397420638032873349253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46944931613758688582232835 70417397420638032873349253)
      ·
        refine ⟨13203262016369631163752985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70417397420638032873349253 13203262016369631163752985)
        ·
          refine ⟨9902446512277223372814739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13203262016369631163752985 9902446512277223372814739)
          ·
            refine ⟨14853669768415835059222109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9902446512277223372814739 14853669768415835059222109)
            ·
              refine ⟨5570126163155938147208291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14853669768415835059222109 5570126163155938147208291)
              ·
                refine ⟨8355189244733907220812437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5570126163155938147208291 8355189244733907220812437)
                ·
                  refine ⟨391649495846901900975583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8355189244733907220812437 391649495846901900975583)
                  ·
                    rfl

theorem cell21_1716153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_1716153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716153 prefixEnd_1716153 := by exact prefixLift 1716153
  have htrace : WordTrace (prefixWord ++ tailWord_1716153) baseStart_1716153 baseEnd_1716153 := by
    simpa [prefixWord, tailWord_1716153, baseEnd_1716153] using wordTrace_append hprefix tailTrace_1716153
  have hstable : (prefixWord ++ tailWord_1716153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716153).length < 2 ^ (prefixWord ++ tailWord_1716153).sum := by decide
  have hdescent : baseEnd_1716153 < baseStart_1716153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716167 : List Nat := [1, 1, 4, 1, 1, 2, 1, 10]
def baseStart_1716167 : Nat := 118140960795 + 1716167 * 2 ^ 59
def prefixEnd_1716167 : Nat := 4983230072969 + 3 ^ 40 * 1716167 * 2
def baseEnd_1716167 : Nat := 130550896945880329247407

theorem tailTrace_1716167 : CollatzResearch.WordTrace tailWord_1716167 prefixEnd_1716167 130550896945880329247407 := by
  unfold tailWord_1716167
  simp only [CollatzResearch.WordTrace]
  refine ⟨62593752773627531833986755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41729168515751687889324503 62593752773627531833986755)
  ·
    refine ⟨93890629160441297750980133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62593752773627531833986755 93890629160441297750980133)
    ·
      refine ⟨17604492967582743328308775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93890629160441297750980133 17604492967582743328308775)
      ·
        refine ⟨26406739451374114992463163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17604492967582743328308775 26406739451374114992463163)
        ·
          refine ⟨39610109177061172488694745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26406739451374114992463163 39610109177061172488694745)
          ·
            refine ⟨29707581882795879366521059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39610109177061172488694745 29707581882795879366521059)
            ·
              refine ⟨44561372824193819049781589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29707581882795879366521059 44561372824193819049781589)
              ·
                refine ⟨130550896945880329247407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44561372824193819049781589 130550896945880329247407)
                ·
                  rfl

theorem cell21_1716167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 10].length) (baseStart_1716167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716167 prefixEnd_1716167 := by exact prefixLift 1716167
  have htrace : WordTrace (prefixWord ++ tailWord_1716167) baseStart_1716167 baseEnd_1716167 := by
    simpa [prefixWord, tailWord_1716167, baseEnd_1716167] using wordTrace_append hprefix tailTrace_1716167
  have hstable : (prefixWord ++ tailWord_1716167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716167).length < 2 ^ (prefixWord ++ tailWord_1716167).sum := by decide
  have hdescent : baseEnd_1716167 < baseStart_1716167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716243 : List Nat := [1, 1, 1, 2, 1, 4, 4, 7]
def baseStart_1716243 : Nat := 118140960795 + 1716243 * 2 ^ 59
def prefixEnd_1716243 : Nat := 4983230072969 + 3 ^ 40 * 1716243 * 2
def baseEnd_1716243 : Nat := 130556678357693914825133

theorem tailTrace_1716243 : CollatzResearch.WordTrace tailWord_1716243 prefixEnd_1716243 130556678357693914825133 := by
  unfold tailWord_1716243
  simp only [CollatzResearch.WordTrace]
  refine ⟨62596524721352196813753383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41731016480901464542502255 62596524721352196813753383)
  ·
    refine ⟨93894787082028295220630075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62596524721352196813753383 93894787082028295220630075)
    ·
      refine ⟨140842180623042442830945113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93894787082028295220630075 140842180623042442830945113)
      ·
        refine ⟨105631635467281832123208835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140842180623042442830945113 105631635467281832123208835)
        ·
          refine ⟨158447453200922748184813253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105631635467281832123208835 158447453200922748184813253)
          ·
            refine ⟨29708897475173015284652485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158447453200922748184813253 29708897475173015284652485)
            ·
              refine ⟨5570418276594940365872341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29708897475173015284652485 5570418276594940365872341)
              ·
                refine ⟨130556678357693914825133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5570418276594940365872341 130556678357693914825133)
                ·
                  rfl

theorem cell21_1716243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 7].length) (baseStart_1716243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716243 prefixEnd_1716243 := by exact prefixLift 1716243
  have htrace : WordTrace (prefixWord ++ tailWord_1716243) baseStart_1716243 baseEnd_1716243 := by
    simpa [prefixWord, tailWord_1716243, baseEnd_1716243] using wordTrace_append hprefix tailTrace_1716243
  have hstable : (prefixWord ++ tailWord_1716243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716243).length < 2 ^ (prefixWord ++ tailWord_1716243).sum := by decide
  have hdescent : baseEnd_1716243 < baseStart_1716243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716260 : List Nat := [2, 3, 1, 4, 2, 9]
def baseStart_1716260 : Nat := 118140960795 + 1716260 * 2 ^ 59
def prefixEnd_1716260 : Nat := 4983230072969 + 3 ^ 40 * 1716260 * 2
def baseEnd_1716260 : Nat := 14506441285359018247853

theorem tailTrace_1716260 : CollatzResearch.WordTrace tailWord_1716260 prefixEnd_1716260 14506441285359018247853 := by
  unfold tailWord_1716260
  simp only [CollatzResearch.WordTrace]
  refine ⟨31298572381145304358561117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41731429841527072478081489 31298572381145304358561117)
  ·
    refine ⟨11736964642929489134460419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31298572381145304358561117 11736964642929489134460419)
    ·
      refine ⟨17605446964394233701690629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11736964642929489134460419 17605446964394233701690629)
      ·
        refine ⟨3301021305823918819066993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17605446964394233701690629 3301021305823918819066993)
        ·
          refine ⟨2475765979367939114300245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3301021305823918819066993 2475765979367939114300245)
          ·
            refine ⟨14506441285359018247853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2475765979367939114300245 14506441285359018247853)
            ·
              rfl

theorem cell21_1716260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 9].length) (baseStart_1716260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716260 prefixEnd_1716260 := by exact prefixLift 1716260
  have htrace : WordTrace (prefixWord ++ tailWord_1716260) baseStart_1716260 baseEnd_1716260 := by
    simpa [prefixWord, tailWord_1716260, baseEnd_1716260] using wordTrace_append hprefix tailTrace_1716260
  have hstable : (prefixWord ++ tailWord_1716260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716260).length < 2 ^ (prefixWord ++ tailWord_1716260).sum := by decide
  have hdescent : baseEnd_1716260 < baseStart_1716260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716266 : List Nat := [3, 1, 4, 1, 2, 3, 2, 2, 3]
def baseStart_1716266 : Nat := 118140960795 + 1716266 * 2 ^ 59
def prefixEnd_1716266 : Nat := 4983230072969 + 3 ^ 40 * 1716266 * 2
def baseEnd_1716266 : Nat := 391675283986438815592019

theorem tailTrace_1716266 : CollatzResearch.WordTrace tailWord_1716266 prefixEnd_1716266 391675283986438815592019 := by
  unfold tailWord_1716266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15649340900067217935460163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41731575733512581161227101 15649340900067217935460163)
  ·
    refine ⟨23474011350100826903190245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15649340900067217935460163 23474011350100826903190245)
    ·
      refine ⟨4401377128143905044348171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23474011350100826903190245 4401377128143905044348171)
      ·
        refine ⟨6602065692215857566522257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4401377128143905044348171 6602065692215857566522257)
        ·
          refine ⟨4951549269161893174891693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6602065692215857566522257 4951549269161893174891693)
          ·
            refine ⟨1856830975935709940584385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4951549269161893174891693 1856830975935709940584385)
            ·
              refine ⟨1392623231951782455438289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1856830975935709940584385 1392623231951782455438289)
              ·
                refine ⟨1044467423963836841578717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1392623231951782455438289 1044467423963836841578717)
                ·
                  refine ⟨391675283986438815592019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044467423963836841578717 391675283986438815592019)
                  ·
                    rfl

theorem cell21_1716266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_1716266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716266 prefixEnd_1716266 := by exact prefixLift 1716266
  have htrace : WordTrace (prefixWord ++ tailWord_1716266) baseStart_1716266 baseEnd_1716266 := by
    simpa [prefixWord, tailWord_1716266, baseEnd_1716266] using wordTrace_append hprefix tailTrace_1716266
  have hstable : (prefixWord ++ tailWord_1716266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716266).length < 2 ^ (prefixWord ++ tailWord_1716266).sum := by decide
  have hdescent : baseEnd_1716266 < baseStart_1716266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716294 : List Nat := [6, 1, 1, 1, 1, 1, 5, 5]
def baseStart_1716294 : Nat := 118140960795 + 1716294 * 2 ^ 59
def prefixEnd_1716294 : Nat := 4983230072969 + 3 ^ 40 * 1716294 * 2
def baseEnd_1716294 : Nat := 130560557989305663041765

theorem tailTrace_1716294 : CollatzResearch.WordTrace tailWord_1716294 prefixEnd_1716294 130560557989305663041765 := by
  unfold tailWord_1716294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1956199526380232266370623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41732256562778288349239957 1956199526380232266370623)
  ·
    refine ⟨2934299289570348399555935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1956199526380232266370623 2934299289570348399555935)
    ·
      refine ⟨4401448934355522599333903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2934299289570348399555935 4401448934355522599333903)
      ·
        refine ⟨6602173401533283899000855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4401448934355522599333903 6602173401533283899000855)
        ·
          refine ⟨9903260102299925848501283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6602173401533283899000855 9903260102299925848501283)
          ·
            refine ⟨14854890153449888772751925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9903260102299925848501283 14854890153449888772751925)
            ·
              refine ⟨1392645951885927072445493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14854890153449888772751925 1392645951885927072445493)
              ·
                refine ⟨130560557989305663041765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1392645951885927072445493 130560557989305663041765)
                ·
                  rfl

theorem cell21_1716294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_1716294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716294 prefixEnd_1716294 := by exact prefixLift 1716294
  have htrace : WordTrace (prefixWord ++ tailWord_1716294) baseStart_1716294 baseEnd_1716294 := by
    simpa [prefixWord, tailWord_1716294, baseEnd_1716294] using wordTrace_append hprefix tailTrace_1716294
  have hstable : (prefixWord ++ tailWord_1716294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716294).length < 2 ^ (prefixWord ++ tailWord_1716294).sum := by decide
  have hdescent : baseEnd_1716294 < baseStart_1716294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716381 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 6]
def baseStart_1716381 : Nat := 118140960795 + 1716381 * 2 ^ 59
def prefixEnd_1716381 : Nat := 4983230072969 + 3 ^ 40 * 1716381 * 2
def baseEnd_1716381 : Nat := 391701528553224171175117

theorem tailTrace_1716381 : CollatzResearch.WordTrace tailWord_1716381 prefixEnd_1716381 391701528553224171175117 := by
  unfold tailWord_1716381
  simp only [CollatzResearch.WordTrace]
  refine ⟨62601557994852246382276997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41734371996568164254851331 62601557994852246382276997)
  ·
    refine ⟨11737792124034796196676937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62601557994852246382276997 11737792124034796196676937)
    ·
      refine ⟨8803344093026097147507703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11737792124034796196676937 8803344093026097147507703)
      ·
        refine ⟨13205016139539145721261555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8803344093026097147507703 13205016139539145721261555)
        ·
          refine ⟨19807524209308718581892333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13205016139539145721261555 19807524209308718581892333)
          ·
            refine ⟨7427821578490769468209625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19807524209308718581892333 7427821578490769468209625)
            ·
              refine ⟨5570866183868077101157219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7427821578490769468209625 5570866183868077101157219)
              ·
                refine ⟨8356299275802115651735829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5570866183868077101157219 8356299275802115651735829)
                ·
                  refine ⟨391701528553224171175117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8356299275802115651735829 391701528553224171175117)
                  ·
                    rfl

theorem cell21_1716381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_1716381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716381 prefixEnd_1716381 := by exact prefixLift 1716381
  have htrace : WordTrace (prefixWord ++ tailWord_1716381) baseStart_1716381 baseEnd_1716381 := by
    simpa [prefixWord, tailWord_1716381, baseEnd_1716381] using wordTrace_append hprefix tailTrace_1716381
  have hstable : (prefixWord ++ tailWord_1716381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716381).length < 2 ^ (prefixWord ++ tailWord_1716381).sum := by decide
  have hdescent : baseEnd_1716381 < baseStart_1716381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716522 : List Nat := [3, 1, 4, 2, 2, 2, 2, 5]
def baseStart_1716522 : Nat := 118140960795 + 1716522 * 2 ^ 59
def prefixEnd_1716522 : Nat := 4983230072969 + 3 ^ 40 * 1716522 * 2
def baseEnd_1716522 : Nat := 130577902224746419774943

theorem tailTrace_1716522 : CollatzResearch.WordTrace tailWord_1716522 prefixEnd_1716522 130577902224746419774943 := by
  unfold tailWord_1716522
  simp only [CollatzResearch.WordTrace]
  refine ⟨15651675171835356865789955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41737800458227618308773213 15651675171835356865789955)
  ·
    refine ⟨23477512757753035298684933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15651675171835356865789955 23477512757753035298684933)
    ·
      refine ⟨4402033642078694118503425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23477512757753035298684933 4402033642078694118503425)
      ·
        refine ⟨3301525231559020588877569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4402033642078694118503425 3301525231559020588877569)
        ·
          refine ⟨2476143923669265441658177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3301525231559020588877569 2476143923669265441658177)
          ·
            refine ⟨1857107942751949081243633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2476143923669265441658177 1857107942751949081243633)
            ·
              refine ⟨1392830957063961810932725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1857107942751949081243633 1392830957063961810932725)
              ·
                refine ⟨130577902224746419774943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1392830957063961810932725 130577902224746419774943)
                ·
                  rfl

theorem cell21_1716522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_1716522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716522 prefixEnd_1716522 := by exact prefixLift 1716522
  have htrace : WordTrace (prefixWord ++ tailWord_1716522) baseStart_1716522 baseEnd_1716522 := by
    simpa [prefixWord, tailWord_1716522, baseEnd_1716522] using wordTrace_append hprefix tailTrace_1716522
  have hstable : (prefixWord ++ tailWord_1716522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716522).length < 2 ^ (prefixWord ++ tailWord_1716522).sum := by decide
  have hdescent : baseEnd_1716522 < baseStart_1716522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716564 : List Nat := [2, 4, 1, 1, 2, 3, 2, 6]
def baseStart_1716564 : Nat := 118140960795 + 1716564 * 2 ^ 59
def prefixEnd_1716564 : Nat := 4983230072969 + 3 ^ 40 * 1716564 * 2
def baseEnd_1716564 : Nat := 130581097215485506541581

theorem tailTrace_1716564 : CollatzResearch.WordTrace tailWord_1716564 prefixEnd_1716564 130581097215485506541581 := by
  unfold tailWord_1716564
  simp only [CollatzResearch.WordTrace]
  refine ⟨31304116276594634318094373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41738821702126179090792497 31304116276594634318094373)
  ·
    refine ⟨5869521801861493934642695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31304116276594634318094373 5869521801861493934642695)
    ·
      refine ⟨8804282702792240901964043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5869521801861493934642695 8804282702792240901964043)
      ·
        refine ⟨13206424054188361352946065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8804282702792240901964043 13206424054188361352946065)
        ·
          refine ⟨9904818040641271014709549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13206424054188361352946065 9904818040641271014709549)
          ·
            refine ⟨3714306765240476630516081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9904818040641271014709549 3714306765240476630516081)
            ·
              refine ⟨2785730073930357472887061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3714306765240476630516081 2785730073930357472887061)
              ·
                refine ⟨130581097215485506541581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2785730073930357472887061 130581097215485506541581)
                ·
                  rfl

theorem cell21_1716564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 6].length) (baseStart_1716564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716564 prefixEnd_1716564 := by exact prefixLift 1716564
  have htrace : WordTrace (prefixWord ++ tailWord_1716564) baseStart_1716564 baseEnd_1716564 := by
    simpa [prefixWord, tailWord_1716564, baseEnd_1716564] using wordTrace_append hprefix tailTrace_1716564
  have hstable : (prefixWord ++ tailWord_1716564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716564).length < 2 ^ (prefixWord ++ tailWord_1716564).sum := by decide
  have hdescent : baseEnd_1716564 < baseStart_1716564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716640 : List Nat := [2, 1, 1, 4, 1, 4, 3, 5]
def baseStart_1716640 : Nat := 118140960795 + 1716640 * 2 ^ 59
def prefixEnd_1716640 : Nat := 4983230072969 + 3 ^ 40 * 1716640 * 2
def baseEnd_1716640 : Nat := 130586878627299092119307

theorem tailTrace_1716640 : CollatzResearch.WordTrace tailWord_1716640 prefixEnd_1716640 130586878627299092119307 := by
  unfold tailWord_1716640
  simp only [CollatzResearch.WordTrace]
  refine ⟨31305502250456966807977687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41740669667275955743970249 31305502250456966807977687)
  ·
    refine ⟨46958253375685450211966531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31305502250456966807977687 46958253375685450211966531)
    ·
      refine ⟨70437380063528175317949797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46958253375685450211966531 70437380063528175317949797)
      ·
        refine ⟨13207008761911532872115587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70437380063528175317949797 13207008761911532872115587)
        ·
          refine ⟨19810513142867299308173381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13207008761911532872115587 19810513142867299308173381)
          ·
            refine ⟨3714471214287618620282509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19810513142867299308173381 3714471214287618620282509)
            ·
              refine ⟨1392926705357856982605941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3714471214287618620282509 1392926705357856982605941)
              ·
                refine ⟨130586878627299092119307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1392926705357856982605941 130586878627299092119307)
                ·
                  rfl

theorem cell21_1716640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 5].length) (baseStart_1716640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716640 prefixEnd_1716640 := by exact prefixLift 1716640
  have htrace : WordTrace (prefixWord ++ tailWord_1716640) baseStart_1716640 baseEnd_1716640 := by
    simpa [prefixWord, tailWord_1716640, baseEnd_1716640] using wordTrace_append hprefix tailTrace_1716640
  have hstable : (prefixWord ++ tailWord_1716640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716640).length < 2 ^ (prefixWord ++ tailWord_1716640).sum := by decide
  have hdescent : baseEnd_1716640 < baseStart_1716640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716778 : List Nat := [3, 1, 4, 1, 1, 3, 2, 2, 4]
def baseStart_1716778 : Nat := 118140960795 + 1716778 * 2 ^ 59
def prefixEnd_1716778 : Nat := 4983230072969 + 3 ^ 40 * 1716778 * 2
def baseEnd_1716778 : Nat := 391792129362039703057639

theorem tailTrace_1716778 : CollatzResearch.WordTrace tailWord_1716778 prefixEnd_1716778 391792129362039703057639 := by
  unfold tailWord_1716778
  simp only [CollatzResearch.WordTrace]
  refine ⟨15654009443603495796119747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41744025182942655456319325 15654009443603495796119747)
  ·
    refine ⟨23481014165405243694179621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15654009443603495796119747 23481014165405243694179621)
    ·
      refine ⟨4402690156013483192658679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23481014165405243694179621 4402690156013483192658679)
      ·
        refine ⟨6604035234020224788988019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4402690156013483192658679 6604035234020224788988019)
        ·
          refine ⟨9906052851030337183482029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6604035234020224788988019 9906052851030337183482029)
          ·
            refine ⟨3714769819136376443805761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9906052851030337183482029 3714769819136376443805761)
            ·
              refine ⟨2786077364352282332854321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3714769819136376443805761 2786077364352282332854321)
              ·
                refine ⟨2089558023264211749640741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2786077364352282332854321 2089558023264211749640741)
                ·
                  refine ⟨391792129362039703057639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2089558023264211749640741 391792129362039703057639)
                  ·
                    rfl

theorem cell21_1716778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_1716778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716778 prefixEnd_1716778 := by exact prefixLift 1716778
  have htrace : WordTrace (prefixWord ++ tailWord_1716778) baseStart_1716778 baseEnd_1716778 := by
    simpa [prefixWord, tailWord_1716778, baseEnd_1716778] using wordTrace_append hprefix tailTrace_1716778
  have hstable : (prefixWord ++ tailWord_1716778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716778).length < 2 ^ (prefixWord ++ tailWord_1716778).sum := by decide
  have hdescent : baseEnd_1716778 < baseStart_1716778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716823 : List Nat := [1, 1, 3, 2, 2, 2, 4, 3, 3]
def baseStart_1716823 : Nat := 118140960795 + 1716823 * 2 ^ 59
def prefixEnd_1716823 : Nat := 4983230072969 + 3 ^ 40 * 1716823 * 2
def baseEnd_1716823 : Nat := 391802398975129624807547

theorem tailTrace_1716823 : CollatzResearch.WordTrace tailWord_1716823 prefixEnd_1716823 391802398975129624807547 := by
  unfold tailWord_1716823
  simp only [CollatzResearch.WordTrace]
  refine ⟨62617679059250955869867123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41745119372833970579911415 62617679059250955869867123)
  ·
    refine ⟨93926518588876433804800685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62617679059250955869867123 93926518588876433804800685)
    ·
      refine ⟨35222444470828662676800257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93926518588876433804800685 35222444470828662676800257)
      ·
        refine ⟨26416833353121497007600193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35222444470828662676800257 26416833353121497007600193)
        ·
          refine ⟨19812625014841122755700145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26416833353121497007600193 19812625014841122755700145)
          ·
            refine ⟨14859468761130842066775109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19812625014841122755700145 14859468761130842066775109)
            ·
              refine ⟨2786150392712032887520333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14859468761130842066775109 2786150392712032887520333)
              ·
                refine ⟨1044806397267012332820125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2786150392712032887520333 1044806397267012332820125)
                ·
                  refine ⟨391802398975129624807547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044806397267012332820125 391802398975129624807547)
                  ·
                    rfl

theorem cell21_1716823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 3].length) (baseStart_1716823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716823 prefixEnd_1716823 := by exact prefixLift 1716823
  have htrace : WordTrace (prefixWord ++ tailWord_1716823) baseStart_1716823 baseEnd_1716823 := by
    simpa [prefixWord, tailWord_1716823, baseEnd_1716823] using wordTrace_append hprefix tailTrace_1716823
  have hstable : (prefixWord ++ tailWord_1716823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716823).length < 2 ^ (prefixWord ++ tailWord_1716823).sum := by decide
  have hdescent : baseEnd_1716823 < baseStart_1716823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716837 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 6]
def baseStart_1716837 : Nat := 118140960795 + 1716837 * 2 ^ 59
def prefixEnd_1716837 : Nat := 4983230072969 + 3 ^ 40 * 1716837 * 2
def baseEnd_1716837 : Nat := 391805593965868711574185

theorem tailTrace_1716837 : CollatzResearch.WordTrace tailWord_1716837 prefixEnd_1716837 391805593965868711574185 := by
  unfold tailWord_1716837
  simp only [CollatzResearch.WordTrace]
  refine ⟨62618189681200236260876765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41745459787466824173917843 62618189681200236260876765)
  ·
    refine ⟨23481821130450088597828787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62618189681200236260876765 23481821130450088597828787)
    ·
      refine ⟨35222731695675132896743181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23481821130450088597828787 35222731695675132896743181)
      ·
        refine ⟨13208524385878174836278693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35222731695675132896743181 13208524385878174836278693)
        ·
          refine ⟨2476598322352157781802255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13208524385878174836278693 2476598322352157781802255)
          ·
            refine ⟨3714897483528236672703383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476598322352157781802255 3714897483528236672703383)
            ·
              refine ⟨5572346225292355009055075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3714897483528236672703383 5572346225292355009055075)
              ·
                refine ⟨8358519337938532513582613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5572346225292355009055075 8358519337938532513582613)
                ·
                  refine ⟨391805593965868711574185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8358519337938532513582613 391805593965868711574185)
                  ·
                    rfl

theorem cell21_1716837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_1716837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716837 prefixEnd_1716837 := by exact prefixLift 1716837
  have htrace : WordTrace (prefixWord ++ tailWord_1716837) baseStart_1716837 baseEnd_1716837 := by
    simpa [prefixWord, tailWord_1716837, baseEnd_1716837] using wordTrace_append hprefix tailTrace_1716837
  have hstable : (prefixWord ++ tailWord_1716837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716837).length < 2 ^ (prefixWord ++ tailWord_1716837).sum := by decide
  have hdescent : baseEnd_1716837 < baseStart_1716837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716868 : List Nat := [2, 3, 2, 1, 3, 1, 4, 5]
def baseStart_1716868 : Nat := 118140960795 + 1716868 * 2 ^ 59
def prefixEnd_1716868 : Nat := 4983230072969 + 3 ^ 40 * 1716868 * 2
def baseEnd_1716868 : Nat := 130604222862739848852485

theorem tailTrace_1716868 : CollatzResearch.WordTrace tailWord_1716868 prefixEnd_1716868 130604222862739848852485 := by
  unfold tailWord_1716868
  simp only [CollatzResearch.WordTrace]
  refine ⟨31309660172043964277627629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41746213562725285703503505 31309660172043964277627629)
  ·
    refine ⟨11741122564516486604110361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31309660172043964277627629 11741122564516486604110361)
    ·
      refine ⟨8805841923387364953082771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11741122564516486604110361 8805841923387364953082771)
      ·
        refine ⟨13208762885081047429624157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8805841923387364953082771 13208762885081047429624157)
        ·
          refine ⟨4953286081905392786109059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13208762885081047429624157 4953286081905392786109059)
          ·
            refine ⟨7429929122858089179163589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4953286081905392786109059 7429929122858089179163589)
            ·
              refine ⟨1393111710535891721093173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7429929122858089179163589 1393111710535891721093173)
              ·
                refine ⟨130604222862739848852485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1393111710535891721093173 130604222862739848852485)
                ·
                  rfl

theorem cell21_1716868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 5].length) (baseStart_1716868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716868 prefixEnd_1716868 := by exact prefixLift 1716868
  have htrace : WordTrace (prefixWord ++ tailWord_1716868) baseStart_1716868 baseEnd_1716868 := by
    simpa [prefixWord, tailWord_1716868, baseEnd_1716868] using wordTrace_append hprefix tailTrace_1716868
  have hstable : (prefixWord ++ tailWord_1716868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716868).length < 2 ^ (prefixWord ++ tailWord_1716868).sum := by decide
  have hdescent : baseEnd_1716868 < baseStart_1716868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716986 : List Nat := [3, 1, 1, 1, 1, 3, 2, 9]
def baseStart_1716986 : Nat := 118140960795 + 1716986 * 2 ^ 59
def prefixEnd_1716986 : Nat := 4983230072969 + 3 ^ 40 * 1716986 * 2
def baseEnd_1716986 : Nat := 130613199265292521196849

theorem tailTrace_1716986 : CollatzResearch.WordTrace tailWord_1716986 prefixEnd_1716986 130613199265292521196849 := by
  unfold tailWord_1716986
  simp only [CollatzResearch.WordTrace]
  refine ⟨15655906039415108677012703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41749082771773623138700541 15655906039415108677012703)
  ·
    refine ⟨23483859059122663015519055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15655906039415108677012703 23483859059122663015519055)
    ·
      refine ⟨35225788588683994523278583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23483859059122663015519055 35225788588683994523278583)
      ·
        refine ⟨52838682883025991784917875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35225788588683994523278583 52838682883025991784917875)
        ·
          refine ⟨79258024324538987677376813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52838682883025991784917875 79258024324538987677376813)
          ·
            refine ⟨29721759121702120379016305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79258024324538987677376813 29721759121702120379016305)
            ·
              refine ⟨22291319341276590284262229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29721759121702120379016305 22291319341276590284262229)
              ·
                refine ⟨130613199265292521196849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22291319341276590284262229 130613199265292521196849)
                ·
                  rfl

theorem cell21_1716986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_1716986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1716986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1716986 prefixEnd_1716986 := by exact prefixLift 1716986
  have htrace : WordTrace (prefixWord ++ tailWord_1716986) baseStart_1716986 baseEnd_1716986 := by
    simpa [prefixWord, tailWord_1716986, baseEnd_1716986] using wordTrace_append hprefix tailTrace_1716986
  have hstable : (prefixWord ++ tailWord_1716986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716986).length < 2 ^ (prefixWord ++ tailWord_1716986).sum := by decide
  have hdescent : baseEnd_1716986 < baseStart_1716986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717037 : List Nat := [1, 5, 3, 2, 1, 1, 1, 7]
def baseStart_1717037 : Nat := 118140960795 + 1717037 * 2 ^ 59
def prefixEnd_1717037 : Nat := 4983230072969 + 3 ^ 40 * 1717037 * 2
def baseEnd_1717037 : Nat := 130617078896904269413481

theorem tailTrace_1717037 : CollatzResearch.WordTrace tailWord_1717037 prefixEnd_1717037 130617078896904269413481 := by
  unfold tailWord_1717037
  simp only [CollatzResearch.WordTrace]
  refine ⟨62625484280475670418157365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41750322853650446945438243 62625484280475670418157365)
  ·
    refine ⟨5871139151294594101702253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62625484280475670418157365 5871139151294594101702253)
    ·
      refine ⟨2201677181735472788138345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5871139151294594101702253 2201677181735472788138345)
      ·
        refine ⟨1651257886301604591103759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2201677181735472788138345 1651257886301604591103759)
        ·
          refine ⟨2476886829452406886655639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1651257886301604591103759 2476886829452406886655639)
          ·
            refine ⟨3715330244178610329983459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476886829452406886655639 3715330244178610329983459)
            ·
              refine ⟨5572995366267915494975189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3715330244178610329983459 5572995366267915494975189)
              ·
                refine ⟨130617078896904269413481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5572995366267915494975189 130617078896904269413481)
                ·
                  rfl

theorem cell21_1717037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 7].length) (baseStart_1717037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717037 prefixEnd_1717037 := by exact prefixLift 1717037
  have htrace : WordTrace (prefixWord ++ tailWord_1717037) baseStart_1717037 baseEnd_1717037 := by
    simpa [prefixWord, tailWord_1717037, baseEnd_1717037] using wordTrace_append hprefix tailTrace_1717037
  have hstable : (prefixWord ++ tailWord_1717037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717037).length < 2 ^ (prefixWord ++ tailWord_1717037).sum := by decide
  have hdescent : baseEnd_1717037 < baseStart_1717037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717068 : List Nat := [2, 2, 1, 3, 3, 2, 3, 2, 3]
def baseStart_1717068 : Nat := 118140960795 + 1717068 * 2 ^ 59
def prefixEnd_1717068 : Nat := 4983230072969 + 3 ^ 40 * 1717068 * 2
def baseEnd_1717068 : Nat := 391858311313063643223713

theorem tailTrace_1717068 : CollatzResearch.WordTrace tailWord_1717068 prefixEnd_1717068 391858311313063643223713 := by
  unfold tailWord_1717068
  simp only [CollatzResearch.WordTrace]
  refine ⟨31313307471681681356267929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41751076628908908475023905 31313307471681681356267929)
  ·
    refine ⟨23484980603761261017200947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31313307471681681356267929 23484980603761261017200947)
    ·
      refine ⟨35227470905641891525801421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23484980603761261017200947 35227470905641891525801421)
      ·
        refine ⟨13210301589615709322175533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35227470905641891525801421 13210301589615709322175533)
        ·
          refine ⟨4953863096105890995815825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13210301589615709322175533 4953863096105890995815825)
          ·
            refine ⟨3715397322079418246861869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4953863096105890995815825 3715397322079418246861869)
            ·
              refine ⟨1393273995779781842573201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3715397322079418246861869 1393273995779781842573201)
              ·
                refine ⟨1044955496834836381929901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1393273995779781842573201 1044955496834836381929901)
                ·
                  refine ⟨391858311313063643223713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044955496834836381929901 391858311313063643223713)
                  ·
                    rfl

theorem cell21_1717068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_1717068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717068 prefixEnd_1717068 := by exact prefixLift 1717068
  have htrace : WordTrace (prefixWord ++ tailWord_1717068) baseStart_1717068 baseEnd_1717068 := by
    simpa [prefixWord, tailWord_1717068, baseEnd_1717068] using wordTrace_append hprefix tailTrace_1717068
  have hstable : (prefixWord ++ tailWord_1717068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717068).length < 2 ^ (prefixWord ++ tailWord_1717068).sum := by decide
  have hdescent : baseEnd_1717068 < baseStart_1717068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717079 : List Nat := [1, 1, 3, 2, 4, 2, 2, 6]
def baseStart_1717079 : Nat := 118140960795 + 1717079 * 2 ^ 59
def prefixEnd_1717079 : Nat := 4983230072969 + 3 ^ 40 * 1717079 * 2
def baseEnd_1717079 : Nat := 130620273887643356180119

theorem tailTrace_1717079 : CollatzResearch.WordTrace tailWord_1717079 prefixEnd_1717079 130620273887643356180119 := by
  unfold tailWord_1717079
  simp only [CollatzResearch.WordTrace]
  refine ⟨62627016146323511591186291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41751344097549007727457527 62627016146323511591186291)
  ·
    refine ⟨93940524219485267386779437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62627016146323511591186291 93940524219485267386779437)
    ·
      refine ⟨35227696582306975270042289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93940524219485267386779437 35227696582306975270042289)
      ·
        refine ⟨26420772436730231452531717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35227696582306975270042289 26420772436730231452531717)
        ·
          refine ⟨4953894831886918397349697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26420772436730231452531717 4953894831886918397349697)
          ·
            refine ⟨3715421123915188798012273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4953894831886918397349697 3715421123915188798012273)
            ·
              refine ⟨2786565842936391598509205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3715421123915188798012273 2786565842936391598509205)
              ·
                refine ⟨130620273887643356180119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2786565842936391598509205 130620273887643356180119)
                ·
                  rfl

theorem cell21_1717079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 6].length) (baseStart_1717079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717079 prefixEnd_1717079 := by exact prefixLift 1717079
  have htrace : WordTrace (prefixWord ++ tailWord_1717079) baseStart_1717079 baseEnd_1717079 := by
    simpa [prefixWord, tailWord_1717079, baseEnd_1717079] using wordTrace_append hprefix tailTrace_1717079
  have hstable : (prefixWord ++ tailWord_1717079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717079).length < 2 ^ (prefixWord ++ tailWord_1717079).sum := by decide
  have hdescent : baseEnd_1717079 < baseStart_1717079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717082 : List Nat := [3, 1, 1, 2, 1, 6, 2, 1, 4]
def baseStart_1717082 : Nat := 118140960795 + 1717082 * 2 ^ 59
def prefixEnd_1717082 : Nat := 4983230072969 + 3 ^ 40 * 1717082 * 2
def baseEnd_1717082 : Nat := 391861506303802729990351

theorem tailTrace_1717082 : CollatzResearch.WordTrace tailWord_1717082 prefixEnd_1717082 391861506303802729990351 := by
  unfold tailWord_1717082
  simp only [CollatzResearch.WordTrace]
  refine ⟨15656781391328160775886375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41751417043541762069030333 15656781391328160775886375)
  ·
    refine ⟨23485172086992241163829563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15656781391328160775886375 23485172086992241163829563)
    ·
      refine ⟨35227758130488361745744345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23485172086992241163829563 35227758130488361745744345)
      ·
        refine ⟨26420818597866271309308259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35227758130488361745744345 26420818597866271309308259)
        ·
          refine ⟨39631227896799406963962389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26420818597866271309308259 39631227896799406963962389)
          ·
            refine ⟨1857713807662472201435737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39631227896799406963962389 1857713807662472201435737)
            ·
              refine ⟨1393285355746854151076803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1857713807662472201435737 1393285355746854151076803)
              ·
                refine ⟨2089928033620281226615205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1393285355746854151076803 2089928033620281226615205)
                ·
                  refine ⟨391861506303802729990351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2089928033620281226615205 391861506303802729990351)
                  ·
                    rfl

theorem cell21_1717082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_1717082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717082 prefixEnd_1717082 := by exact prefixLift 1717082
  have htrace : WordTrace (prefixWord ++ tailWord_1717082) baseStart_1717082 baseEnd_1717082 := by
    simpa [prefixWord, tailWord_1717082, baseEnd_1717082] using wordTrace_append hprefix tailTrace_1717082
  have hstable : (prefixWord ++ tailWord_1717082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717082).length < 2 ^ (prefixWord ++ tailWord_1717082).sum := by decide
  have hdescent : baseEnd_1717082 < baseStart_1717082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717093 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 5]
def baseStart_1717093 : Nat := 118140960795 + 1717093 * 2 ^ 59
def prefixEnd_1717093 : Nat := 4983230072969 + 3 ^ 40 * 1717093 * 2
def baseEnd_1717093 : Nat := 391864016653669155306995

theorem tailTrace_1717093 : CollatzResearch.WordTrace tailWord_1717093 prefixEnd_1717093 391864016653669155306995 := by
  unfold tailWord_1717093
  simp only [CollatzResearch.WordTrace]
  refine ⟨62627526768272791982195933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41751684512181861321463955 62627526768272791982195933)
  ·
    refine ⟨23485322538102296993323475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62627526768272791982195933 23485322538102296993323475)
    ·
      refine ⟨35227983807153445489985213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23485322538102296993323475 35227983807153445489985213)
      ·
        refine ⟨13210493927682542058744455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35227983807153445489985213 13210493927682542058744455)
        ·
          refine ⟨19815740891523813088116683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13210493927682542058744455 19815740891523813088116683)
          ·
            refine ⟨29723611337285719632175025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19815740891523813088116683 29723611337285719632175025)
            ·
              refine ⟨22292708502964289724131269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29723611337285719632175025 22292708502964289724131269)
              ·
                refine ⟨4179882844305804323274613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22292708502964289724131269 4179882844305804323274613)
                ·
                  refine ⟨391864016653669155306995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4179882844305804323274613 391864016653669155306995)
                  ·
                    rfl

theorem cell21_1717093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_1717093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717093 prefixEnd_1717093 := by exact prefixLift 1717093
  have htrace : WordTrace (prefixWord ++ tailWord_1717093) baseStart_1717093 baseEnd_1717093 := by
    simpa [prefixWord, tailWord_1717093, baseEnd_1717093] using wordTrace_append hprefix tailTrace_1717093
  have hstable : (prefixWord ++ tailWord_1717093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717093).length < 2 ^ (prefixWord ++ tailWord_1717093).sum := by decide
  have hdescent : baseEnd_1717093 < baseStart_1717093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717107 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 8]
def baseStart_1717107 : Nat := 118140960795 + 1717107 * 2 ^ 59
def prefixEnd_1717107 : Nat := 4983230072969 + 3 ^ 40 * 1717107 * 2
def baseEnd_1717107 : Nat := 391867211644408242073633

theorem tailTrace_1717107 : CollatzResearch.WordTrace tailWord_1717107 prefixEnd_1717107 391867211644408242073633 := by
  unfold tailWord_1717107
  simp only [CollatzResearch.WordTrace]
  refine ⟨62628037390222072373205575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41752024926814714915470383 62628037390222072373205575)
  ·
    refine ⟨93942056085333108559808363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62628037390222072373205575 93942056085333108559808363)
    ·
      refine ⟨140913084127999662839712545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93942056085333108559808363 140913084127999662839712545)
      ·
        refine ⟨105684813095999747129784409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140913084127999662839712545 105684813095999747129784409)
        ·
          refine ⟨79263609821999810347338307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105684813095999747129784409 79263609821999810347338307)
          ·
            refine ⟨118895414732999715521007461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79263609821999810347338307 118895414732999715521007461)
            ·
              refine ⟨22292890262437446660188899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118895414732999715521007461 22292890262437446660188899)
              ·
                refine ⟨33439335393656169990283349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22292890262437446660188899 33439335393656169990283349)
                ·
                  refine ⟨391867211644408242073633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33439335393656169990283349 391867211644408242073633)
                  ·
                    rfl

theorem cell21_1717107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 8].length) (baseStart_1717107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717107 prefixEnd_1717107 := by exact prefixLift 1717107
  have htrace : WordTrace (prefixWord ++ tailWord_1717107) baseStart_1717107 baseEnd_1717107 := by
    simpa [prefixWord, tailWord_1717107, baseEnd_1717107] using wordTrace_append hprefix tailTrace_1717107
  have hstable : (prefixWord ++ tailWord_1717107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717107).length < 2 ^ (prefixWord ++ tailWord_1717107).sum := by decide
  have hdescent : baseEnd_1717107 < baseStart_1717107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717127 : List Nat := [1, 1, 4, 2, 3, 2, 1, 4, 3]
def baseStart_1717127 : Nat := 118140960795 + 1717127 * 2 ^ 59
def prefixEnd_1717127 : Nat := 4983230072969 + 3 ^ 40 * 1717127 * 2
def baseEnd_1717127 : Nat := 391871775916892651740259

theorem tailTrace_1717127 : CollatzResearch.WordTrace tailWord_1717127 prefixEnd_1717127 391871775916892651740259 := by
  unfold tailWord_1717127
  simp only [CollatzResearch.WordTrace]
  refine ⟨62628766850149615788933635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41752511233433077192622423 62628766850149615788933635)
  ·
    refine ⟨93943150275224423683400453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62628766850149615788933635 93943150275224423683400453)
    ·
      refine ⟨17614340676604579440637585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93943150275224423683400453 17614340676604579440637585)
      ·
        refine ⟨13210755507453434580478189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17614340676604579440637585 13210755507453434580478189)
        ·
          refine ⟨4954033315295037967679321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13210755507453434580478189 4954033315295037967679321)
          ·
            refine ⟨3715524986471278475759491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4954033315295037967679321 3715524986471278475759491)
            ·
              refine ⟨5573287479706917713639237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3715524986471278475759491 5573287479706917713639237)
              ·
                refine ⟨1044991402445047071307357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5573287479706917713639237 1044991402445047071307357)
                ·
                  refine ⟨391871775916892651740259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044991402445047071307357 391871775916892651740259)
                  ·
                    rfl

theorem cell21_1717127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 3].length) (baseStart_1717127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717127 prefixEnd_1717127 := by exact prefixLift 1717127
  have htrace : WordTrace (prefixWord ++ tailWord_1717127) baseStart_1717127 baseEnd_1717127 := by
    simpa [prefixWord, tailWord_1717127, baseEnd_1717127] using wordTrace_append hprefix tailTrace_1717127
  have hstable : (prefixWord ++ tailWord_1717127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717127).length < 2 ^ (prefixWord ++ tailWord_1717127).sum := by decide
  have hdescent : baseEnd_1717127 < baseStart_1717127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717172 : List Nat := [2, 5, 2, 1, 1, 2, 8]
def baseStart_1717172 : Nat := 118140960795 + 1717172 * 2 ^ 59
def prefixEnd_1717172 : Nat := 4983230072969 + 3 ^ 40 * 1717172 * 2
def baseEnd_1717172 : Nat := 43542449503331397054463

theorem tailTrace_1717172 : CollatzResearch.WordTrace tailWord_1717172 prefixEnd_1717172 43542449503331397054463 := by
  unfold tailWord_1717172
  simp only [CollatzResearch.WordTrace]
  refine ⟨31315204067493294237160885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41753605423324392316214513 31315204067493294237160885)
  ·
    refine ⟨2935800381327496334733833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31315204067493294237160885 2935800381327496334733833)
    ·
      refine ⟨2201850285995622251050375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2935800381327496334733833 2201850285995622251050375)
      ·
        refine ⟨3302775428993433376575563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2201850285995622251050375 3302775428993433376575563)
        ·
          refine ⟨4954163143490150064863345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3302775428993433376575563 4954163143490150064863345)
          ·
            refine ⟨3715622357617612548647509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4954163143490150064863345 3715622357617612548647509)
            ·
              refine ⟨43542449503331397054463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3715622357617612548647509 43542449503331397054463)
              ·
                rfl

theorem cell21_1717172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 8].length) (baseStart_1717172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717172 prefixEnd_1717172 := by exact prefixLift 1717172
  have htrace : WordTrace (prefixWord ++ tailWord_1717172) baseStart_1717172 baseEnd_1717172 := by
    simpa [prefixWord, tailWord_1717172, baseEnd_1717172] using wordTrace_append hprefix tailTrace_1717172
  have hstable : (prefixWord ++ tailWord_1717172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717172).length < 2 ^ (prefixWord ++ tailWord_1717172).sum := by decide
  have hdescent : baseEnd_1717172 < baseStart_1717172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717237 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 5]
def baseStart_1717237 : Nat := 118140960795 + 1717237 * 2 ^ 59
def prefixEnd_1717237 : Nat := 4983230072969 + 3 ^ 40 * 1717237 * 2
def baseEnd_1717237 : Nat := 391896879415556904906701

theorem tailTrace_1717237 : CollatzResearch.WordTrace tailWord_1717237 prefixEnd_1717237 391896879415556904906701 := by
  unfold tailWord_1717237
  simp only [CollatzResearch.WordTrace]
  refine ⟨62632778879751104575437965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41755185919834069716958643 62632778879751104575437965)
  ·
    refine ⟨23487292079906664215789237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62632778879751104575437965 23487292079906664215789237)
    ·
      refine ⟨2201933632491249770230241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23487292079906664215789237 2201933632491249770230241)
      ·
        refine ⟨1651450224368437327672681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2201933632491249770230241 1651450224368437327672681)
        ·
          refine ⟨1238587668276327995754511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1651450224368437327672681 1238587668276327995754511)
          ·
            refine ⟨1857881502414491993631767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238587668276327995754511 1857881502414491993631767)
            ·
              refine ⟨2786822253621737990447651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1857881502414491993631767 2786822253621737990447651)
              ·
                refine ⟨4180233380432606985671477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2786822253621737990447651 4180233380432606985671477)
                ·
                  refine ⟨391896879415556904906701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4180233380432606985671477 391896879415556904906701)
                  ·
                    rfl

theorem cell21_1717237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_1717237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717237 prefixEnd_1717237 := by exact prefixLift 1717237
  have htrace : WordTrace (prefixWord ++ tailWord_1717237) baseStart_1717237 baseEnd_1717237 := by
    simpa [prefixWord, tailWord_1717237, baseEnd_1717237] using wordTrace_append hprefix tailTrace_1717237
  have hstable : (prefixWord ++ tailWord_1717237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717237).length < 2 ^ (prefixWord ++ tailWord_1717237).sum := by decide
  have hdescent : baseEnd_1717237 < baseStart_1717237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717290 : List Nat := [3, 1, 4, 1, 12]
def baseStart_1717290 : Nat := 118140960795 + 1717290 * 2 ^ 59
def prefixEnd_1717290 : Nat := 4983230072969 + 3 ^ 40 * 1717290 * 2
def baseEnd_1717290 : Nat := 4838382404168402352139

theorem tailTrace_1717290 : CollatzResearch.WordTrace tailWord_1717290 prefixEnd_1717290 4838382404168402352139 := by
  unfold tailWord_1717290
  simp only [CollatzResearch.WordTrace]
  refine ⟨15658677987139773656779331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41756474632372729751411549 15658677987139773656779331)
  ·
    refine ⟨23488016980709660485168997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15658677987139773656779331 23488016980709660485168997)
    ·
      refine ⟨4404003183883061340969187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23488016980709660485168997 4404003183883061340969187)
      ·
        refine ⟨6606004775824592011453781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4404003183883061340969187 6606004775824592011453781)
        ·
          refine ⟨4838382404168402352139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6606004775824592011453781 4838382404168402352139)
          ·
            rfl

theorem cell21_1717290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 12].length) (baseStart_1717290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717290 prefixEnd_1717290 := by exact prefixLift 1717290
  have htrace : WordTrace (prefixWord ++ tailWord_1717290) baseStart_1717290 baseEnd_1717290 := by
    simpa [prefixWord, tailWord_1717290, baseEnd_1717290] using wordTrace_append hprefix tailTrace_1717290
  have hstable : (prefixWord ++ tailWord_1717290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717290).length < 2 ^ (prefixWord ++ tailWord_1717290).sum := by decide
  have hdescent : baseEnd_1717290 < baseStart_1717290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717335 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 6]
def baseStart_1717335 : Nat := 118140960795 + 1717335 * 2 ^ 59
def prefixEnd_1717335 : Nat := 4983230072969 + 3 ^ 40 * 1717335 * 2
def baseEnd_1717335 : Nat := 391919244350730512273167

theorem tailTrace_1717335 : CollatzResearch.WordTrace tailWord_1717335 prefixEnd_1717335 391919244350730512273167 := by
  unfold tailWord_1717335
  simp only [CollatzResearch.WordTrace]
  refine ⟨62636353233396067312505459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41757568822264044875003639 62636353233396067312505459)
  ·
    refine ⟨93954529850094100968758189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62636353233396067312505459 93954529850094100968758189)
    ·
      refine ⟨35232948693785287863284321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93954529850094100968758189 35232948693785287863284321)
      ·
        refine ⟨26424711520338965897463241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35232948693785287863284321 26424711520338965897463241)
        ·
          refine ⟨19818533640254224423097431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26424711520338965897463241 19818533640254224423097431)
          ·
            refine ⟨29727800460381336634646147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19818533640254224423097431 29727800460381336634646147)
            ·
              refine ⟨44591700690572004951969221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29727800460381336634646147 44591700690572004951969221)
              ·
                refine ⟨8360943879482250928494229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44591700690572004951969221 8360943879482250928494229)
                ·
                  refine ⟨391919244350730512273167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8360943879482250928494229 391919244350730512273167)
                  ·
                    rfl

theorem cell21_1717335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 6].length) (baseStart_1717335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717335 prefixEnd_1717335 := by exact prefixLift 1717335
  have htrace : WordTrace (prefixWord ++ tailWord_1717335) baseStart_1717335 baseEnd_1717335 := by
    simpa [prefixWord, tailWord_1717335, baseEnd_1717335] using wordTrace_append hprefix tailTrace_1717335
  have hstable : (prefixWord ++ tailWord_1717335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717335).length < 2 ^ (prefixWord ++ tailWord_1717335).sum := by decide
  have hdescent : baseEnd_1717335 < baseStart_1717335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717490 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 5]
def baseStart_1717490 : Nat := 118140960795 + 1717490 * 2 ^ 59
def prefixEnd_1717490 : Nat := 4983230072969 + 3 ^ 40 * 1717490 * 2
def baseEnd_1717490 : Nat := 391954617462484687189517

theorem tailTrace_1717490 : CollatzResearch.WordTrace tailWord_1717490 prefixEnd_1717490 391954617462484687189517 := by
  unfold tailWord_1717490
  simp only [CollatzResearch.WordTrace]
  refine ⟨15660501636958632196099481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41761337698556352522931949 15660501636958632196099481)
  ·
    refine ⟨11745376227718974147074611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15660501636958632196099481 11745376227718974147074611)
    ·
      refine ⟨17618064341578461220611917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11745376227718974147074611 17618064341578461220611917)
      ·
        refine ⟨6606774128091922957729469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17618064341578461220611917 6606774128091922957729469)
        ·
          refine ⟨2477540298034471109148551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6606774128091922957729469 2477540298034471109148551)
          ·
            refine ⟨3716310447051706663722827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2477540298034471109148551 3716310447051706663722827)
            ·
              refine ⟨5574465670577559995584241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3716310447051706663722827 5574465670577559995584241)
              ·
                refine ⟨4180849252933169996688181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5574465670577559995584241 4180849252933169996688181)
                ·
                  refine ⟨391954617462484687189517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4180849252933169996688181 391954617462484687189517)
                  ·
                    rfl

theorem cell21_1717490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_1717490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717490 prefixEnd_1717490 := by exact prefixLift 1717490
  have htrace : WordTrace (prefixWord ++ tailWord_1717490) baseStart_1717490 baseEnd_1717490 := by
    simpa [prefixWord, tailWord_1717490, baseEnd_1717490] using wordTrace_append hprefix tailTrace_1717490
  have hstable : (prefixWord ++ tailWord_1717490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717490).length < 2 ^ (prefixWord ++ tailWord_1717490).sum := by decide
  have hdescent : baseEnd_1717490 < baseStart_1717490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717518 : List Nat := [4, 1, 1, 2, 1, 4, 8]
def baseStart_1717518 : Nat := 118140960795 + 1717518 * 2 ^ 59
def prefixEnd_1717518 : Nat := 4983230072969 + 3 ^ 40 * 1717518 * 2
def baseEnd_1717518 : Nat := 43551223049329206746977

theorem tailTrace_1717518 : CollatzResearch.WordTrace tailWord_1717518 prefixEnd_1717518 43551223049329206746977 := by
  unfold tailWord_1717518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7830378473966636195802151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41762018527822059710944805 7830378473966636195802151)
  ·
    refine ⟨11745567710949954293703227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7830378473966636195802151 11745567710949954293703227)
    ·
      refine ⟨17618351566424931440554841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11745567710949954293703227 17618351566424931440554841)
      ·
        refine ⟨13213763674818698580416131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17618351566424931440554841 13213763674818698580416131)
        ·
          refine ⟨19820645512228047870624197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13213763674818698580416131 19820645512228047870624197)
          ·
            refine ⟨3716371033542758975742037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19820645512228047870624197 3716371033542758975742037)
            ·
              refine ⟨43551223049329206746977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3716371033542758975742037 43551223049329206746977)
              ·
                rfl

theorem cell21_1717518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 8].length) (baseStart_1717518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717518 prefixEnd_1717518 := by exact prefixLift 1717518
  have htrace : WordTrace (prefixWord ++ tailWord_1717518) baseStart_1717518 baseEnd_1717518 := by
    simpa [prefixWord, tailWord_1717518, baseEnd_1717518] using wordTrace_append hprefix tailTrace_1717518
  have hstable : (prefixWord ++ tailWord_1717518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717518).length < 2 ^ (prefixWord ++ tailWord_1717518).sum := by decide
  have hdescent : baseEnd_1717518 < baseStart_1717518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717538 : List Nat := [3, 3, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1717538 : Nat := 118140960795 + 1717538 * 2 ^ 59
def prefixEnd_1717538 : Nat := 4983230072969 + 3 ^ 40 * 1717538 * 2
def baseEnd_1717538 : Nat := 391965571716447270389419

theorem tailTrace_1717538 : CollatzResearch.WordTrace tailWord_1717538 prefixEnd_1717538 391965571716447270389419 := by
  unfold tailWord_1717538
  simp only [CollatzResearch.WordTrace]
  refine ⟨15660939312915158245536317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41762504834440421988096845 15660939312915158245536317)
  ·
    refine ⟨5872852242343184342076119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15660939312915158245536317 5872852242343184342076119)
    ·
      refine ⟨8809278363514776513114179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5872852242343184342076119 8809278363514776513114179)
      ·
        refine ⟨13213917545272164769671269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8809278363514776513114179 13213917545272164769671269)
        ·
          refine ⟨2477609539738530894313363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13213917545272164769671269 2477609539738530894313363)
          ·
            refine ⟨3716414309607796341470045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2477609539738530894313363 3716414309607796341470045)
            ·
              refine ⟨1393655366102923628051267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3716414309607796341470045 1393655366102923628051267)
              ·
                refine ⟨2090483049154385442076901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1393655366102923628051267 2090483049154385442076901)
                ·
                  refine ⟨391965571716447270389419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2090483049154385442076901 391965571716447270389419)
                  ·
                    rfl

theorem cell21_1717538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1717538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717538 prefixEnd_1717538 := by exact prefixLift 1717538
  have htrace : WordTrace (prefixWord ++ tailWord_1717538) baseStart_1717538 baseEnd_1717538 := by
    simpa [prefixWord, tailWord_1717538, baseEnd_1717538] using wordTrace_append hprefix tailTrace_1717538
  have hstable : (prefixWord ++ tailWord_1717538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717538).length < 2 ^ (prefixWord ++ tailWord_1717538).sum := by decide
  have hdescent : baseEnd_1717538 < baseStart_1717538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717558 : List Nat := [5, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_1717558 : Nat := 118140960795 + 1717558 * 2 ^ 59
def prefixEnd_1717558 : Nat := 4983230072969 + 3 ^ 40 * 1717558 * 2
def baseEnd_1717558 : Nat := 391970135988931680056045

theorem tailTrace_1717558 : CollatzResearch.WordTrace tailWord_1717558 prefixEnd_1717558 391970135988931680056045 := by
  unfold tailWord_1717558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915280419474261024867083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41762991141058784265248885 3915280419474261024867083)
  ·
    refine ⟨5872920629211391537300625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3915280419474261024867083 5872920629211391537300625)
    ·
      refine ⟨4404690471908543652975469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5872920629211391537300625 4404690471908543652975469)
      ·
        refine ⟨1651758926965703869865801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4404690471908543652975469 1651758926965703869865801)
        ·
          refine ⟨1238819195224277902399351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1651758926965703869865801 1238819195224277902399351)
          ·
            refine ⟨1858228792836416853599027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238819195224277902399351 1858228792836416853599027)
            ·
              refine ⟨2787343189254625280398541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1858228792836416853599027 2787343189254625280398541)
              ·
                refine ⟨1045253695970484480149453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2787343189254625280398541 1045253695970484480149453)
                ·
                  refine ⟨391970135988931680056045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1045253695970484480149453 391970135988931680056045)
                  ·
                    rfl

theorem cell21_1717558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_1717558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717558 prefixEnd_1717558 := by exact prefixLift 1717558
  have htrace : WordTrace (prefixWord ++ tailWord_1717558) baseStart_1717558 baseEnd_1717558 := by
    simpa [prefixWord, tailWord_1717558, baseEnd_1717558] using wordTrace_append hprefix tailTrace_1717558
  have hstable : (prefixWord ++ tailWord_1717558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717558).length < 2 ^ (prefixWord ++ tailWord_1717558).sum := by decide
  have hdescent : baseEnd_1717558 < baseStart_1717558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717577 : List Nat := [1, 2, 1, 1, 2, 3, 11]
def baseStart_1717577 : Nat := 118140960795 + 1717577 * 2 ^ 59
def prefixEnd_1717577 : Nat := 4983230072969 + 3 ^ 40 * 1717577 * 2
def baseEnd_1717577 : Nat := 43552719116421318804371

theorem tailTrace_1717577 : CollatzResearch.WordTrace tailWord_1717577 prefixEnd_1717577 43552719116421318804371 := by
  unfold tailWord_1717577
  simp only [CollatzResearch.WordTrace]
  refine ⟨62645179698519342642814985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41763453132346228428543323 62645179698519342642814985)
  ·
    refine ⟨46983884773889506982111239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62645179698519342642814985 46983884773889506982111239)
    ·
      refine ⟨70475827160834260473166859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46983884773889506982111239 70475827160834260473166859)
      ·
        refine ⟨105713740741251390709750289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70475827160834260473166859 105713740741251390709750289)
        ·
          refine ⟨79285305555938543032312717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105713740741251390709750289 79285305555938543032312717)
          ·
            refine ⟨29731989583476953637117269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79285305555938543032312717 29731989583476953637117269)
            ·
              refine ⟨43552719116421318804371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29731989583476953637117269 43552719116421318804371)
              ·
                rfl

theorem cell21_1717577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 11].length) (baseStart_1717577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717577 prefixEnd_1717577 := by exact prefixLift 1717577
  have htrace : WordTrace (prefixWord ++ tailWord_1717577) baseStart_1717577 baseEnd_1717577 := by
    simpa [prefixWord, tailWord_1717577, baseEnd_1717577] using wordTrace_append hprefix tailTrace_1717577
  have hstable : (prefixWord ++ tailWord_1717577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717577).length < 2 ^ (prefixWord ++ tailWord_1717577).sum := by decide
  have hdescent : baseEnd_1717577 < baseStart_1717577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717718 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1717718 : Nat := 118140960795 + 1717718 * 2 ^ 59
def prefixEnd_1717718 : Nat := 4983230072969 + 3 ^ 40 * 1717718 * 2
def baseEnd_1717718 : Nat := 392006650168806957389051

theorem tailTrace_1717718 : CollatzResearch.WordTrace tailWord_1717718 prefixEnd_1717718 392006650168806957389051 := by
  unfold tailWord_1717718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915645149438032732731113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41766881594005682482465205 3915645149438032732731113)
  ·
    refine ⟨2936733862078524549548335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3915645149438032732731113 2936733862078524549548335)
    ·
      refine ⟨4405100793117786824322503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2936733862078524549548335 4405100793117786824322503)
      ·
        refine ⟨6607651189676680236483755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4405100793117786824322503 6607651189676680236483755)
        ·
          refine ⟨9911476784515020354725633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6607651189676680236483755 9911476784515020354725633)
          ·
            refine ⟨7433607588386265266044225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9911476784515020354725633 7433607588386265266044225)
            ·
              refine ⟨5575205691289698949533169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7433607588386265266044225 5575205691289698949533169)
              ·
                refine ⟨4181404268467274212149877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5575205691289698949533169 4181404268467274212149877)
                ·
                  refine ⟨392006650168806957389051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4181404268467274212149877 392006650168806957389051)
                  ·
                    rfl

theorem cell21_1717718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1717718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717718 prefixEnd_1717718 := by exact prefixLift 1717718
  have htrace : WordTrace (prefixWord ++ tailWord_1717718) baseStart_1717718 baseEnd_1717718 := by
    simpa [prefixWord, tailWord_1717718, baseEnd_1717718] using wordTrace_append hprefix tailTrace_1717718
  have hstable : (prefixWord ++ tailWord_1717718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717718).length < 2 ^ (prefixWord ++ tailWord_1717718).sum := by decide
  have hdescent : baseEnd_1717718 < baseStart_1717718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717735 : List Nat := [1, 1, 5, 2, 1, 4, 1, 3, 3]
def baseStart_1717735 : Nat := 118140960795 + 1717735 * 2 ^ 59
def prefixEnd_1717735 : Nat := 4983230072969 + 3 ^ 40 * 1717735 * 2
def baseEnd_1717735 : Nat := 392010529800418705605683

theorem tailTrace_1717735 : CollatzResearch.WordTrace tailWord_1717735 prefixEnd_1717735 392010529800418705605683 := by
  unfold tailWord_1717735
  simp only [CollatzResearch.WordTrace]
  refine ⟨62650942431946935627066659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41767294954631290418044439 62650942431946935627066659)
  ·
    refine ⟨93976413647920403440599989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62650942431946935627066659 93976413647920403440599989)
    ·
      refine ⟨8810288779492537822556249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93976413647920403440599989 8810288779492537822556249)
      ·
        refine ⟨6607716584619403366917187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8810288779492537822556249 6607716584619403366917187)
        ·
          refine ⟨9911574876929105050375781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6607716584619403366917187 9911574876929105050375781)
          ·
            refine ⟨1858420289424207196945459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9911574876929105050375781 1858420289424207196945459)
            ·
              refine ⟨2787630434136310795418189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1858420289424207196945459 2787630434136310795418189)
              ·
                refine ⟨1045361412801116548281821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2787630434136310795418189 1045361412801116548281821)
                ·
                  refine ⟨392010529800418705605683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1045361412801116548281821 392010529800418705605683)
                  ·
                    rfl

theorem cell21_1717735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 3].length) (baseStart_1717735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717735 prefixEnd_1717735 := by exact prefixLift 1717735
  have htrace : WordTrace (prefixWord ++ tailWord_1717735) baseStart_1717735 baseEnd_1717735 := by
    simpa [prefixWord, tailWord_1717735, baseEnd_1717735] using wordTrace_append hprefix tailTrace_1717735
  have hstable : (prefixWord ++ tailWord_1717735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717735).length < 2 ^ (prefixWord ++ tailWord_1717735).sum := by decide
  have hdescent : baseEnd_1717735 < baseStart_1717735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717746 : List Nat := [3, 2, 1, 4, 1, 1, 9]
def baseStart_1717746 : Nat := 118140960795 + 1717746 * 2 ^ 59
def prefixEnd_1717746 : Nat := 4983230072969 + 3 ^ 40 * 1717746 * 2
def baseEnd_1717746 : Nat := 43557004461142792324703

theorem tailTrace_1717746 : CollatzResearch.WordTrace tailWord_1717746 prefixEnd_1717746 43557004461142792324703 := by
  unfold tailWord_1717746
  simp only [CollatzResearch.WordTrace]
  refine ⟨15662835908726771126429273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41767562423271389670478061 15662835908726771126429273)
  ·
    refine ⟨11747126931545078344821955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15662835908726771126429273 11747126931545078344821955)
    ·
      refine ⟨17620690397317617517232933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11747126931545078344821955 17620690397317617517232933)
      ·
        refine ⟨3303879449497053284481175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17620690397317617517232933 3303879449497053284481175)
        ·
          refine ⟨4955819174245579926721763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3303879449497053284481175 4955819174245579926721763)
          ·
            refine ⟨7433728761368369890082645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4955819174245579926721763 7433728761368369890082645)
            ·
              refine ⟨43557004461142792324703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7433728761368369890082645 43557004461142792324703)
              ·
                rfl

theorem cell21_1717746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 9].length) (baseStart_1717746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717746 prefixEnd_1717746 := by exact prefixLift 1717746
  have htrace : WordTrace (prefixWord ++ tailWord_1717746) baseStart_1717746 baseEnd_1717746 := by
    simpa [prefixWord, tailWord_1717746, baseEnd_1717746] using wordTrace_append hprefix tailTrace_1717746
  have hstable : (prefixWord ++ tailWord_1717746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717746).length < 2 ^ (prefixWord ++ tailWord_1717746).sum := by decide
  have hdescent : baseEnd_1717746 < baseStart_1717746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717811 : List Nat := [1, 1, 1, 2, 4, 5, 2, 2, 3]
def baseStart_1717811 : Nat := 118140960795 + 1717811 * 2 ^ 59
def prefixEnd_1717811 : Nat := 4983230072969 + 3 ^ 40 * 1717811 * 2
def baseEnd_1717811 : Nat := 392027874035859462338861

theorem tailTrace_1717811 : CollatzResearch.WordTrace tailWord_1717811 prefixEnd_1717811 392027874035859462338861 := by
  unfold tailWord_1717811
  simp only [CollatzResearch.WordTrace]
  refine ⟨62653714379671600606833287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41769142919781067071222191 62653714379671600606833287)
  ·
    refine ⟨93980571569507400910249931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62653714379671600606833287 93980571569507400910249931)
    ·
      refine ⟨140970857354261101365374897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93980571569507400910249931 140970857354261101365374897)
      ·
        refine ⟨105728143015695826024031173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140970857354261101365374897 105728143015695826024031173)
        ·
          refine ⟨19824026815442967379505845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105728143015695826024031173 19824026815442967379505845)
          ·
            refine ⟨1858502513947778191828673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19824026815442967379505845 1858502513947778191828673)
            ·
              refine ⟨1393876885460833643871505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1858502513947778191828673 1393876885460833643871505)
              ·
                refine ⟨1045407664095625232903629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1393876885460833643871505 1045407664095625232903629)
                ·
                  refine ⟨392027874035859462338861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1045407664095625232903629 392027874035859462338861)
                  ·
                    rfl

theorem cell21_1717811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 3].length) (baseStart_1717811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717811 prefixEnd_1717811 := by exact prefixLift 1717811
  have htrace : WordTrace (prefixWord ++ tailWord_1717811) baseStart_1717811 baseEnd_1717811 := by
    simpa [prefixWord, tailWord_1717811, baseEnd_1717811] using wordTrace_append hprefix tailTrace_1717811
  have hstable : (prefixWord ++ tailWord_1717811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717811).length < 2 ^ (prefixWord ++ tailWord_1717811).sum := by decide
  have hdescent : baseEnd_1717811 < baseStart_1717811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717836 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 7]
def baseStart_1717836 : Nat := 118140960795 + 1717836 * 2 ^ 59
def prefixEnd_1717836 : Nat := 4983230072969 + 3 ^ 40 * 1717836 * 2
def baseEnd_1717836 : Nat := 392033579376464974422143

theorem tailTrace_1717836 : CollatzResearch.WordTrace tailWord_1717836 prefixEnd_1717836 392033579376464974422143 := by
  unfold tailWord_1717836
  simp only [CollatzResearch.WordTrace]
  refine ⟨31327313102290514938246681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41769750803054019917662241 31327313102290514938246681)
  ·
    refine ⟨23495484826717886203685011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31327313102290514938246681 23495484826717886203685011)
    ·
      refine ⟨35243227240076829305527517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23495484826717886203685011 35243227240076829305527517)
      ·
        refine ⟨13216210215028810989572819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35243227240076829305527517 13216210215028810989572819)
        ·
          refine ⟨19824315322543216484359229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13216210215028810989572819 19824315322543216484359229)
          ·
            refine ⟨7434118245953706181634711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19824315322543216484359229 7434118245953706181634711)
            ·
              refine ⟨11151177368930559272452067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7434118245953706181634711 11151177368930559272452067)
              ·
                refine ⟨16726766053395838908678101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11151177368930559272452067 16726766053395838908678101)
                ·
                  refine ⟨392033579376464974422143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16726766053395838908678101 392033579376464974422143)
                  ·
                    rfl

theorem cell21_1717836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_1717836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717836 prefixEnd_1717836 := by exact prefixLift 1717836
  have htrace : WordTrace (prefixWord ++ tailWord_1717836) baseStart_1717836 baseEnd_1717836 := by
    simpa [prefixWord, tailWord_1717836, baseEnd_1717836] using wordTrace_append hprefix tailTrace_1717836
  have hstable : (prefixWord ++ tailWord_1717836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717836).length < 2 ^ (prefixWord ++ tailWord_1717836).sum := by decide
  have hdescent : baseEnd_1717836 < baseStart_1717836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717870 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_1717870 : Nat := 118140960795 + 1717870 * 2 ^ 59
def prefixEnd_1717870 : Nat := 4983230072969 + 3 ^ 40 * 1717870 * 2
def baseEnd_1717870 : Nat := 392041338639688470855407

theorem tailTrace_1717870 : CollatzResearch.WordTrace tailWord_1717870 prefixEnd_1717870 392041338639688470855407 := by
  unfold tailWord_1717870
  simp only [CollatzResearch.WordTrace]
  refine ⟨7831983285807231710403883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41770577524305235788820709 7831983285807231710403883)
  ·
    refine ⟨11747974928710847565605825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7831983285807231710403883 11747974928710847565605825)
    ·
      refine ⟨8810981196533135674204369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11747974928710847565605825 8810981196533135674204369)
      ·
        refine ⟨6608235897399851755653277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8810981196533135674204369 6608235897399851755653277)
        ·
          refine ⟨2478088461524944408369979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6608235897399851755653277 2478088461524944408369979)
          ·
            refine ⟨3717132692287416612554969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478088461524944408369979 3717132692287416612554969)
            ·
              refine ⟨2787849519215562459416227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3717132692287416612554969 2787849519215562459416227)
              ·
                refine ⟨4181774278823343689124341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787849519215562459416227 4181774278823343689124341)
                ·
                  refine ⟨392041338639688470855407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4181774278823343689124341 392041338639688470855407)
                  ·
                    rfl

theorem cell21_1717870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_1717870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717870 prefixEnd_1717870 := by exact prefixLift 1717870
  have htrace : WordTrace (prefixWord ++ tailWord_1717870) baseStart_1717870 baseEnd_1717870 := by
    simpa [prefixWord, tailWord_1717870, baseEnd_1717870] using wordTrace_append hprefix tailTrace_1717870
  have hstable : (prefixWord ++ tailWord_1717870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717870).length < 2 ^ (prefixWord ++ tailWord_1717870).sum := by decide
  have hdescent : baseEnd_1717870 < baseStart_1717870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717881 : List Nat := [1, 2, 1, 3, 3, 1, 2, 8]
def baseStart_1717881 : Nat := 118140960795 + 1717881 * 2 ^ 59
def prefixEnd_1717881 : Nat := 4983230072969 + 3 ^ 40 * 1717881 * 2
def baseEnd_1717881 : Nat := 130681282996518298724017

theorem tailTrace_1717881 : CollatzResearch.WordTrace tailWord_1717881 prefixEnd_1717881 130681282996518298724017 := by
  unfold tailWord_1717881
  simp only [CollatzResearch.WordTrace]
  refine ⟨62656267489418002561881497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41770844992945335041254331 62656267489418002561881497)
  ·
    refine ⟨46992200617063501921411123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62656267489418002561881497 46992200617063501921411123)
    ·
      refine ⟨70488300925595252882116685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46992200617063501921411123 70488300925595252882116685)
      ·
        refine ⟨26433112847098219830793757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70488300925595252882116685 26433112847098219830793757)
        ·
          refine ⟨9912417317661832436547659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26433112847098219830793757 9912417317661832436547659)
          ·
            refine ⟨14868625976492748654821489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9912417317661832436547659 14868625976492748654821489)
            ·
              refine ⟨11151469482369561491116117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14868625976492748654821489 11151469482369561491116117)
              ·
                refine ⟨130681282996518298724017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11151469482369561491116117 130681282996518298724017)
                ·
                  rfl

theorem cell21_1717881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 8].length) (baseStart_1717881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717881 prefixEnd_1717881 := by exact prefixLift 1717881
  have htrace : WordTrace (prefixWord ++ tailWord_1717881) baseStart_1717881 baseEnd_1717881 := by
    simpa [prefixWord, tailWord_1717881, baseEnd_1717881] using wordTrace_append hprefix tailTrace_1717881
  have hstable : (prefixWord ++ tailWord_1717881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717881).length < 2 ^ (prefixWord ++ tailWord_1717881).sum := by decide
  have hdescent : baseEnd_1717881 < baseStart_1717881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717898 : List Nat := [3, 1, 2, 3, 2, 2, 1, 7]
def baseStart_1717898 : Nat := 118140960795 + 1717898 * 2 ^ 59
def prefixEnd_1717898 : Nat := 4983230072969 + 3 ^ 40 * 1717898 * 2
def baseEnd_1717898 : Nat := 130682576207055548129561

theorem tailTrace_1717898 : CollatzResearch.WordTrace tailWord_1717898 prefixEnd_1717898 130682576207055548129561 := by
  unfold tailWord_1717898
  simp only [CollatzResearch.WordTrace]
  refine ⟨15664221882589103616312587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41771258353570942976833565 15664221882589103616312587)
  ·
    refine ⟨23496332823883655424468881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15664221882589103616312587 23496332823883655424468881)
    ·
      refine ⟨17622249617912741568351661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23496332823883655424468881 17622249617912741568351661)
      ·
        refine ⟨6608343606717278088131873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17622249617912741568351661 6608343606717278088131873)
        ·
          refine ⟨4956257705037958566098905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6608343606717278088131873 4956257705037958566098905)
          ·
            refine ⟨3717193278778468924574179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4956257705037958566098905 3717193278778468924574179)
            ·
              refine ⟨5575789918167703386861269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3717193278778468924574179 5575789918167703386861269)
              ·
                refine ⟨130682576207055548129561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5575789918167703386861269 130682576207055548129561)
                ·
                  rfl

theorem cell21_1717898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_1717898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717898 prefixEnd_1717898 := by exact prefixLift 1717898
  have htrace : WordTrace (prefixWord ++ tailWord_1717898) baseStart_1717898 baseEnd_1717898 := by
    simpa [prefixWord, tailWord_1717898, baseEnd_1717898] using wordTrace_append hprefix tailTrace_1717898
  have hstable : (prefixWord ++ tailWord_1717898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717898).length < 2 ^ (prefixWord ++ tailWord_1717898).sum := by decide
  have hdescent : baseEnd_1717898 < baseStart_1717898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717988 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 5]
def baseStart_1717988 : Nat := 118140960795 + 1717988 * 2 ^ 59
def prefixEnd_1717988 : Nat := 4983230072969 + 3 ^ 40 * 1717988 * 2
def baseEnd_1717988 : Nat := 392068267847346487888499

theorem tailTrace_1717988 : CollatzResearch.WordTrace tailWord_1717988 prefixEnd_1717988 392068267847346487888499 := by
  unfold tailWord_1717988
  simp only [CollatzResearch.WordTrace]
  refine ⟨31330085050015179918013309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41773446733353573224017745 31330085050015179918013309)
  ·
    refine ⟨11748781893755692469254991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31330085050015179918013309 11748781893755692469254991)
    ·
      refine ⟨17623172840633538703882487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11748781893755692469254991 17623172840633538703882487)
      ·
        refine ⟨26434759260950308055823731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17623172840633538703882487 26434759260950308055823731)
        ·
          refine ⟨39652138891425462083735597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26434759260950308055823731 39652138891425462083735597)
          ·
            refine ⟨14869552084284548281400849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39652138891425462083735597 14869552084284548281400849)
            ·
              refine ⟨11152164063213411211050637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14869552084284548281400849 11152164063213411211050637)
              ·
                refine ⟨4182061523705029204143989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11152164063213411211050637 4182061523705029204143989)
                ·
                  refine ⟨392068267847346487888499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4182061523705029204143989 392068267847346487888499)
                  ·
                    rfl

theorem cell21_1717988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_1717988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1717988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1717988 prefixEnd_1717988 := by exact prefixLift 1717988
  have htrace : WordTrace (prefixWord ++ tailWord_1717988) baseStart_1717988 baseEnd_1717988 := by
    simpa [prefixWord, tailWord_1717988, baseEnd_1717988] using wordTrace_append hprefix tailTrace_1717988
  have hstable : (prefixWord ++ tailWord_1717988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717988).length < 2 ^ (prefixWord ++ tailWord_1717988).sum := by decide
  have hdescent : baseEnd_1717988 < baseStart_1717988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718067 : List Nat := [1, 1, 1, 2, 7, 2, 2, 5]
def baseStart_1718067 : Nat := 118140960795 + 1718067 * 2 ^ 59
def prefixEnd_1718067 : Nat := 4983230072969 + 3 ^ 40 * 1718067 * 2
def baseEnd_1718067 : Nat := 130695432241219968690557

theorem tailTrace_1718067 : CollatzResearch.WordTrace tailWord_1718067 prefixEnd_1718067 130695432241219968690557 := by
  unfold tailWord_1718067
  simp only [CollatzResearch.WordTrace]
  refine ⟨62663051466744156328152455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41775367644496104218768303 62663051466744156328152455)
  ·
    refine ⟨93994577200116234492228683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62663051466744156328152455 93994577200116234492228683)
    ·
      refine ⟨140991865800174351738343025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93994577200116234492228683 140991865800174351738343025)
      ·
        refine ⟨105743899350130763803757269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140991865800174351738343025 105743899350130763803757269)
        ·
          refine ⟨2478372641018689776650561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 105743899350130763803757269 2478372641018689776650561)
          ·
            refine ⟨1858779480764017332487921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2478372641018689776650561 1858779480764017332487921)
            ·
              refine ⟨1394084610573012999365941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1858779480764017332487921 1394084610573012999365941)
              ·
                refine ⟨130695432241219968690557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1394084610573012999365941 130695432241219968690557)
                ·
                  rfl

theorem cell21_1718067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 5].length) (baseStart_1718067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718067 prefixEnd_1718067 := by exact prefixLift 1718067
  have htrace : WordTrace (prefixWord ++ tailWord_1718067) baseStart_1718067 baseEnd_1718067 := by
    simpa [prefixWord, tailWord_1718067, baseEnd_1718067] using wordTrace_append hprefix tailTrace_1718067
  have hstable : (prefixWord ++ tailWord_1718067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718067).length < 2 ^ (prefixWord ++ tailWord_1718067).sum := by decide
  have hdescent : baseEnd_1718067 < baseStart_1718067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718112 : List Nat := [2, 1, 1, 3, 3, 2, 4, 1, 4]
def baseStart_1718112 : Nat := 118140960795 + 1718112 * 2 ^ 59
def prefixEnd_1718112 : Nat := 4983230072969 + 3 ^ 40 * 1718112 * 2
def baseEnd_1718112 : Nat := 392096566336749827821579

theorem tailTrace_1718112 : CollatzResearch.WordTrace tailWord_1718112 prefixEnd_1718112 392096566336749827821579 := by
  unfold tailWord_1718112
  simp only [CollatzResearch.WordTrace]
  refine ⟨31332346375790564506770295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41776461834387419342360393 31332346375790564506770295)
  ·
    refine ⟨46998519563685846760155443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31332346375790564506770295 46998519563685846760155443)
    ·
      refine ⟨70497779345528770140233165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46998519563685846760155443 70497779345528770140233165)
      ·
        refine ⟨26436667254573288802587437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70497779345528770140233165 26436667254573288802587437)
        ·
          refine ⟨9913750220464983300970289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26436667254573288802587437 9913750220464983300970289)
          ·
            refine ⟨7435312665348737475727717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9913750220464983300970289 7435312665348737475727717)
            ·
              refine ⟨1394121124752888276698947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7435312665348737475727717 1394121124752888276698947)
              ·
                refine ⟨2091181687129332415048421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1394121124752888276698947 2091181687129332415048421)
                ·
                  refine ⟨392096566336749827821579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2091181687129332415048421 392096566336749827821579)
                  ·
                    rfl

theorem cell21_1718112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 4].length) (baseStart_1718112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718112 prefixEnd_1718112 := by exact prefixLift 1718112
  have htrace : WordTrace (prefixWord ++ tailWord_1718112) baseStart_1718112 baseEnd_1718112 := by
    simpa [prefixWord, tailWord_1718112, baseEnd_1718112] using wordTrace_append hprefix tailTrace_1718112
  have hstable : (prefixWord ++ tailWord_1718112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718112).length < 2 ^ (prefixWord ++ tailWord_1718112).sum := by decide
  have hdescent : baseEnd_1718112 < baseStart_1718112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718123 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 7]
def baseStart_1718123 : Nat := 118140960795 + 1718123 * 2 ^ 59
def prefixEnd_1718123 : Nat := 4983230072969 + 3 ^ 40 * 1718123 * 2
def baseEnd_1718123 : Nat := 392099076686616253138223

theorem tailTrace_1718123 : CollatzResearch.WordTrace tailWord_1718123 prefixEnd_1718123 392099076686616253138223 := by
  unfold tailWord_1718123
  simp only [CollatzResearch.WordTrace]
  refine ⟨62665093954541277892191023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41776729303027518594794015 62665093954541277892191023)
  ·
    refine ⟨93997640931811916838286535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62665093954541277892191023 93997640931811916838286535)
    ·
      refine ⟨140996461397717875257429803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93997640931811916838286535 140996461397717875257429803)
      ·
        refine ⟨211494692096576812886144705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140996461397717875257429803 211494692096576812886144705)
        ·
          refine ⟨158621019072432609664608529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211494692096576812886144705 158621019072432609664608529)
          ·
            refine ⟨118965764304324457248456397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158621019072432609664608529 118965764304324457248456397)
            ·
              refine ⟨44612161614121671468171149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118965764304324457248456397 44612161614121671468171149)
              ·
                refine ⟨16729560605295626800564181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44612161614121671468171149 16729560605295626800564181)
                ·
                  refine ⟨392099076686616253138223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16729560605295626800564181 392099076686616253138223)
                  ·
                    rfl

theorem cell21_1718123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 7].length) (baseStart_1718123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718123 prefixEnd_1718123 := by exact prefixLift 1718123
  have htrace : WordTrace (prefixWord ++ tailWord_1718123) baseStart_1718123 baseEnd_1718123 := by
    simpa [prefixWord, tailWord_1718123, baseEnd_1718123] using wordTrace_append hprefix tailTrace_1718123
  have hstable : (prefixWord ++ tailWord_1718123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718123).length < 2 ^ (prefixWord ++ tailWord_1718123).sum := by decide
  have hdescent : baseEnd_1718123 < baseStart_1718123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718126 : List Nat := [4, 1, 2, 3, 1, 1, 2, 7]
def baseStart_1718126 : Nat := 118140960795 + 1718126 * 2 ^ 59
def prefixEnd_1718126 : Nat := 4983230072969 + 3 ^ 40 * 1718126 * 2
def baseEnd_1718126 : Nat := 130699920442496304862739

theorem tailTrace_1718126 : CollatzResearch.WordTrace tailWord_1718126 prefixEnd_1718126 130699920442496304862739 := by
  unfold tailWord_1718126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7833150421691301175568779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41776802249020272936366821 7833150421691301175568779)
  ·
    refine ⟨11749725632536951763353169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7833150421691301175568779 11749725632536951763353169)
    ·
      refine ⟨8812294224402713822514877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11749725632536951763353169 8812294224402713822514877)
      ·
        refine ⟨3304610334151017683443079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8812294224402713822514877 3304610334151017683443079)
        ·
          refine ⟨4956915501226526525164619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3304610334151017683443079 4956915501226526525164619)
          ·
            refine ⟨7435373251839789787746929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4956915501226526525164619 7435373251839789787746929)
            ·
              refine ⟨5576529938879842340810197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7435373251839789787746929 5576529938879842340810197)
              ·
                refine ⟨130699920442496304862739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5576529938879842340810197 130699920442496304862739)
                ·
                  rfl

theorem cell21_1718126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_1718126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718126 prefixEnd_1718126 := by exact prefixLift 1718126
  have htrace : WordTrace (prefixWord ++ tailWord_1718126) baseStart_1718126 baseEnd_1718126 := by
    simpa [prefixWord, tailWord_1718126, baseEnd_1718126] using wordTrace_append hprefix tailTrace_1718126
  have hstable : (prefixWord ++ tailWord_1718126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718126).length < 2 ^ (prefixWord ++ tailWord_1718126).sum := by decide
  have hdescent : baseEnd_1718126 < baseStart_1718126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718199 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 9]
def baseStart_1718199 : Nat := 118140960795 + 1718199 * 2 ^ 59
def prefixEnd_1718199 : Nat := 4983230072969 + 3 ^ 40 * 1718199 * 2
def baseEnd_1718199 : Nat := 392116420922057009871401

theorem tailTrace_1718199 : CollatzResearch.WordTrace tailWord_1718199 prefixEnd_1718199 392116420922057009871401 := by
  unfold tailWord_1718199
  simp only [CollatzResearch.WordTrace]
  refine ⟨62667865902265942871957651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41778577268177295247971767 62667865902265942871957651)
  ·
    refine ⟨94001798853398914307936477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62667865902265942871957651 94001798853398914307936477)
    ·
      refine ⟨35250674570024592865476179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94001798853398914307936477 35250674570024592865476179)
      ·
        refine ⟨52876011855036889298214269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35250674570024592865476179 52876011855036889298214269)
        ·
          refine ⟨19828504445638833486830351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52876011855036889298214269 19828504445638833486830351)
          ·
            refine ⟨29742756668458250230245527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19828504445638833486830351 29742756668458250230245527)
            ·
              refine ⟨44614135002687375345368291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29742756668458250230245527 44614135002687375345368291)
              ·
                refine ⟨66921202504031063018052437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44614135002687375345368291 66921202504031063018052437)
                ·
                  refine ⟨392116420922057009871401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66921202504031063018052437 392116420922057009871401)
                  ·
                    rfl

theorem cell21_1718199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 9].length) (baseStart_1718199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718199 prefixEnd_1718199 := by exact prefixLift 1718199
  have htrace : WordTrace (prefixWord ++ tailWord_1718199) baseStart_1718199 baseEnd_1718199 := by
    simpa [prefixWord, tailWord_1718199, baseEnd_1718199] using wordTrace_append hprefix tailTrace_1718199
  have hstable : (prefixWord ++ tailWord_1718199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718199).length < 2 ^ (prefixWord ++ tailWord_1718199).sum := by decide
  have hdescent : baseEnd_1718199 < baseStart_1718199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718216 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 5]
def baseStart_1718216 : Nat := 118140960795 + 1718216 * 2 ^ 59
def prefixEnd_1718216 : Nat := 4983230072969 + 3 ^ 40 * 1718216 * 2
def baseEnd_1718216 : Nat := 392120300553668758088033

theorem tailTrace_1718216 : CollatzResearch.WordTrace tailWord_1718216 prefixEnd_1718216 392120300553668758088033 := by
  unfold tailWord_1718216
  simp only [CollatzResearch.WordTrace]
  refine ⟨31334242971602177387663251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41778990628802903183551001 31334242971602177387663251)
  ·
    refine ⟨47001364457403266081494877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31334242971602177387663251 47001364457403266081494877)
    ·
      refine ⟨17625511671526224780560579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47001364457403266081494877 17625511671526224780560579)
      ·
        refine ⟨26438267507289337170840869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17625511671526224780560579 26438267507289337170840869)
        ·
          refine ⟨4957175157616750719532663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26438267507289337170840869 4957175157616750719532663)
          ·
            refine ⟨7435762736425126079298995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957175157616750719532663 7435762736425126079298995)
            ·
              refine ⟨11153644104637689118948493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7435762736425126079298995 11153644104637689118948493)
              ·
                refine ⟨4182616539239133419605685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11153644104637689118948493 4182616539239133419605685)
                ·
                  refine ⟨392120300553668758088033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4182616539239133419605685 392120300553668758088033)
                  ·
                    rfl

theorem cell21_1718216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_1718216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718216 prefixEnd_1718216 := by exact prefixLift 1718216
  have htrace : WordTrace (prefixWord ++ tailWord_1718216) baseStart_1718216 baseEnd_1718216 := by
    simpa [prefixWord, tailWord_1718216, baseEnd_1718216] using wordTrace_append hprefix tailTrace_1718216
  have hstable : (prefixWord ++ tailWord_1718216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718216).length < 2 ^ (prefixWord ++ tailWord_1718216).sum := by decide
  have hdescent : baseEnd_1718216 < baseStart_1718216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718236 : List Nat := [2, 2, 6, 1, 1, 1, 1, 7]
def baseStart_1718236 : Nat := 118140960795 + 1718236 * 2 ^ 59
def prefixEnd_1718236 : Nat := 4983230072969 + 3 ^ 40 * 1718236 * 2
def baseEnd_1718236 : Nat := 130708288275384389251553

theorem tailTrace_1718236 : CollatzResearch.WordTrace tailWord_1718236 prefixEnd_1718236 130708288275384389251553 := by
  unfold tailWord_1718236
  simp only [CollatzResearch.WordTrace]
  refine ⟨31334607701565949095527281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41779476935421265460703041 31334607701565949095527281)
  ·
    refine ⟨23500955776174461821645461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31334607701565949095527281 23500955776174461821645461)
    ·
      refine ⟨1101607302008177897889631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23500955776174461821645461 1101607302008177897889631)
      ·
        refine ⟨1652410953012266846834447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1101607302008177897889631 1652410953012266846834447)
        ·
          refine ⟨2478616429518400270251671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1652410953012266846834447 2478616429518400270251671)
          ·
            refine ⟨3717924644277600405377507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478616429518400270251671 3717924644277600405377507)
            ·
              refine ⟨5576886966416400608066261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3717924644277600405377507 5576886966416400608066261)
              ·
                refine ⟨130708288275384389251553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5576886966416400608066261 130708288275384389251553)
                ·
                  rfl

theorem cell21_1718236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 7].length) (baseStart_1718236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718236 prefixEnd_1718236 := by exact prefixLift 1718236
  have htrace : WordTrace (prefixWord ++ tailWord_1718236) baseStart_1718236 baseEnd_1718236 := by
    simpa [prefixWord, tailWord_1718236, baseEnd_1718236] using wordTrace_append hprefix tailTrace_1718236
  have hstable : (prefixWord ++ tailWord_1718236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718236).length < 2 ^ (prefixWord ++ tailWord_1718236).sum := by decide
  have hdescent : baseEnd_1718236 < baseStart_1718236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718320 : List Nat := [2, 1, 1, 1, 2, 14]
def baseStart_1718320 : Nat := 118140960795 + 1718320 * 2 ^ 59
def prefixEnd_1718320 : Nat := 4983230072969 + 3 ^ 40 * 1718320 * 2
def baseEnd_1718320 : Nat := 14523853139651395864981

theorem tailTrace_1718320 : CollatzResearch.WordTrace tailWord_1718320 prefixEnd_1718320 14523853139651395864981 := by
  unfold tailWord_1718320
  simp only [CollatzResearch.WordTrace]
  refine ⟨31336139567413790268556207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41781519423218387024741609 31336139567413790268556207)
  ·
    refine ⟨47004209351120685402834311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31336139567413790268556207 47004209351120685402834311)
    ·
      refine ⟨70506314026681028104251467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47004209351120685402834311 70506314026681028104251467)
      ·
        refine ⟨105759471040021542156377201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70506314026681028104251467 105759471040021542156377201)
        ·
          refine ⟨79319603280016156617282901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105759471040021542156377201 79319603280016156617282901)
          ·
            refine ⟨14523853139651395864981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 79319603280016156617282901 14523853139651395864981)
            ·
              rfl

theorem cell21_1718320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 14].length) (baseStart_1718320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718320 prefixEnd_1718320 := by exact prefixLift 1718320
  have htrace : WordTrace (prefixWord ++ tailWord_1718320) baseStart_1718320 baseEnd_1718320 := by
    simpa [prefixWord, tailWord_1718320, baseEnd_1718320] using wordTrace_append hprefix tailTrace_1718320
  have hstable : (prefixWord ++ tailWord_1718320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718320).length < 2 ^ (prefixWord ++ tailWord_1718320).sum := by decide
  have hdescent : baseEnd_1718320 < baseStart_1718320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718326 : List Nat := [5, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_1718326 : Nat := 118140960795 + 1718326 * 2 ^ 59
def prefixEnd_1718326 : Nat := 4983230072969 + 3 ^ 40 * 1718326 * 2
def baseEnd_1718326 : Nat := 392145404052333011254475

theorem tailTrace_1718326 : CollatzResearch.WordTrace tailWord_1718326 prefixEnd_1718326 392145404052333011254475 := by
  unfold tailWord_1718326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3917031123300365222614427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41781665315203895707887221 3917031123300365222614427)
  ·
    refine ⟨5875546684950547833921641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3917031123300365222614427 5875546684950547833921641)
    ·
      refine ⟨4406660013712910875441231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5875546684950547833921641 4406660013712910875441231)
      ·
        refine ⟨6609990020569366313161847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4406660013712910875441231 6609990020569366313161847)
        ·
          refine ⟨9914985030854049469742771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6609990020569366313161847 9914985030854049469742771)
          ·
            refine ⟨14872477546281074204614157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9914985030854049469742771 14872477546281074204614157)
            ·
              refine ⟨5577179079855402826730309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14872477546281074204614157 5577179079855402826730309)
              ·
                refine ⟨1045721077472888030011933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5577179079855402826730309 1045721077472888030011933)
                ·
                  refine ⟨392145404052333011254475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1045721077472888030011933 392145404052333011254475)
                  ·
                    rfl

theorem cell21_1718326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_1718326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718326 prefixEnd_1718326 := by exact prefixLift 1718326
  have htrace : WordTrace (prefixWord ++ tailWord_1718326) baseStart_1718326 baseEnd_1718326 := by
    simpa [prefixWord, tailWord_1718326, baseEnd_1718326] using wordTrace_append hprefix tailTrace_1718326
  have hstable : (prefixWord ++ tailWord_1718326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718326).length < 2 ^ (prefixWord ++ tailWord_1718326).sum := by decide
  have hdescent : baseEnd_1718326 < baseStart_1718326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718351 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 5]
def baseStart_1718351 : Nat := 118140960795 + 1718351 * 2 ^ 59
def prefixEnd_1718351 : Nat := 4983230072969 + 3 ^ 40 * 1718351 * 2
def baseEnd_1718351 : Nat := 392151109392938523337757

theorem tailTrace_1718351 : CollatzResearch.WordTrace tailWord_1718351 prefixEnd_1718351 392151109392938523337757 := by
  unfold tailWord_1718351
  simp only [CollatzResearch.WordTrace]
  refine ⟨62673409797715272831490907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41782273198476848554327271 62673409797715272831490907)
  ·
    refine ⟨94010114696572909247236361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62673409797715272831490907 94010114696572909247236361)
    ·
      refine ⟨70507586022429681935427271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94010114696572909247236361 70507586022429681935427271)
      ·
        refine ⟨105761379033644522903140907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70507586022429681935427271 105761379033644522903140907)
        ·
          refine ⟨158642068550466784354711361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105761379033644522903140907 158642068550466784354711361)
          ·
            refine ⟨118981551412850088266033521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158642068550466784354711361 118981551412850088266033521)
            ·
              refine ⟨89236163559637566199525141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118981551412850088266033521 89236163559637566199525141)
              ·
                refine ⟨4182945166858010915602741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89236163559637566199525141 4182945166858010915602741)
                ·
                  refine ⟨392151109392938523337757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4182945166858010915602741 392151109392938523337757)
                  ·
                    rfl

theorem cell21_1718351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 5].length) (baseStart_1718351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718351 prefixEnd_1718351 := by exact prefixLift 1718351
  have htrace : WordTrace (prefixWord ++ tailWord_1718351) baseStart_1718351 baseEnd_1718351 := by
    simpa [prefixWord, tailWord_1718351, baseEnd_1718351] using wordTrace_append hprefix tailTrace_1718351
  have hstable : (prefixWord ++ tailWord_1718351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718351).length < 2 ^ (prefixWord ++ tailWord_1718351).sum := by decide
  have hdescent : baseEnd_1718351 < baseStart_1718351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718422 : List Nat := [5, 3, 2, 1, 2, 1, 7]
def baseStart_1718422 : Nat := 118140960795 + 1718422 * 2 ^ 59
def prefixEnd_1718422 : Nat := 4983230072969 + 3 ^ 40 * 1718422 * 2
def baseEnd_1718422 : Nat := 43574145840028686406031

theorem tailTrace_1718422 : CollatzResearch.WordTrace tailWord_1718422 prefixEnd_1718422 43574145840028686406031 := by
  unfold tailWord_1718422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3917249961278628247332845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41783999586972034638217013 3917249961278628247332845)
  ·
    refine ⟨1468968735479485592749817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3917249961278628247332845 1468968735479485592749817)
    ·
      refine ⟨1101726551609614194562363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1468968735479485592749817 1101726551609614194562363)
      ·
        refine ⟨1652589827414421291843545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1101726551609614194562363 1652589827414421291843545)
        ·
          refine ⟨1239442370560815968882659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1652589827414421291843545 1239442370560815968882659)
          ·
            refine ⟨1859163555841223953323989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239442370560815968882659 1859163555841223953323989)
            ·
              refine ⟨43574145840028686406031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1859163555841223953323989 43574145840028686406031)
              ·
                rfl

theorem cell21_1718422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 7].length) (baseStart_1718422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718422 prefixEnd_1718422 := by exact prefixLift 1718422
  have htrace : WordTrace (prefixWord ++ tailWord_1718422) baseStart_1718422 baseEnd_1718422 := by
    simpa [prefixWord, tailWord_1718422, baseEnd_1718422] using wordTrace_append hprefix tailTrace_1718422
  have hstable : (prefixWord ++ tailWord_1718422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718422).length < 2 ^ (prefixWord ++ tailWord_1718422).sum := by decide
  have hdescent : baseEnd_1718422 < baseStart_1718422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718537 : List Nat := [1, 2, 1, 1, 3, 5, 2, 3, 3]
def baseStart_1718537 : Nat := 118140960795 + 1718537 * 2 ^ 59
def prefixEnd_1718537 : Nat := 4983230072969 + 3 ^ 40 * 1718537 * 2
def baseEnd_1718537 : Nat := 392193557127043533237377

theorem tailTrace_1718537 : CollatzResearch.WordTrace tailWord_1718537 prefixEnd_1718537 392193557127043533237377 := by
  unfold tailWord_1718537
  simp only [CollatzResearch.WordTrace]
  refine ⟨62680193775041426597761865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41786795850027617731841243 62680193775041426597761865)
  ·
    refine ⟨47010145331281069948321399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62680193775041426597761865 47010145331281069948321399)
    ·
      refine ⟨70515217996921604922482099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47010145331281069948321399 70515217996921604922482099)
      ·
        refine ⟨105772826995382407383723149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70515217996921604922482099 105772826995382407383723149)
        ·
          refine ⟨39664810123268402768896181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105772826995382407383723149 39664810123268402768896181)
          ·
            refine ⟨3718575949056412759584017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39664810123268402768896181 3718575949056412759584017)
            ·
              refine ⟨2788931961792309569688013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3718575949056412759584017 2788931961792309569688013)
              ·
                refine ⟨1045849485672116088633005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2788931961792309569688013 1045849485672116088633005)
                ·
                  refine ⟨392193557127043533237377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1045849485672116088633005 392193557127043533237377)
                  ·
                    rfl

theorem cell21_1718537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 3].length) (baseStart_1718537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718537 prefixEnd_1718537 := by exact prefixLift 1718537
  have htrace : WordTrace (prefixWord ++ tailWord_1718537) baseStart_1718537 baseEnd_1718537 := by
    simpa [prefixWord, tailWord_1718537, baseEnd_1718537] using wordTrace_append hprefix tailTrace_1718537
  have hstable : (prefixWord ++ tailWord_1718537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718537).length < 2 ^ (prefixWord ++ tailWord_1718537).sum := by decide
  have hdescent : baseEnd_1718537 < baseStart_1718537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718551 : List Nat := [1, 1, 3, 4, 1, 2, 3, 2, 4]
def baseStart_1718551 : Nat := 118140960795 + 1718551 * 2 ^ 59
def prefixEnd_1718551 : Nat := 4983230072969 + 3 ^ 40 * 1718551 * 2
def baseEnd_1718551 : Nat := 392196752117782620004015

theorem tailTrace_1718551 : CollatzResearch.WordTrace tailWord_1718551 prefixEnd_1718551 392196752117782620004015 := by
  unfold tailWord_1718551
  simp only [CollatzResearch.WordTrace]
  refine ⟨62680704396990706988771507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41787136264660471325847671 62680704396990706988771507)
  ·
    refine ⟨94021056595486060483157261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62680704396990706988771507 94021056595486060483157261)
    ·
      refine ⟨35257896223307272681183973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94021056595486060483157261 35257896223307272681183973)
      ·
        refine ⟨6610855541870113627721995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35257896223307272681183973 6610855541870113627721995)
        ·
          refine ⟨9916283312805170441582993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6610855541870113627721995 9916283312805170441582993)
          ·
            refine ⟨7437212484603877831187245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9916283312805170441582993 7437212484603877831187245)
            ·
              refine ⟨2788954681726454186695217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7437212484603877831187245 2788954681726454186695217)
              ·
                refine ⟨2091716011294840640021413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2788954681726454186695217 2091716011294840640021413)
                ·
                  refine ⟨392196752117782620004015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2091716011294840640021413 392196752117782620004015)
                  ·
                    rfl

theorem cell21_1718551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 4].length) (baseStart_1718551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718551 prefixEnd_1718551 := by exact prefixLift 1718551
  have htrace : WordTrace (prefixWord ++ tailWord_1718551) baseStart_1718551 baseEnd_1718551 := by
    simpa [prefixWord, tailWord_1718551, baseEnd_1718551] using wordTrace_append hprefix tailTrace_1718551
  have hstable : (prefixWord ++ tailWord_1718551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718551).length < 2 ^ (prefixWord ++ tailWord_1718551).sum := by decide
  have hdescent : baseEnd_1718551 < baseStart_1718551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718579 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 5]
def baseStart_1718579 : Nat := 118140960795 + 1718579 * 2 ^ 59
def prefixEnd_1718579 : Nat := 4983230072969 + 3 ^ 40 * 1718579 * 2
def baseEnd_1718579 : Nat := 392203142099260793537291

theorem tailTrace_1718579 : CollatzResearch.WordTrace tailWord_1718579 prefixEnd_1718579 392203142099260793537291 := by
  unfold tailWord_1718579
  simp only [CollatzResearch.WordTrace]
  refine ⟨62681725640889267770790791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41787817093926178513860527 62681725640889267770790791)
  ·
    refine ⟨94022588461333901656186187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62681725640889267770790791 94022588461333901656186187)
    ·
      refine ⟨141033882692000852484279281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94022588461333901656186187 141033882692000852484279281)
      ·
        refine ⟨105775412019000639363209461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141033882692000852484279281 105775412019000639363209461)
        ·
          refine ⟨9916444876781309940300887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105775412019000639363209461 9916444876781309940300887)
          ·
            refine ⟨14874667315171964910451331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9916444876781309940300887 14874667315171964910451331)
            ·
              refine ⟨22312000972757947365676997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14874667315171964910451331 22312000972757947365676997)
              ·
                refine ⟨4183500182392115131064437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22312000972757947365676997 4183500182392115131064437)
                ·
                  refine ⟨392203142099260793537291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4183500182392115131064437 392203142099260793537291)
                  ·
                    rfl

theorem cell21_1718579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 5].length) (baseStart_1718579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718579 prefixEnd_1718579 := by exact prefixLift 1718579
  have htrace : WordTrace (prefixWord ++ tailWord_1718579) baseStart_1718579 baseEnd_1718579 := by
    simpa [prefixWord, tailWord_1718579, baseEnd_1718579] using wordTrace_append hprefix tailTrace_1718579
  have hstable : (prefixWord ++ tailWord_1718579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718579).length < 2 ^ (prefixWord ++ tailWord_1718579).sum := by decide
  have hdescent : baseEnd_1718579 < baseStart_1718579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718610 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 6]
def baseStart_1718610 : Nat := 118140960795 + 1718610 * 2 ^ 59
def prefixEnd_1718610 : Nat := 4983230072969 + 3 ^ 40 * 1718610 * 2
def baseEnd_1718610 : Nat := 392210216721611628520561

theorem tailTrace_1718610 : CollatzResearch.WordTrace tailWord_1718610 prefixEnd_1718610 392210216721611628520561 := by
  unfold tailWord_1718610
  simp only [CollatzResearch.WordTrace]
  refine ⟨15670714075944240016292321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41788570869184640043446189 15670714075944240016292321)
  ·
    refine ⟨11753035556958180012219241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15670714075944240016292321 11753035556958180012219241)
    ·
      refine ⟨8814776667718635009164431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11753035556958180012219241 8814776667718635009164431)
      ·
        refine ⟨13222165001577952513746647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8814776667718635009164431 13222165001577952513746647)
        ·
          refine ⟨19833247502366928770619971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13222165001577952513746647 19833247502366928770619971)
          ·
            refine ⟨29749871253550393155929957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19833247502366928770619971 29749871253550393155929957)
            ·
              refine ⟨5578100860040698716736867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29749871253550393155929957 5578100860040698716736867)
              ·
                refine ⟨8367151290061048075105301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5578100860040698716736867 8367151290061048075105301)
                ·
                  refine ⟨392210216721611628520561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8367151290061048075105301 392210216721611628520561)
                  ·
                    rfl

theorem cell21_1718610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_1718610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718610 prefixEnd_1718610 := by exact prefixLift 1718610
  have htrace : WordTrace (prefixWord ++ tailWord_1718610) baseStart_1718610 baseEnd_1718610 := by
    simpa [prefixWord, tailWord_1718610, baseEnd_1718610] using wordTrace_append hprefix tailTrace_1718610
  have hstable : (prefixWord ++ tailWord_1718610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718610).length < 2 ^ (prefixWord ++ tailWord_1718610).sum := by decide
  have hdescent : baseEnd_1718610 < baseStart_1718610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718613 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 5]
def baseStart_1718613 : Nat := 118140960795 + 1718613 * 2 ^ 59
def prefixEnd_1718613 : Nat := 4983230072969 + 3 ^ 40 * 1718613 * 2
def baseEnd_1718613 : Nat := 392210901362484289970555

theorem tailTrace_1718613 : CollatzResearch.WordTrace tailWord_1718613 prefixEnd_1718613 392210901362484289970555 := by
  unfold tailWord_1718613
  simp only [CollatzResearch.WordTrace]
  refine ⟨62682965722766091577528493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41788643815177394385018995 62682965722766091577528493)
  ·
    refine ⟨23506112146037284341573185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62682965722766091577528493 23506112146037284341573185)
    ·
      refine ⟨17629584109527963256179889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23506112146037284341573185 17629584109527963256179889)
      ·
        refine ⟨13222188082145972442134917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17629584109527963256179889 13222188082145972442134917)
        ·
          refine ⟨2479160265402369832900297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13222188082145972442134917 2479160265402369832900297)
          ·
            refine ⟨1859370199051777374675223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2479160265402369832900297 1859370199051777374675223)
            ·
              refine ⟨2789055298577666062012835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1859370199051777374675223 2789055298577666062012835)
              ·
                refine ⟨4183582947866499093019253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2789055298577666062012835 4183582947866499093019253)
                ·
                  refine ⟨392210901362484289970555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4183582947866499093019253 392210901362484289970555)
                  ·
                    rfl

theorem cell21_1718613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_1718613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718613 prefixEnd_1718613 := by exact prefixLift 1718613
  have htrace : WordTrace (prefixWord ++ tailWord_1718613) baseStart_1718613 baseEnd_1718613 := by
    simpa [prefixWord, tailWord_1718613, baseEnd_1718613] using wordTrace_append hprefix tailTrace_1718613
  have hstable : (prefixWord ++ tailWord_1718613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718613).length < 2 ^ (prefixWord ++ tailWord_1718613).sum := by decide
  have hdescent : baseEnd_1718613 < baseStart_1718613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718658 : List Nat := [3, 4, 2, 1, 2, 9]
def baseStart_1718658 : Nat := 118140960795 + 1718658 * 2 ^ 59
def prefixEnd_1718658 : Nat := 4983230072969 + 3 ^ 40 * 1718658 * 2
def baseEnd_1718658 : Nat := 14526710036132378211869

theorem tailTrace_1718658 : CollatzResearch.WordTrace tailWord_1718658 prefixEnd_1718658 14526710036132378211869 := by
  unfold tailWord_1718658
  simp only [CollatzResearch.WordTrace]
  refine ⟨15671151751900766065729157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41789738005068709508611085 15671151751900766065729157)
  ·
    refine ⟨2938340953481393637324217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15671151751900766065729157 2938340953481393637324217)
    ·
      refine ⟨2203755715111045227993163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2938340953481393637324217 2203755715111045227993163)
      ·
        refine ⟨3305633572666567841989745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2203755715111045227993163 3305633572666567841989745)
        ·
          refine ⟨2479225179499925881492309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3305633572666567841989745 2479225179499925881492309)
          ·
            refine ⟨14526710036132378211869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2479225179499925881492309 14526710036132378211869)
            ·
              rfl

theorem cell21_1718658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 9].length) (baseStart_1718658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718658 prefixEnd_1718658 := by exact prefixLift 1718658
  have htrace : WordTrace (prefixWord ++ tailWord_1718658) baseStart_1718658 baseEnd_1718658 := by
    simpa [prefixWord, tailWord_1718658, baseEnd_1718658] using wordTrace_append hprefix tailTrace_1718658
  have hstable : (prefixWord ++ tailWord_1718658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718658).length < 2 ^ (prefixWord ++ tailWord_1718658).sum := by decide
  have hdescent : baseEnd_1718658 < baseStart_1718658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718689 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 5]
def baseStart_1718689 : Nat := 118140960795 + 1718689 * 2 ^ 59
def prefixEnd_1718689 : Nat := 4983230072969 + 3 ^ 40 * 1718689 * 2
def baseEnd_1718689 : Nat := 392228245597925046703733

theorem tailTrace_1718689 : CollatzResearch.WordTrace tailWord_1718689 prefixEnd_1718689 392228245597925046703733 := by
  unfold tailWord_1718689
  simp only [CollatzResearch.WordTrace]
  refine ⟨62685737670490756557295121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41790491780327171038196747 62685737670490756557295121)
  ·
    refine ⟨47014303252868067417971341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62685737670490756557295121 47014303252868067417971341)
    ·
      refine ⟨17630363719825525281739253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47014303252868067417971341 17630363719825525281739253)
      ·
        refine ⟨1652846598733642995163055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17630363719825525281739253 1652846598733642995163055)
        ·
          refine ⟨2479269898100464492744583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1652846598733642995163055 2479269898100464492744583)
          ·
            refine ⟨3718904847150696739116875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2479269898100464492744583 3718904847150696739116875)
            ·
              refine ⟨5578357270726045108675313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3718904847150696739116875 5578357270726045108675313)
              ·
                refine ⟨4183767953044533831506485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5578357270726045108675313 4183767953044533831506485)
                ·
                  refine ⟨392228245597925046703733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4183767953044533831506485 392228245597925046703733)
                  ·
                    rfl

theorem cell21_1718689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_1718689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718689 prefixEnd_1718689 := by exact prefixLift 1718689
  have htrace : WordTrace (prefixWord ++ tailWord_1718689) baseStart_1718689 baseEnd_1718689 := by
    simpa [prefixWord, tailWord_1718689, baseEnd_1718689] using wordTrace_append hprefix tailTrace_1718689
  have hstable : (prefixWord ++ tailWord_1718689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718689).length < 2 ^ (prefixWord ++ tailWord_1718689).sum := by decide
  have hdescent : baseEnd_1718689 < baseStart_1718689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718762 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 6]
def baseStart_1718762 : Nat := 118140960795 + 1718762 * 2 ^ 59
def prefixEnd_1718762 : Nat := 4983230072969 + 3 ^ 40 * 1718762 * 2
def baseEnd_1718762 : Nat := 392244905192493141986917

theorem tailTrace_1718762 : CollatzResearch.WordTrace tailWord_1718762 prefixEnd_1718762 392244905192493141986917 := by
  unfold tailWord_1718762
  simp only [CollatzResearch.WordTrace]
  refine ⟨15672100049806572506175635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41792266799484193349801693 15672100049806572506175635)
  ·
    refine ⟨23508150074709858759263453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15672100049806572506175635 23508150074709858759263453)
    ·
      refine ⟨8815556278016197034723795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23508150074709858759263453 8815556278016197034723795)
      ·
        refine ⟨13223334417024295552085693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8815556278016197034723795 13223334417024295552085693)
        ·
          refine ⟨4958750406384110832032135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13223334417024295552085693 4958750406384110832032135)
          ·
            refine ⟨7438125609576166248048203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4958750406384110832032135 7438125609576166248048203)
            ·
              refine ⟨11157188414364249372072305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7438125609576166248048203 11157188414364249372072305)
              ·
                refine ⟨8367891310773187029054229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11157188414364249372072305 8367891310773187029054229)
                ·
                  refine ⟨392244905192493141986917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8367891310773187029054229 392244905192493141986917)
                  ·
                    rfl

theorem cell21_1718762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_1718762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718762 prefixEnd_1718762 := by exact prefixLift 1718762
  have htrace : WordTrace (prefixWord ++ tailWord_1718762) baseStart_1718762 baseEnd_1718762 := by
    simpa [prefixWord, tailWord_1718762, baseEnd_1718762] using wordTrace_append hprefix tailTrace_1718762
  have hstable : (prefixWord ++ tailWord_1718762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718762).length < 2 ^ (prefixWord ++ tailWord_1718762).sum := by decide
  have hdescent : baseEnd_1718762 < baseStart_1718762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718796 : List Nat := [2, 2, 1, 2, 4, 3, 2, 1, 4]
def baseStart_1718796 : Nat := 118140960795 + 1718796 * 2 ^ 59
def prefixEnd_1718796 : Nat := 4983230072969 + 3 ^ 40 * 1718796 * 2
def baseEnd_1718796 : Nat := 392252664455716638420181

theorem tailTrace_1718796 : CollatzResearch.WordTrace tailWord_1718796 prefixEnd_1718796 392252664455716638420181 := by
  unfold tailWord_1718796
  simp only [CollatzResearch.WordTrace]
  refine ⟨31344820140551556915720121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41793093520735409220960161 31344820140551556915720121)
  ·
    refine ⟨23508615105413667686790091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31344820140551556915720121 23508615105413667686790091)
    ·
      refine ⟨35262922658120501530185137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23508615105413667686790091 35262922658120501530185137)
      ·
        refine ⟨26447191993590376147638853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35262922658120501530185137 26447191993590376147638853)
        ·
          refine ⟨4958848498798195527682285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26447191993590376147638853 4958848498798195527682285)
          ·
            refine ⟨1859568187049323322880857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4958848498798195527682285 1859568187049323322880857)
            ·
              refine ⟨1394676140286992492160643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1859568187049323322880857 1394676140286992492160643)
              ·
                refine ⟨2092014210430488738240965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1394676140286992492160643 2092014210430488738240965)
                ·
                  refine ⟨392252664455716638420181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2092014210430488738240965 392252664455716638420181)
                  ·
                    rfl

theorem cell21_1718796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_1718796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718796 prefixEnd_1718796 := by exact prefixLift 1718796
  have htrace : WordTrace (prefixWord ++ tailWord_1718796) baseStart_1718796 baseEnd_1718796 := by
    simpa [prefixWord, tailWord_1718796, baseEnd_1718796] using wordTrace_append hprefix tailTrace_1718796
  have hstable : (prefixWord ++ tailWord_1718796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718796).length < 2 ^ (prefixWord ++ tailWord_1718796).sum := by decide
  have hdescent : baseEnd_1718796 < baseStart_1718796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718821 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 8]
def baseStart_1718821 : Nat := 118140960795 + 1718821 * 2 ^ 59
def prefixEnd_1718821 : Nat := 4983230072969 + 3 ^ 40 * 1718821 * 2
def baseEnd_1718821 : Nat := 392258369796322150503463

theorem tailTrace_1718821 : CollatzResearch.WordTrace tailWord_1718821 prefixEnd_1718821 392258369796322150503463 := by
  unfold tailWord_1718821
  simp only [CollatzResearch.WordTrace]
  refine ⟨62690552106012543101100317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41793701404008362067400211 62690552106012543101100317)
  ·
    refine ⟨23508957039754703662912619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62690552106012543101100317 23508957039754703662912619)
    ·
      refine ⟨35263435559632055494368929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23508957039754703662912619 35263435559632055494368929)
      ·
        refine ⟨26447576669724041620776697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35263435559632055494368929 26447576669724041620776697)
        ·
          refine ⟨19835682502293031215582523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26447576669724041620776697 19835682502293031215582523)
          ·
            refine ⟨29753523753439546823373785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19835682502293031215582523 29753523753439546823373785)
            ·
              refine ⟨22315142815079660117530339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29753523753439546823373785 22315142815079660117530339)
              ·
                refine ⟨33472714222619490176295509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22315142815079660117530339 33472714222619490176295509)
                ·
                  refine ⟨392258369796322150503463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33472714222619490176295509 392258369796322150503463)
                  ·
                    rfl

theorem cell21_1718821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_1718821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718821 prefixEnd_1718821 := by exact prefixLift 1718821
  have htrace : WordTrace (prefixWord ++ tailWord_1718821) baseStart_1718821 baseEnd_1718821 := by
    simpa [prefixWord, tailWord_1718821, baseEnd_1718821] using wordTrace_append hprefix tailTrace_1718821
  have hstable : (prefixWord ++ tailWord_1718821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718821).length < 2 ^ (prefixWord ++ tailWord_1718821).sum := by decide
  have hdescent : baseEnd_1718821 < baseStart_1718821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718945 : List Nat := [1, 2, 3, 3, 3, 2, 7]
def baseStart_1718945 : Nat := 118140960795 + 1718945 * 2 ^ 59
def prefixEnd_1718945 : Nat := 4983230072969 + 3 ^ 40 * 1718945 * 2
def baseEnd_1718945 : Nat := 43587407587302832270727

theorem tailTrace_1718945 : CollatzResearch.WordTrace tailWord_1718945 prefixEnd_1718945 43587407587302832270727 := by
  unfold tailWord_1718945
  simp only [CollatzResearch.WordTrace]
  refine ⟨62695074757563312278614289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41796716505042208185742859 62695074757563312278614289)
  ·
    refine ⟨47021306068172484208960717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62695074757563312278614289 47021306068172484208960717)
    ·
      refine ⟨17632989775564681578360269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47021306068172484208960717 17632989775564681578360269)
      ·
        refine ⟨6612371165836755591885101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17632989775564681578360269 6612371165836755591885101)
        ·
          refine ⟨2479639187188783346956913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6612371165836755591885101 2479639187188783346956913)
          ·
            refine ⟨1859729390391587510217685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2479639187188783346956913 1859729390391587510217685)
            ·
              refine ⟨43587407587302832270727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1859729390391587510217685 43587407587302832270727)
              ·
                rfl

theorem cell21_1718945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 7].length) (baseStart_1718945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718945 prefixEnd_1718945 := by exact prefixLift 1718945
  have htrace : WordTrace (prefixWord ++ tailWord_1718945) baseStart_1718945 baseEnd_1718945 := by
    simpa [prefixWord, tailWord_1718945, baseEnd_1718945] using wordTrace_append hprefix tailTrace_1718945
  have hstable : (prefixWord ++ tailWord_1718945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718945).length < 2 ^ (prefixWord ++ tailWord_1718945).sum := by decide
  have hdescent : baseEnd_1718945 < baseStart_1718945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718951 : List Nat := [1, 1, 6, 3, 1, 1, 3, 2, 3]
def baseStart_1718951 : Nat := 118140960795 + 1718951 * 2 ^ 59
def prefixEnd_1718951 : Nat := 4983230072969 + 3 ^ 40 * 1718951 * 2
def baseEnd_1718951 : Nat := 392288037567470813336531

theorem tailTrace_1718951 : CollatzResearch.WordTrace tailWord_1718951 prefixEnd_1718951 392288037567470813336531 := by
  unfold tailWord_1718951
  simp only [CollatzResearch.WordTrace]
  refine ⟨62695293595541575303332707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41796862397027716868888471 62695293595541575303332707)
  ·
    refine ⟨94042940393312362954999061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62695293595541575303332707 94042940393312362954999061)
    ·
      refine ⟨4408262830936517013515581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94042940393312362954999061 4408262830936517013515581)
      ·
        refine ⟨1653098561601193880068343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4408262830936517013515581 1653098561601193880068343)
        ·
          refine ⟨2479647842401790820102515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1653098561601193880068343 2479647842401790820102515)
          ·
            refine ⟨3719471763602686230153773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2479647842401790820102515 3719471763602686230153773)
            ·
              refine ⟨1394801911351007336307665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3719471763602686230153773 1394801911351007336307665)
              ·
                refine ⟨1046101433513255502230749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1394801911351007336307665 1046101433513255502230749)
                ·
                  refine ⟨392288037567470813336531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046101433513255502230749 392288037567470813336531)
                  ·
                    rfl

theorem cell21_1718951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 3].length) (baseStart_1718951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718951 prefixEnd_1718951 := by exact prefixLift 1718951
  have htrace : WordTrace (prefixWord ++ tailWord_1718951) baseStart_1718951 baseEnd_1718951 := by
    simpa [prefixWord, tailWord_1718951, baseEnd_1718951] using wordTrace_append hprefix tailTrace_1718951
  have hstable : (prefixWord ++ tailWord_1718951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718951).length < 2 ^ (prefixWord ++ tailWord_1718951).sum := by decide
  have hdescent : baseEnd_1718951 < baseStart_1718951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718959 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 5]
def baseStart_1718959 : Nat := 118140960795 + 1718959 * 2 ^ 59
def prefixEnd_1718959 : Nat := 4983230072969 + 3 ^ 40 * 1718959 * 2
def baseEnd_1718959 : Nat := 392289863276464577203181

theorem tailTrace_1718959 : CollatzResearch.WordTrace tailWord_1718959 prefixEnd_1718959 392289863276464577203181 := by
  unfold tailWord_1718959
  simp only [CollatzResearch.WordTrace]
  refine ⟨62695585379512592669623931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41797056919675061779749287 62695585379512592669623931)
  ·
    refine ⟨94043378069268889004435897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62695585379512592669623931 94043378069268889004435897)
    ·
      refine ⟨70532533551951666753326923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94043378069268889004435897 70532533551951666753326923)
      ·
        refine ⟨105798800327927500129990385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70532533551951666753326923 105798800327927500129990385)
        ·
          refine ⟨79349100245945625097492789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105798800327927500129990385 79349100245945625097492789)
          ·
            refine ⟨7438978148057402352889949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79349100245945625097492789 7438978148057402352889949)
            ·
              refine ⟨2789616805521525882333731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7438978148057402352889949 2789616805521525882333731)
              ·
                refine ⟨4184425208282288823500597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2789616805521525882333731 4184425208282288823500597)
                ·
                  refine ⟨392289863276464577203181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4184425208282288823500597 392289863276464577203181)
                  ·
                    rfl

theorem cell21_1718959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 5].length) (baseStart_1718959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1718959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1718959 prefixEnd_1718959 := by exact prefixLift 1718959
  have htrace : WordTrace (prefixWord ++ tailWord_1718959) baseStart_1718959 baseEnd_1718959 := by
    simpa [prefixWord, tailWord_1718959, baseEnd_1718959] using wordTrace_append hprefix tailTrace_1718959
  have hstable : (prefixWord ++ tailWord_1718959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718959).length < 2 ^ (prefixWord ++ tailWord_1718959).sum := by decide
  have hdescent : baseEnd_1718959 < baseStart_1718959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719038 : List Nat := [4, 2, 2, 1, 2, 2, 3, 5]
def baseStart_1719038 : Nat := 118140960795 + 1719038 * 2 ^ 59
def prefixEnd_1719038 : Nat := 4983230072969 + 3 ^ 40 * 1719038 * 2
def baseEnd_1719038 : Nat := 130769297384259331795451

theorem tailTrace_1719038 : CollatzResearch.WordTrace tailWord_1719038 prefixEnd_1719038 130769297384259331795451 := by
  unfold tailWord_1719038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7837308343278298645218721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41798977830817592774499845 7837308343278298645218721)
  ·
    refine ⟨5877981257458723983914041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7837308343278298645218721 5877981257458723983914041)
    ·
      refine ⟨4408485943094042987935531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5877981257458723983914041 4408485943094042987935531)
      ·
        refine ⟨6612728914641064481903297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4408485943094042987935531 6612728914641064481903297)
        ·
          refine ⟨4959546685980798361427473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6612728914641064481903297 4959546685980798361427473)
          ·
            refine ⟨3719660014485598771070605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4959546685980798361427473 3719660014485598771070605)
            ·
              refine ⟨1394872505432099539151477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3719660014485598771070605 1394872505432099539151477)
              ·
                refine ⟨130769297384259331795451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1394872505432099539151477 130769297384259331795451)
                ·
                  rfl

theorem cell21_1719038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_1719038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719038 prefixEnd_1719038 := by exact prefixLift 1719038
  have htrace : WordTrace (prefixWord ++ tailWord_1719038) baseStart_1719038 baseEnd_1719038 := by
    simpa [prefixWord, tailWord_1719038, baseEnd_1719038] using wordTrace_append hprefix tailTrace_1719038
  have hstable : (prefixWord ++ tailWord_1719038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719038).length < 2 ^ (prefixWord ++ tailWord_1719038).sum := by decide
  have hdescent : baseEnd_1719038 < baseStart_1719038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719069 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 5]
def baseStart_1719069 : Nat := 118140960795 + 1719069 * 2 ^ 59
def prefixEnd_1719069 : Nat := 4983230072969 + 3 ^ 40 * 1719069 * 2
def baseEnd_1719069 : Nat := 392314966775128830369623

theorem tailTrace_1719069 : CollatzResearch.WordTrace tailWord_1719069 prefixEnd_1719069 392314966775128830369623 := by
  unfold tailWord_1719069
  simp only [CollatzResearch.WordTrace]
  refine ⟨62699597409114081456128261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41799731606076054304085507 62699597409114081456128261)
  ·
    refine ⟨11756174514208890273024049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62699597409114081456128261 11756174514208890273024049)
    ·
      refine ⟨8817130885656667704768037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11756174514208890273024049 8817130885656667704768037)
      ·
        refine ⟨1653212041060625194644007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8817130885656667704768037 1653212041060625194644007)
        ·
          refine ⟨2479818061590937791966011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1653212041060625194644007 2479818061590937791966011)
          ·
            refine ⟨3719727092386406687949017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2479818061590937791966011 3719727092386406687949017)
            ·
              refine ⟨2789795319289805015961763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3719727092386406687949017 2789795319289805015961763)
              ·
                refine ⟨4184692978934707523942645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2789795319289805015961763 4184692978934707523942645)
                ·
                  refine ⟨392314966775128830369623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4184692978934707523942645 392314966775128830369623)
                  ·
                    rfl

theorem cell21_1719069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_1719069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719069 prefixEnd_1719069 := by exact prefixLift 1719069
  have htrace : WordTrace (prefixWord ++ tailWord_1719069) baseStart_1719069 baseEnd_1719069 := by
    simpa [prefixWord, tailWord_1719069, baseEnd_1719069] using wordTrace_append hprefix tailTrace_1719069
  have hstable : (prefixWord ++ tailWord_1719069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719069).length < 2 ^ (prefixWord ++ tailWord_1719069).sum := by decide
  have hdescent : baseEnd_1719069 < baseStart_1719069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719080 : List Nat := [2, 1, 5, 1, 1, 1, 2, 8]
def baseStart_1719080 : Nat := 118140960795 + 1719080 * 2 ^ 59
def prefixEnd_1719080 : Nat := 4983230072969 + 3 ^ 40 * 1719080 * 2
def baseEnd_1719080 : Nat := 130772492374998418562089

theorem tailTrace_1719080 : CollatzResearch.WordTrace tailWord_1719080 prefixEnd_1719080 130772492374998418562089 := by
  unfold tailWord_1719080
  simp only [CollatzResearch.WordTrace]
  refine ⟨31349999306037115167389347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41799999074716153556519129 31349999306037115167389347)
  ·
    refine ⟨47024998959055672751084021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31349999306037115167389347 47024998959055672751084021)
    ·
      refine ⟨4408593652411469320414127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47024998959055672751084021 4408593652411469320414127)
      ·
        refine ⟨6612890478617203980621191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4408593652411469320414127 6612890478617203980621191)
        ·
          refine ⟨9919335717925805970931787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6612890478617203980621191 9919335717925805970931787)
          ·
            refine ⟨14879003576888708956397681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9919335717925805970931787 14879003576888708956397681)
            ·
              refine ⟨11159252682666531717298261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14879003576888708956397681 11159252682666531717298261)
              ·
                refine ⟨130772492374998418562089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11159252682666531717298261 130772492374998418562089)
                ·
                  rfl

theorem cell21_1719080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 8].length) (baseStart_1719080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719080 prefixEnd_1719080 := by exact prefixLift 1719080
  have htrace : WordTrace (prefixWord ++ tailWord_1719080) baseStart_1719080 baseEnd_1719080 := by
    simpa [prefixWord, tailWord_1719080, baseEnd_1719080] using wordTrace_append hprefix tailTrace_1719080
  have hstable : (prefixWord ++ tailWord_1719080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719080).length < 2 ^ (prefixWord ++ tailWord_1719080).sum := by decide
  have hdescent : baseEnd_1719080 < baseStart_1719080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719125 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 6]
def baseStart_1719125 : Nat := 118140960795 + 1719125 * 2 ^ 59
def prefixEnd_1719125 : Nat := 4983230072969 + 3 ^ 40 * 1719125 * 2
def baseEnd_1719125 : Nat := 392327746738085177436175

theorem tailTrace_1719125 : CollatzResearch.WordTrace tailWord_1719125 prefixEnd_1719125 392327746738085177436175 := by
  unfold tailWord_1719125
  simp only [CollatzResearch.WordTrace]
  refine ⟨62701639896911203020166829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41801093264607468680111219 62701639896911203020166829)
  ·
    refine ⟨23513114961341701132562561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62701639896911203020166829 23513114961341701132562561)
    ·
      refine ⟨17634836221006275849421921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23513114961341701132562561 17634836221006275849421921)
      ·
        refine ⟨13226127165754706887066441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17634836221006275849421921 13226127165754706887066441)
        ·
          refine ⟨9919595374316030165299831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13226127165754706887066441 9919595374316030165299831)
          ·
            refine ⟨14879393061474045247949747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9919595374316030165299831 14879393061474045247949747)
            ·
              refine ⟨22319089592211067871924621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14879393061474045247949747 22319089592211067871924621)
              ·
                refine ⟨8369658597079150451971733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22319089592211067871924621 8369658597079150451971733)
                ·
                  refine ⟨392327746738085177436175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8369658597079150451971733 392327746738085177436175)
                  ·
                    rfl

theorem cell21_1719125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_1719125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719125 prefixEnd_1719125 := by exact prefixLift 1719125
  have htrace : WordTrace (prefixWord ++ tailWord_1719125) baseStart_1719125 baseEnd_1719125 := by
    simpa [prefixWord, tailWord_1719125, baseEnd_1719125] using wordTrace_append hprefix tailTrace_1719125
  have hstable : (prefixWord ++ tailWord_1719125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719125).length < 2 ^ (prefixWord ++ tailWord_1719125).sum := by decide
  have hdescent : baseEnd_1719125 < baseStart_1719125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719266 : List Nat := [3, 3, 3, 1, 1, 1, 4, 5]
def baseStart_1719266 : Nat := 118140960795 + 1719266 * 2 ^ 59
def prefixEnd_1719266 : Nat := 4983230072969 + 3 ^ 40 * 1719266 * 2
def baseEnd_1719266 : Nat := 130786641619700088528629

theorem tailTrace_1719266 : CollatzResearch.WordTrace tailWord_1719266 prefixEnd_1719266 130786641619700088528629 := by
  unfold tailWord_1719266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15676695647350096025262413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41804521726266922734033101 15676695647350096025262413)
  ·
    refine ⟨5878760867756286009473405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15676695647350096025262413 5878760867756286009473405)
    ·
      refine ⟨2204535325408607253552527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5878760867756286009473405 2204535325408607253552527)
      ·
        refine ⟨3306802988112910880328791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2204535325408607253552527 3306802988112910880328791)
        ·
          refine ⟨4960204482169366320493187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3306802988112910880328791 4960204482169366320493187)
          ·
            refine ⟨7440306723254049480739781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4960204482169366320493187 7440306723254049480739781)
            ·
              refine ⟨1395057510610134277638709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7440306723254049480739781 1395057510610134277638709)
              ·
                refine ⟨130786641619700088528629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1395057510610134277638709 130786641619700088528629)
                ·
                  rfl

theorem cell21_1719266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_1719266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719266 prefixEnd_1719266 := by exact prefixLift 1719266
  have htrace : WordTrace (prefixWord ++ tailWord_1719266) baseStart_1719266 baseEnd_1719266 := by
    simpa [prefixWord, tailWord_1719266, baseEnd_1719266] using wordTrace_append hprefix tailTrace_1719266
  have hstable : (prefixWord ++ tailWord_1719266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719266).length < 2 ^ (prefixWord ++ tailWord_1719266).sum := by decide
  have hdescent : baseEnd_1719266 < baseStart_1719266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719297 : List Nat := [1, 2, 4, 1, 2, 3, 3, 2, 3]
def baseStart_1719297 : Nat := 118140960795 + 1719297 * 2 ^ 59
def prefixEnd_1719297 : Nat := 4983230072969 + 3 ^ 40 * 1719297 * 2
def baseEnd_1719297 : Nat := 392366999481451100569157

theorem tailTrace_1719297 : CollatzResearch.WordTrace tailWord_1719297 prefixEnd_1719297 392366999481451100569157 := by
  unfold tailWord_1719297
  simp only [CollatzResearch.WordTrace]
  refine ⟨62707913252288076395428145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41805275501525384263618763 62707913252288076395428145)
  ·
    refine ⟨47030934939216057296571109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62707913252288076395428145 47030934939216057296571109)
    ·
      refine ⟨8818300301103010743107083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47030934939216057296571109 8818300301103010743107083)
      ·
        refine ⟨13227450451654516114660625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8818300301103010743107083 13227450451654516114660625)
        ·
          refine ⟨9920587838740887085995469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13227450451654516114660625 9920587838740887085995469)
          ·
            refine ⟨3720220439527832657248301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9920587838740887085995469 3720220439527832657248301)
            ·
              refine ⟨1395082664822937246468113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3720220439527832657248301 1395082664822937246468113)
              ·
                refine ⟨1046311998617202934851085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395082664822937246468113 1046311998617202934851085)
                ·
                  refine ⟨392366999481451100569157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046311998617202934851085 392366999481451100569157)
                  ·
                    rfl

theorem cell21_1719297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 3].length) (baseStart_1719297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719297 prefixEnd_1719297 := by exact prefixLift 1719297
  have htrace : WordTrace (prefixWord ++ tailWord_1719297) baseStart_1719297 baseEnd_1719297 := by
    simpa [prefixWord, tailWord_1719297, baseEnd_1719297] using wordTrace_append hprefix tailTrace_1719297
  have hstable : (prefixWord ++ tailWord_1719297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719297).length < 2 ^ (prefixWord ++ tailWord_1719297).sum := by decide
  have hdescent : baseEnd_1719297 < baseStart_1719297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719308 : List Nat := [2, 2, 1, 2, 3, 3, 2, 6]
def baseStart_1719308 : Nat := 118140960795 + 1719308 * 2 ^ 59
def prefixEnd_1719308 : Nat := 4983230072969 + 3 ^ 40 * 1719308 * 2
def baseEnd_1719308 : Nat := 130789836610439175295267

theorem tailTrace_1719308 : CollatzResearch.WordTrace tailWord_1719308 prefixEnd_1719308 130789836610439175295267 := by
  unfold tailWord_1719308
  simp only [CollatzResearch.WordTrace]
  refine ⟨31354157227624112637039289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41805542970165483516052385 31354157227624112637039289)
  ·
    refine ⟨23515617920718084477779467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31354157227624112637039289 23515617920718084477779467)
    ·
      refine ⟨35273426881077126716669201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23515617920718084477779467 35273426881077126716669201)
      ·
        refine ⟨26455070160807845037501901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35273426881077126716669201 26455070160807845037501901)
        ·
          refine ⟨9920651310302941889063213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26455070160807845037501901 9920651310302941889063213)
          ·
            refine ⟨3720244241363603208398705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9920651310302941889063213 3720244241363603208398705)
            ·
              refine ⟨2790183181022702406299029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3720244241363603208398705 2790183181022702406299029)
              ·
                refine ⟨130789836610439175295267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2790183181022702406299029 130789836610439175295267)
                ·
                  rfl

theorem cell21_1719308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 6].length) (baseStart_1719308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1719308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1719308 prefixEnd_1719308 := by exact prefixLift 1719308
  have htrace : WordTrace (prefixWord ++ tailWord_1719308) baseStart_1719308 baseEnd_1719308 := by
    simpa [prefixWord, tailWord_1719308, baseEnd_1719308] using wordTrace_append hprefix tailTrace_1719308
  have hstable : (prefixWord ++ tailWord_1719308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719308).length < 2 ^ (prefixWord ++ tailWord_1719308).sum := by decide
  have hdescent : baseEnd_1719308 < baseStart_1719308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
