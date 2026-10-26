import V185TrunkScan23Chunk1034

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6127592 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_6127592 : Nat := 118140960795 + 6127592 * 2 ^ 59
def prefixEnd_6127592 : Nat := 4983230072969 + 3 ^ 40 * 6127592 * 2
def baseEnd_6127592 : Nat := 3146399950645095001819723

theorem tailTrace_6127592 : CollatzResearch.WordTrace tailWord_6127592 prefixEnd_6127592 3146399950645095001819723 := by
  unfold tailWord_6127592
  simp only [CollatzResearch.WordTrace]
  refine ⟨111745820408394084120920515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148994427211192112161227353 111745820408394084120920515)
  ·
    refine ⟨167618730612591126181380773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111745820408394084120920515 167618730612591126181380773)
    ·
      refine ⟨31428511989860836159008895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167618730612591126181380773 31428511989860836159008895)
      ·
        refine ⟨47142767984791254238513343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31428511989860836159008895 47142767984791254238513343)
        ·
          refine ⟨70714151977186881357770015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47142767984791254238513343 70714151977186881357770015)
          ·
            refine ⟨106071227965780322036655023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70714151977186881357770015 106071227965780322036655023)
            ·
              refine ⟨159106841948670483054982535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106071227965780322036655023 159106841948670483054982535)
              ·
                refine ⟨238660262923005724582473803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159106841948670483054982535 238660262923005724582473803)
                ·
                  refine ⟨357990394384508586873710705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238660262923005724582473803 357990394384508586873710705)
                  ·
                    refine ⟨268492795788381440155283029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 357990394384508586873710705 268492795788381440155283029)
                    ·
                      refine ⟨3146399950645095001819723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 268492795788381440155283029 3146399950645095001819723)
                      ·
                        rfl

theorem cell23_6127592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_6127592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127592 prefixEnd_6127592 := by exact prefixLift 6127592
  have htrace : WordTrace (prefixWord ++ tailWord_6127592) baseStart_6127592 baseEnd_6127592 := by
    simpa [prefixWord, tailWord_6127592, baseEnd_6127592] using wordTrace_append hprefix tailTrace_6127592
  have hstable : (prefixWord ++ tailWord_6127592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127592).length < 2 ^ (prefixWord ++ tailWord_6127592).sum := by decide
  have hdescent : baseEnd_6127592 < baseStart_6127592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127666 : List Nat := [3, 2, 1, 1, 2, 3, 1, 5, 5]
def baseStart_6127666 : Nat := 118140960795 + 6127666 * 2 ^ 59
def prefixEnd_6127666 : Nat := 4983230072969 + 3 ^ 40 * 6127666 * 2
def baseEnd_6127666 : Nat := 349604216468169745810487

theorem tailTrace_6127666 : CollatzResearch.WordTrace tailWord_6127666 prefixEnd_6127666 349604216468169745810487 := by
  unfold tailWord_6127666
  simp only [CollatzResearch.WordTrace]
  refine ⟨55873584954630019720008713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148996226545680052586689901 55873584954630019720008713)
  ·
    refine ⟨41905188715972514790006535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55873584954630019720008713 41905188715972514790006535)
    ·
      refine ⟨62857783073958772185009803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41905188715972514790006535 62857783073958772185009803)
      ·
        refine ⟨94286674610938158277514705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62857783073958772185009803 94286674610938158277514705)
        ·
          refine ⟨70715005958203618708136029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94286674610938158277514705 70715005958203618708136029)
          ·
            refine ⟨26518127234326357015551011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70715005958203618708136029 26518127234326357015551011)
            ·
              refine ⟨39777190851489535523326517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26518127234326357015551011 39777190851489535523326517)
              ·
                refine ⟨3729111642327143955311861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39777190851489535523326517 3729111642327143955311861)
                ·
                  refine ⟨349604216468169745810487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3729111642327143955311861 349604216468169745810487)
                  ·
                    rfl

theorem cell23_6127666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_6127666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127666 prefixEnd_6127666 := by exact prefixLift 6127666
  have htrace : WordTrace (prefixWord ++ tailWord_6127666) baseStart_6127666 baseEnd_6127666 := by
    simpa [prefixWord, tailWord_6127666, baseEnd_6127666] using wordTrace_append hprefix tailTrace_6127666
  have hstable : (prefixWord ++ tailWord_6127666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127666).length < 2 ^ (prefixWord ++ tailWord_6127666).sum := by decide
  have hdescent : baseEnd_6127666 < baseStart_6127666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127679 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 2, 5]
def baseStart_6127679 : Nat := 118140960795 + 6127679 * 2 ^ 59
def prefixEnd_6127679 : Nat := 4983230072969 + 3 ^ 40 * 6127679 * 2
def baseEnd_6127679 : Nat := 1048814874487345387143941

theorem tailTrace_6127679 : CollatzResearch.WordTrace tailWord_6127679 prefixEnd_6127679 1048814874487345387143941 := by
  unfold tailWord_6127679
  simp only [CollatzResearch.WordTrace]
  refine ⟨223494813967472982100258091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148996542644981988066838727 223494813967472982100258091)
  ·
    refine ⟨335242220951209473150387137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223494813967472982100258091 335242220951209473150387137)
    ·
      refine ⟨251431665713407104862790353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335242220951209473150387137 251431665713407104862790353)
      ·
        refine ⟨188573749285055328647092765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251431665713407104862790353 188573749285055328647092765)
        ·
          refine ⟨70715155981895748242659787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188573749285055328647092765 70715155981895748242659787)
          ·
            refine ⟨106072733972843622363989681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70715155981895748242659787 106072733972843622363989681)
            ·
              refine ⟨79554550479632716772992261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106072733972843622363989681 79554550479632716772992261)
              ·
                refine ⟨14916478214931134394936049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79554550479632716772992261 14916478214931134394936049)
                ·
                  refine ⟨11187358661198350796202037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14916478214931134394936049 11187358661198350796202037)
                  ·
                    refine ⟨1048814874487345387143941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11187358661198350796202037 1048814874487345387143941)
                    ·
                      rfl

theorem cell23_6127679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 5].length) (baseStart_6127679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127679 prefixEnd_6127679 := by exact prefixLift 6127679
  have htrace : WordTrace (prefixWord ++ tailWord_6127679) baseStart_6127679 baseEnd_6127679 := by
    simpa [prefixWord, tailWord_6127679, baseEnd_6127679] using wordTrace_append hprefix tailTrace_6127679
  have hstable : (prefixWord ++ tailWord_6127679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127679).length < 2 ^ (prefixWord ++ tailWord_6127679).sum := by decide
  have hdescent : baseEnd_6127679 < baseStart_6127679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127716 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 1, 6, 2]
def baseStart_6127716 : Nat := 118140960795 + 6127716 * 2 ^ 59
def prefixEnd_6127716 : Nat := 4983230072969 + 3 ^ 40 * 6127716 * 2
def baseEnd_6127716 : Nat := 3146463622246252516669153

theorem tailTrace_6127716 : CollatzResearch.WordTrace tailWord_6127716 prefixEnd_6127716 3146463622246252516669153 := by
  unfold tailWord_6127716
  simp only [CollatzResearch.WordTrace]
  refine ⟨111748081734169468709677501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148997442312225958279570001 111748081734169468709677501)
  ·
    refine ⟨41905530650313550766129063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111748081734169468709677501 41905530650313550766129063)
    ·
      refine ⟨62858295975470326149193595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41905530650313550766129063 62858295975470326149193595)
      ·
        refine ⟨94287443963205489223790393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62858295975470326149193595 94287443963205489223790393)
        ·
          refine ⟨70715582972404116917842795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94287443963205489223790393 70715582972404116917842795)
          ·
            refine ⟨106073374458606175376764193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70715582972404116917842795 106073374458606175376764193)
            ·
              refine ⟨79555030843954631532573145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106073374458606175376764193 79555030843954631532573145)
              ·
                refine ⟨59666273132965973649429859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79555030843954631532573145 59666273132965973649429859)
                ·
                  refine ⟨89499409699448960474144789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59666273132965973649429859 89499409699448960474144789)
                  ·
                    refine ⟨4195284829661670022225537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89499409699448960474144789 4195284829661670022225537)
                    ·
                      refine ⟨3146463622246252516669153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4195284829661670022225537 3146463622246252516669153)
                      ·
                        rfl

theorem cell23_6127716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_6127716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127716 prefixEnd_6127716 := by exact prefixLift 6127716
  have htrace : WordTrace (prefixWord ++ tailWord_6127716) baseStart_6127716 baseEnd_6127716 := by
    simpa [prefixWord, tailWord_6127716, baseEnd_6127716] using wordTrace_append hprefix tailTrace_6127716
  have hstable : (prefixWord ++ tailWord_6127716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127716).length < 2 ^ (prefixWord ++ tailWord_6127716).sum := by decide
  have hdescent : baseEnd_6127716 < baseStart_6127716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127770 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3]
def baseStart_6127770 : Nat := 118140960795 + 6127770 * 2 ^ 59
def prefixEnd_6127770 : Nat := 4983230072969 + 3 ^ 40 * 6127770 * 2
def baseEnd_6127770 : Nat := 3146491350201595305393905

theorem tailTrace_6127770 : CollatzResearch.WordTrace tailWord_6127770 prefixEnd_6127770 3146491350201595305393905 := by
  unfold tailWord_6127770
  simp only [CollatzResearch.WordTrace]
  refine ⟨55874533252535826160455191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148998755340095536427880509 55874533252535826160455191)
  ·
    refine ⟨83811799878803739240682787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55874533252535826160455191 83811799878803739240682787)
    ·
      refine ⟨125717699818205608861024181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83811799878803739240682787 125717699818205608861024181)
      ·
        refine ⟨11786034357956775830721017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125717699818205608861024181 11786034357956775830721017)
        ·
          refine ⟨8839525768467581873040763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11786034357956775830721017 8839525768467581873040763)
          ·
            refine ⟨13259288652701372809561145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8839525768467581873040763 13259288652701372809561145)
            ·
              refine ⟨9944466489526029607170859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13259288652701372809561145 9944466489526029607170859)
              ·
                refine ⟨14916699734289044410756289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9944466489526029607170859 14916699734289044410756289)
                ·
                  refine ⟨11187524800716783308067217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14916699734289044410756289 11187524800716783308067217)
                  ·
                    refine ⟨8390643600537587481050413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11187524800716783308067217 8390643600537587481050413)
                    ·
                      refine ⟨3146491350201595305393905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8390643600537587481050413 3146491350201595305393905)
                      ·
                        rfl

theorem cell23_6127770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_6127770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127770 prefixEnd_6127770 := by exact prefixLift 6127770
  have htrace : WordTrace (prefixWord ++ tailWord_6127770) baseStart_6127770 baseEnd_6127770 := by
    simpa [prefixWord, tailWord_6127770, baseEnd_6127770] using wordTrace_append hprefix tailTrace_6127770
  have hstable : (prefixWord ++ tailWord_6127770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127770).length < 2 ^ (prefixWord ++ tailWord_6127770).sum := by decide
  have hdescent : baseEnd_6127770 < baseStart_6127770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127800 : List Nat := [2, 1, 2, 1, 2, 1, 5, 4, 1, 1, 3]
def baseStart_6127800 : Nat := 118140960795 + 6127800 * 2 ^ 59
def prefixEnd_6127800 : Nat := 4983230072969 + 3 ^ 40 * 6127800 * 2
def baseEnd_6127800 : Nat := 3146506754621230188018767

theorem tailTrace_6127800 : CollatzResearch.WordTrace tailWord_6127800 prefixEnd_6127800 3146506754621230188018767 := by
  unfold tailWord_6127800
  simp only [CollatzResearch.WordTrace]
  refine ⟨111749613600017309882706427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148999484800023079843608569 111749613600017309882706427)
  ·
    refine ⟨167624420400025964824059641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111749613600017309882706427 167624420400025964824059641)
    ·
      refine ⟨125718315300019473618044731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167624420400025964824059641 125718315300019473618044731)
      ·
        refine ⟨188577472950029210427067097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125718315300019473618044731 188577472950029210427067097)
        ·
          refine ⟨141433104712521907820300323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188577472950029210427067097 141433104712521907820300323)
          ·
            refine ⟨212149657068782861730450485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141433104712521907820300323 212149657068782861730450485)
            ·
              refine ⟨19889030350198393287229733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 212149657068782861730450485 19889030350198393287229733)
              ·
                refine ⟨3729193190662198741355575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19889030350198393287229733 3729193190662198741355575)
                ·
                  refine ⟨5593789785993298112033363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3729193190662198741355575 5593789785993298112033363)
                  ·
                    refine ⟨8390684678989947168050045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5593789785993298112033363 8390684678989947168050045)
                    ·
                      refine ⟨3146506754621230188018767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8390684678989947168050045 3146506754621230188018767)
                      ·
                        rfl

theorem cell23_6127800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 1, 1, 3].length) (baseStart_6127800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127800 prefixEnd_6127800 := by exact prefixLift 6127800
  have htrace : WordTrace (prefixWord ++ tailWord_6127800) baseStart_6127800 baseEnd_6127800 := by
    simpa [prefixWord, tailWord_6127800, baseEnd_6127800] using wordTrace_append hprefix tailTrace_6127800
  have hstable : (prefixWord ++ tailWord_6127800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127800).length < 2 ^ (prefixWord ++ tailWord_6127800).sum := by decide
  have hdescent : baseEnd_6127800 < baseStart_6127800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127816 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 6, 4]
def baseStart_6127816 : Nat := 118140960795 + 6127816 * 2 ^ 59
def prefixEnd_6127816 : Nat := 4983230072969 + 3 ^ 40 * 6127816 * 2
def baseEnd_6127816 : Nat := 1048838323437234041806231

theorem tailTrace_6127816 : CollatzResearch.WordTrace tailWord_6127816 prefixEnd_6127816 1048838323437234041806231 := by
  unfold tailWord_6127816
  simp only [CollatzResearch.WordTrace]
  refine ⟨111749905383988327248997651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148999873845317769665330201 111749905383988327248997651)
  ·
    refine ⟨167624858075982490873496477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111749905383988327248997651 167624858075982490873496477)
    ·
      refine ⟨62859321778493434077561179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167624858075982490873496477 62859321778493434077561179)
      ·
        refine ⟨94288982667740151116341769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62859321778493434077561179 94288982667740151116341769)
        ·
          refine ⟨70716737000805113337256327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94288982667740151116341769 70716737000805113337256327)
          ·
            refine ⟨106075105501207670005884491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70716737000805113337256327 106075105501207670005884491)
            ·
              refine ⟨159112658251811505008826737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106075105501207670005884491 159112658251811505008826737)
              ·
                refine ⟨119334493688858628756620053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159112658251811505008826737 119334493688858628756620053)
                ·
                  refine ⟨5593804391665248222966565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119334493688858628756620053 5593804391665248222966565)
                  ·
                    refine ⟨1048838323437234041806231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5593804391665248222966565 1048838323437234041806231)
                    ·
                      rfl

theorem cell23_6127816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_6127816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127816 prefixEnd_6127816 := by exact prefixLift 6127816
  have htrace : WordTrace (prefixWord ++ tailWord_6127816) baseStart_6127816 baseEnd_6127816 := by
    simpa [prefixWord, tailWord_6127816, baseEnd_6127816] using wordTrace_append hprefix tailTrace_6127816
  have hstable : (prefixWord ++ tailWord_6127816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127816).length < 2 ^ (prefixWord ++ tailWord_6127816).sum := by decide
  have hdescent : baseEnd_6127816 < baseStart_6127816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127837 : List Nat := [1, 4, 3, 2, 1, 3, 2, 1, 1, 5]
def baseStart_6127837 : Nat := 118140960795 + 6127837 * 2 ^ 59
def prefixEnd_6127837 : Nat := 4983230072969 + 3 ^ 40 * 6127837 * 2
def baseEnd_6127837 : Nat := 1048841917801815514418699

theorem tailTrace_6127837 : CollatzResearch.WordTrace tailWord_6127837 prefixEnd_6127837 1048841917801815514418699 := by
  unfold tailWord_6127837
  simp only [CollatzResearch.WordTrace]
  refine ⟨223500576700900575084509765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149000384467267050056339843 223500576700900575084509765)
  ·
    refine ⟨41906358131418857828345581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223500576700900575084509765 41906358131418857828345581)
    ·
      refine ⟨15714884299282071685629593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41906358131418857828345581 15714884299282071685629593)
      ·
        refine ⟨11786163224461553764222195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15714884299282071685629593 11786163224461553764222195)
        ·
          refine ⟨17679244836692330646333293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11786163224461553764222195 17679244836692330646333293)
          ·
            refine ⟨6629716813759623992374985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17679244836692330646333293 6629716813759623992374985)
            ·
              refine ⟨4972287610319717994281239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6629716813759623992374985 4972287610319717994281239)
              ·
                refine ⟨7458431415479576991421859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4972287610319717994281239 7458431415479576991421859)
                ·
                  refine ⟨11187647123219365487132789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7458431415479576991421859 11187647123219365487132789)
                  ·
                    refine ⟨1048841917801815514418699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11187647123219365487132789 1048841917801815514418699)
                    ·
                      rfl

theorem cell23_6127837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_6127837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127837 prefixEnd_6127837 := by exact prefixLift 6127837
  have htrace : WordTrace (prefixWord ++ tailWord_6127837) baseStart_6127837 baseEnd_6127837 := by
    simpa [prefixWord, tailWord_6127837, baseEnd_6127837] using wordTrace_append hprefix tailTrace_6127837
  have hstable : (prefixWord ++ tailWord_6127837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127837).length < 2 ^ (prefixWord ++ tailWord_6127837).sum := by decide
  have hdescent : baseEnd_6127837 < baseStart_6127837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127856 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 3]
def baseStart_6127856 : Nat := 118140960795 + 6127856 * 2 ^ 59
def prefixEnd_6127856 : Nat := 4983230072969 + 3 ^ 40 * 6127856 * 2
def baseEnd_6127856 : Nat := 3146535509537881968918509

theorem tailTrace_6127856 : CollatzResearch.WordTrace tailWord_6127856 prefixEnd_6127856 3146535509537881968918509 := by
  unfold tailWord_6127856
  simp only [CollatzResearch.WordTrace]
  refine ⟨111750634843915870664725711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149000846458554494219634281 111750634843915870664725711)
  ·
    refine ⟨167625952265873805997088567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111750634843915870664725711 167625952265873805997088567)
    ·
      refine ⟨251438928398810708995632851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167625952265873805997088567 251438928398810708995632851)
      ·
        refine ⟨377158392598216063493449277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251438928398810708995632851 377158392598216063493449277)
        ·
          refine ⟨141434397224331023810043479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 377158392598216063493449277 141434397224331023810043479)
          ·
            refine ⟨212151595836496535715065219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141434397224331023810043479 212151595836496535715065219)
            ·
              refine ⟨318227393754744803572597829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212151595836496535715065219 318227393754744803572597829)
              ·
                refine ⟨59667636329014650669862093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 318227393754744803572597829 59667636329014650669862093)
                ·
                  refine ⟨22375363623380494001198285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59667636329014650669862093 22375363623380494001198285)
                  ·
                    refine ⟨8390761358767685250449357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22375363623380494001198285 8390761358767685250449357)
                    ·
                      refine ⟨3146535509537881968918509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8390761358767685250449357 3146535509537881968918509)
                      ·
                        rfl

theorem cell23_6127856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 3].length) (baseStart_6127856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127856 prefixEnd_6127856 := by exact prefixLift 6127856
  have htrace : WordTrace (prefixWord ++ tailWord_6127856) baseStart_6127856 baseEnd_6127856 := by
    simpa [prefixWord, tailWord_6127856, baseEnd_6127856] using wordTrace_append hprefix tailTrace_6127856
  have hstable : (prefixWord ++ tailWord_6127856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127856).length < 2 ^ (prefixWord ++ tailWord_6127856).sum := by decide
  have hdescent : baseEnd_6127856 < baseStart_6127856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127857 : List Nat := [1, 2, 2, 2, 2, 1, 4, 4, 1, 2, 2]
def baseStart_6127857 : Nat := 118140960795 + 6127857 * 2 ^ 59
def prefixEnd_6127857 : Nat := 4983230072969 + 3 ^ 40 * 6127857 * 2
def baseEnd_6127857 : Nat := 3146536023018536465006005

theorem tailTrace_6127857 : CollatzResearch.WordTrace tailWord_6127857 prefixEnd_6127857 3146536023018536465006005 := by
  unfold tailWord_6127857
  simp only [CollatzResearch.WordTrace]
  refine ⟨223501306160828118500237825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149000870773885412333491883 223501306160828118500237825)
  ·
    refine ⟨167625979620621088875178369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223501306160828118500237825 167625979620621088875178369)
    ·
      refine ⟨125719484715465816656383777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167625979620621088875178369 125719484715465816656383777)
      ·
        refine ⟨94289613536599362492287833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125719484715465816656383777 94289613536599362492287833)
        ·
          refine ⟨70717210152449521869215875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94289613536599362492287833 70717210152449521869215875)
          ·
            refine ⟨106075815228674282803823813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70717210152449521869215875 106075815228674282803823813)
            ·
              refine ⟨19889215355376428025716965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106075815228674282803823813 19889215355376428025716965)
              ·
                refine ⟨3729227879133080254821931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19889215355376428025716965 3729227879133080254821931)
                ·
                  refine ⟨5593841818699620382232897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3729227879133080254821931 5593841818699620382232897)
                  ·
                    refine ⟨4195381364024715286674673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5593841818699620382232897 4195381364024715286674673)
                    ·
                      refine ⟨3146536023018536465006005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4195381364024715286674673 3146536023018536465006005)
                      ·
                        rfl

theorem cell23_6127857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_6127857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127857 prefixEnd_6127857 := by exact prefixLift 6127857
  have htrace : WordTrace (prefixWord ++ tailWord_6127857) baseStart_6127857 baseEnd_6127857 := by
    simpa [prefixWord, tailWord_6127857, baseEnd_6127857] using wordTrace_append hprefix tailTrace_6127857
  have hstable : (prefixWord ++ tailWord_6127857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127857).length < 2 ^ (prefixWord ++ tailWord_6127857).sum := by decide
  have hdescent : baseEnd_6127857 < baseStart_6127857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127886 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_6127886 : Nat := 118140960795 + 6127886 * 2 ^ 59
def prefixEnd_6127886 : Nat := 4983230072969 + 3 ^ 40 * 6127886 * 2
def baseEnd_6127886 : Nat := 3146550913957516851543371

theorem tailTrace_6127886 : CollatzResearch.WordTrace tailWord_6127886 prefixEnd_6127886 3146550913957516851543371 := by
  unfold tailWord_6127886
  simp only [CollatzResearch.WordTrace]
  refine ⟨27937795484715382056630439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149001575918482037635362341 27937795484715382056630439)
  ·
    refine ⟨41906693227073073084945659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27937795484715382056630439 41906693227073073084945659)
    ·
      refine ⟨62860039840609609627418489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41906693227073073084945659 62860039840609609627418489)
      ·
        refine ⟨47145029880457207220563867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62860039840609609627418489 47145029880457207220563867)
        ·
          refine ⟨70717544820685810830845801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47145029880457207220563867 70717544820685810830845801)
          ·
            refine ⟨53038158615514358123134351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70717544820685810830845801 53038158615514358123134351)
            ·
              refine ⟨79557237923271537184701527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53038158615514358123134351 79557237923271537184701527)
              ·
                refine ⟨119335856884907305777052291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79557237923271537184701527 119335856884907305777052291)
                ·
                  refine ⟨179003785327360958665578437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119335856884907305777052291 179003785327360958665578437)
                  ·
                    refine ⟨33563209748880179749795957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 179003785327360958665578437 33563209748880179749795957)
                    ·
                      refine ⟨3146550913957516851543371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33563209748880179749795957 3146550913957516851543371)
                      ·
                        rfl

theorem cell23_6127886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_6127886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127886 prefixEnd_6127886 := by exact prefixLift 6127886
  have htrace : WordTrace (prefixWord ++ tailWord_6127886) baseStart_6127886 baseEnd_6127886 := by
    simpa [prefixWord, tailWord_6127886, baseEnd_6127886] using wordTrace_append hprefix tailTrace_6127886
  have hstable : (prefixWord ++ tailWord_6127886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127886).length < 2 ^ (prefixWord ++ tailWord_6127886).sum := by decide
  have hdescent : baseEnd_6127886 < baseStart_6127886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127924 : List Nat := [2, 5, 1, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_6127924 : Nat := 118140960795 + 6127924 * 2 ^ 59
def prefixEnd_6127924 : Nat := 4983230072969 + 3 ^ 40 * 6127924 * 2
def baseEnd_6127924 : Nat := 3146570426222387702868197

theorem tailTrace_6127924 : CollatzResearch.WordTrace tailWord_6127924 prefixEnd_6127924 3146570426222387702868197 := by
  unfold tailWord_6127924
  simp only [CollatzResearch.WordTrace]
  refine ⟨111751874925792694471463413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149002499901056925961951217 111751874925792694471463413)
  ·
    refine ⟨10476738274293065106699695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111751874925792694471463413 10476738274293065106699695)
    ·
      refine ⟨15715107411439597660049543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10476738274293065106699695 15715107411439597660049543)
      ·
        refine ⟨23572661117159396490074315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15715107411439597660049543 23572661117159396490074315)
        ·
          refine ⟨35358991675739094735111473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23572661117159396490074315 35358991675739094735111473)
          ·
            refine ⟨26519243756804321051333605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35358991675739094735111473 26519243756804321051333605)
            ·
              refine ⟨4972358204400810197125051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26519243756804321051333605 4972358204400810197125051)
              ·
                refine ⟨7458537306601215295687577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4972358204400810197125051 7458537306601215295687577)
                ·
                  refine ⟨5593902979950911471765683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7458537306601215295687577 5593902979950911471765683)
                  ·
                    refine ⟨8390854469926367207648525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5593902979950911471765683 8390854469926367207648525)
                    ·
                      refine ⟨3146570426222387702868197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8390854469926367207648525 3146570426222387702868197)
                      ·
                        rfl

theorem cell23_6127924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_6127924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127924 prefixEnd_6127924 := by exact prefixLift 6127924
  have htrace : WordTrace (prefixWord ++ tailWord_6127924) baseStart_6127924 baseEnd_6127924 := by
    simpa [prefixWord, tailWord_6127924, baseEnd_6127924] using wordTrace_append hprefix tailTrace_6127924
  have hstable : (prefixWord ++ tailWord_6127924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127924).length < 2 ^ (prefixWord ++ tailWord_6127924).sum := by decide
  have hdescent : baseEnd_6127924 < baseStart_6127924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127934 : List Nat := [4, 2, 1, 2, 1, 4, 1, 2, 1, 3, 2]
def baseStart_6127934 : Nat := 118140960795 + 6127934 * 2 ^ 59
def prefixEnd_6127934 : Nat := 4983230072969 + 3 ^ 40 * 6127934 * 2
def baseEnd_6127934 : Nat := 3146575561028932663743151

theorem tailTrace_6127934 : CollatzResearch.WordTrace tailWord_6127934 prefixEnd_6127934 3146575561028932663743151 := by
  unfold tailWord_6127934
  simp only [CollatzResearch.WordTrace]
  refine ⟨27938014322693645081348857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149002743054366107100527237 27938014322693645081348857)
  ·
    refine ⟨20953510742020233811011643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27938014322693645081348857 20953510742020233811011643)
    ·
      refine ⟨31430266113030350716517465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20953510742020233811011643 31430266113030350716517465)
      ·
        refine ⟨23572699584772763037388099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31430266113030350716517465 23572699584772763037388099)
        ·
          refine ⟨35359049377159144556082149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23572699584772763037388099 35359049377159144556082149)
          ·
            refine ⟨6629821758217339604265403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35359049377159144556082149 6629821758217339604265403)
            ·
              refine ⟨9944732637326009406398105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6629821758217339604265403 9944732637326009406398105)
              ·
                refine ⟨7458549477994507054798579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9944732637326009406398105 7458549477994507054798579)
                ·
                  refine ⟨11187824216991760582197869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7458549477994507054798579 11187824216991760582197869)
                  ·
                    refine ⟨4195434081371910218324201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11187824216991760582197869 4195434081371910218324201)
                    ·
                      refine ⟨3146575561028932663743151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4195434081371910218324201 3146575561028932663743151)
                      ·
                        rfl

theorem cell23_6127934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_6127934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127934 prefixEnd_6127934 := by exact prefixLift 6127934
  have htrace : WordTrace (prefixWord ++ tailWord_6127934) baseStart_6127934 baseEnd_6127934 := by
    simpa [prefixWord, tailWord_6127934, baseEnd_6127934] using wordTrace_append hprefix tailTrace_6127934
  have hstable : (prefixWord ++ tailWord_6127934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127934).length < 2 ^ (prefixWord ++ tailWord_6127934).sum := by decide
  have hdescent : baseEnd_6127934 < baseStart_6127934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127980 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 3]
def baseStart_6127980 : Nat := 118140960795 + 6127980 * 2 ^ 59
def prefixEnd_6127980 : Nat := 4983230072969 + 3 ^ 40 * 6127980 * 2
def baseEnd_6127980 : Nat := 3146599181139039483767939

theorem tailTrace_6127980 : CollatzResearch.WordTrace tailWord_6127980 prefixEnd_6127980 3146599181139039483767939 := by
  unfold tailWord_6127980
  simp only [CollatzResearch.WordTrace]
  refine ⟨111752896169691255253482697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149003861559588340337976929 111752896169691255253482697)
  ·
    refine ⟨83814672127268441440112023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111752896169691255253482697 83814672127268441440112023)
    ·
      refine ⟨125722008190902662160168035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83814672127268441440112023 125722008190902662160168035)
      ·
        refine ⟨188583012286353993240252053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125722008190902662160168035 188583012286353993240252053)
        ·
          refine ⟨8839828700922843433136815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 188583012286353993240252053 8839828700922843433136815)
          ·
            refine ⟨13259743051384265149705223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8839828700922843433136815 13259743051384265149705223)
            ·
              refine ⟨19889614577076397724557835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13259743051384265149705223 19889614577076397724557835)
              ·
                refine ⟨29834421865614596586836753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19889614577076397724557835 29834421865614596586836753)
                ·
                  refine ⟨22375816399210947440127565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29834421865614596586836753 22375816399210947440127565)
                  ·
                    refine ⟨8390931149704105290047837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22375816399210947440127565 8390931149704105290047837)
                    ·
                      refine ⟨3146599181139039483767939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8390931149704105290047837 3146599181139039483767939)
                      ·
                        rfl

theorem cell23_6127980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_6127980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127980 prefixEnd_6127980 := by exact prefixLift 6127980
  have htrace : WordTrace (prefixWord ++ tailWord_6127980) baseStart_6127980 baseEnd_6127980 := by
    simpa [prefixWord, tailWord_6127980, baseEnd_6127980] using wordTrace_append hprefix tailTrace_6127980
  have hstable : (prefixWord ++ tailWord_6127980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127980).length < 2 ^ (prefixWord ++ tailWord_6127980).sum := by decide
  have hdescent : baseEnd_6127980 < baseStart_6127980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127996 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 1, 10]
def baseStart_6127996 : Nat := 118140960795 + 6127996 * 2 ^ 59
def prefixEnd_6127996 : Nat := 4983230072969 + 3 ^ 40 * 6127996 * 2
def baseEnd_6127996 : Nat := 1048869132276503807055955

theorem tailTrace_6127996 : CollatzResearch.WordTrace tailWord_6127996 prefixEnd_6127996 1048869132276503807055955 := by
  unfold tailWord_6127996
  simp only [CollatzResearch.WordTrace]
  refine ⟨111753187953662272619773921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149004250604883030159698561 111753187953662272619773921)
  ·
    refine ⟨83814890965246704464830441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111753187953662272619773921 83814890965246704464830441)
    ·
      refine ⟨62861168223935028348622831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83814890965246704464830441 62861168223935028348622831)
      ·
        refine ⟨94291752335902542522934247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62861168223935028348622831 94291752335902542522934247)
        ·
          refine ⟨141437628503853813784401371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94291752335902542522934247 141437628503853813784401371)
          ·
            refine ⟨212156442755780720676602057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141437628503853813784401371 212156442755780720676602057)
            ·
              refine ⟨159117332066835540507451543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212156442755780720676602057 159117332066835540507451543)
              ·
                refine ⟨238675998100253310761177315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159117332066835540507451543 238675998100253310761177315)
                ·
                  refine ⟨358013997150379966141765973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238675998100253310761177315 358013997150379966141765973)
                  ·
                    refine ⟨1048869132276503807055955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 358013997150379966141765973 1048869132276503807055955)
                    ·
                      rfl

theorem cell23_6127996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_6127996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127996 prefixEnd_6127996 := by exact prefixLift 6127996
  have htrace : WordTrace (prefixWord ++ tailWord_6127996) baseStart_6127996 baseEnd_6127996 := by
    simpa [prefixWord, tailWord_6127996, baseEnd_6127996] using wordTrace_append hprefix tailTrace_6127996
  have hstable : (prefixWord ++ tailWord_6127996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127996).length < 2 ^ (prefixWord ++ tailWord_6127996).sum := by decide
  have hdescent : baseEnd_6127996 < baseStart_6127996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128127 : List Nat := [1, 1, 2, 2, 1, 2, 7, 1, 1, 1, 4]
def baseStart_6128127 : Nat := 118140960795 + 6128127 * 2 ^ 59
def prefixEnd_6128127 : Nat := 4983230072969 + 3 ^ 40 * 6128127 * 2
def baseEnd_6128127 : Nat := 3146674662795250408629763

theorem tailTrace_6128127 : CollatzResearch.WordTrace tailWord_6128127 prefixEnd_6128127 3146674662795250408629763 := by
  unfold tailWord_6128127
  simp only [CollatzResearch.WordTrace]
  refine ⟨223511153869849954612566635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149007435913233303075044423 223511153869849954612566635)
  ·
    refine ⟨335266730804774931918849953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223511153869849954612566635 335266730804774931918849953)
    ·
      refine ⟨251450048103581198939137465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335266730804774931918849953 251450048103581198939137465)
      ·
        refine ⟨188587536077685899204353099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251450048103581198939137465 188587536077685899204353099)
        ·
          refine ⟨282881304116528848806529649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188587536077685899204353099 282881304116528848806529649)
          ·
            refine ⟨212160978087396636604897237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282881304116528848806529649 212160978087396636604897237)
            ·
              refine ⟨4972522923923358670427279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 212160978087396636604897237 4972522923923358670427279)
              ·
                refine ⟨7458784385885038005640919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4972522923923358670427279 7458784385885038005640919)
                ·
                  refine ⟨11188176578827557008461379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7458784385885038005640919 11188176578827557008461379)
                  ·
                    refine ⟨16782264868241335512692069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11188176578827557008461379 16782264868241335512692069)
                    ·
                      refine ⟨3146674662795250408629763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16782264868241335512692069 3146674662795250408629763)
                      ·
                        rfl

theorem cell23_6128127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 1, 1, 4].length) (baseStart_6128127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128127 prefixEnd_6128127 := by exact prefixLift 6128127
  have htrace : WordTrace (prefixWord ++ tailWord_6128127) baseStart_6128127 baseEnd_6128127 := by
    simpa [prefixWord, tailWord_6128127, baseEnd_6128127] using wordTrace_append hprefix tailTrace_6128127
  have hstable : (prefixWord ++ tailWord_6128127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128127).length < 2 ^ (prefixWord ++ tailWord_6128127).sum := by decide
  have hdescent : baseEnd_6128127 < baseStart_6128127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128157 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_6128157 : Nat := 118140960795 + 6128157 * 2 ^ 59
def prefixEnd_6128157 : Nat := 4983230072969 + 3 ^ 40 * 6128157 * 2
def baseEnd_6128157 : Nat := 3146690067214885291254625

theorem tailTrace_6128157 : CollatzResearch.WordTrace tailWord_6128157 prefixEnd_6128157 3146690067214885291254625 := by
  unfold tailWord_6128157
  simp only [CollatzResearch.WordTrace]
  refine ⟨223512248059741269736158725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149008165373160846490772483 223512248059741269736158725)
  ·
    refine ⟨41908546511201488075529761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223512248059741269736158725 41908546511201488075529761)
    ·
      refine ⟨31431409883401116056647321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41908546511201488075529761 31431409883401116056647321)
      ·
        refine ⟨23573557412550837042485491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31431409883401116056647321 23573557412550837042485491)
        ·
          refine ⟨35360336118826255563728237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23573557412550837042485491 35360336118826255563728237)
          ·
            refine ⟨13260126044559845836398089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35360336118826255563728237 13260126044559845836398089)
            ·
              refine ⟨9945094533419884377298567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13260126044559845836398089 9945094533419884377298567)
              ·
                refine ⟨14917641800129826565947851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9945094533419884377298567 14917641800129826565947851)
                ·
                  refine ⟨22376462700194739848921777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14917641800129826565947851 22376462700194739848921777)
                  ·
                    refine ⟨16782347025146054886691333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22376462700194739848921777 16782347025146054886691333)
                    ·
                      refine ⟨3146690067214885291254625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16782347025146054886691333 3146690067214885291254625)
                      ·
                        rfl

theorem cell23_6128157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_6128157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128157 prefixEnd_6128157 := by exact prefixLift 6128157
  have htrace : WordTrace (prefixWord ++ tailWord_6128157) baseStart_6128157 baseEnd_6128157 := by
    simpa [prefixWord, tailWord_6128157, baseEnd_6128157] using wordTrace_append hprefix tailTrace_6128157
  have hstable : (prefixWord ++ tailWord_6128157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128157).length < 2 ^ (prefixWord ++ tailWord_6128157).sum := by decide
  have hdescent : baseEnd_6128157 < baseStart_6128157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128210 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 2, 6]
def baseStart_6128210 : Nat := 118140960795 + 6128210 * 2 ^ 59
def prefixEnd_6128210 : Nat := 4983230072969 + 3 ^ 40 * 6128210 * 2
def baseEnd_6128210 : Nat := 1048905760563191194630627

theorem tailTrace_6128210 : CollatzResearch.WordTrace tailWord_6128210 prefixEnd_6128210 1048905760563191194630627 := by
  unfold tailWord_6128210
  simp only [CollatzResearch.WordTrace]
  refine ⟨55878545282137314946959521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149009454085699506525225389 55878545282137314946959521)
  ·
    refine ⟨41908908961602986210219641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55878545282137314946959521 41908908961602986210219641)
    ·
      refine ⟨31431681721202239657664731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41908908961602986210219641 31431681721202239657664731)
      ·
        refine ⟨47147522581803359486497097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31431681721202239657664731 47147522581803359486497097)
        ·
          refine ⟨35360641936352519614872823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47147522581803359486497097 35360641936352519614872823)
          ·
            refine ⟨53040962904528779422309235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35360641936352519614872823 53040962904528779422309235)
            ·
              refine ⟨79561444356793169133463853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53040962904528779422309235 79561444356793169133463853)
              ·
                refine ⟨29835541633797438425048945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79561444356793169133463853 29835541633797438425048945)
                ·
                  refine ⟨22376656225348078818786709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29835541633797438425048945 22376656225348078818786709)
                  ·
                    refine ⟨1048905760563191194630627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22376656225348078818786709 1048905760563191194630627)
                    ·
                      rfl

theorem cell23_6128210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_6128210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128210 prefixEnd_6128210 := by exact prefixLift 6128210
  have htrace : WordTrace (prefixWord ++ tailWord_6128210) baseStart_6128210 baseEnd_6128210 := by
    simpa [prefixWord, tailWord_6128210, baseEnd_6128210] using wordTrace_append hprefix tailTrace_6128210
  have hstable : (prefixWord ++ tailWord_6128210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128210).length < 2 ^ (prefixWord ++ tailWord_6128210).sum := by decide
  have hdescent : baseEnd_6128210 < baseStart_6128210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128234 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 6, 2, 2]
def baseStart_6128234 : Nat := 118140960795 + 6128234 * 2 ^ 59
def prefixEnd_6128234 : Nat := 4983230072969 + 3 ^ 40 * 6128234 * 2
def baseEnd_6128234 : Nat := 3146729605225281489991771

theorem tailTrace_6128234 : CollatzResearch.WordTrace tailWord_6128234 prefixEnd_6128234 3146729605225281489991771 := by
  unfold tailWord_6128234
  simp only [CollatzResearch.WordTrace]
  refine ⟨55878764120115577971677939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149010037653641541257807837 55878764120115577971677939)
  ·
    refine ⟨83818146180173366957516909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55878764120115577971677939 83818146180173366957516909)
    ·
      refine ⟨31431804817565012609068841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83818146180173366957516909 31431804817565012609068841)
      ·
        refine ⟨23573853613173759456801631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31431804817565012609068841 23573853613173759456801631)
        ·
          refine ⟨35360780419760639185202447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23573853613173759456801631 35360780419760639185202447)
          ·
            refine ⟨53041170629640958777803671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35360780419760639185202447 53041170629640958777803671)
            ·
              refine ⟨79561755944461438166705507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53041170629640958777803671 79561755944461438166705507)
              ·
                refine ⟨119342633916692157250058261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79561755944461438166705507 119342633916692157250058261)
                ·
                  refine ⟨5594185964844944871096481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119342633916692157250058261 5594185964844944871096481)
                  ·
                    refine ⟨4195639473633708653322361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5594185964844944871096481 4195639473633708653322361)
                    ·
                      refine ⟨3146729605225281489991771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4195639473633708653322361 3146729605225281489991771)
                      ·
                        rfl

theorem cell23_6128234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_6128234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128234 prefixEnd_6128234 := by exact prefixLift 6128234
  have htrace : WordTrace (prefixWord ++ tailWord_6128234) baseStart_6128234 baseEnd_6128234 := by
    simpa [prefixWord, tailWord_6128234, baseEnd_6128234] using wordTrace_append hprefix tailTrace_6128234
  have hstable : (prefixWord ++ tailWord_6128234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128234).length < 2 ^ (prefixWord ++ tailWord_6128234).sum := by decide
  have hdescent : baseEnd_6128234 < baseStart_6128234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128237 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_6128237 : Nat := 118140960795 + 6128237 * 2 ^ 59
def prefixEnd_6128237 : Nat := 4983230072969 + 3 ^ 40 * 6128237 * 2
def baseEnd_6128237 : Nat := 3146731145667244978254257

theorem tailTrace_6128237 : CollatzResearch.WordTrace tailWord_6128237 prefixEnd_6128237 3146731145667244978254257 := by
  unfold tailWord_6128237
  simp only [CollatzResearch.WordTrace]
  refine ⟨223515165899451443399070965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149010110599634295599380643 223515165899451443399070965)
  ·
    refine ⟨20954546803073572818662903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223515165899451443399070965 20954546803073572818662903)
    ·
      refine ⟨31431820204610359227994355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20954546803073572818662903 31431820204610359227994355)
      ·
        refine ⟨47147730306915538841991533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31431820204610359227994355 47147730306915538841991533)
        ·
          refine ⟨17680398865093327065746825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47147730306915538841991533 17680398865093327065746825)
          ·
            refine ⟨13260299148819995299310119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17680398865093327065746825 13260299148819995299310119)
            ·
              refine ⟨19890448723229992948965179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13260299148819995299310119 19890448723229992948965179)
              ·
                refine ⟨29835673084844989423447769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19890448723229992948965179 29835673084844989423447769)
                ·
                  refine ⟨22376754813633742067585827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29835673084844989423447769 22376754813633742067585827)
                  ·
                    refine ⟨33565132220450613101378741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22376754813633742067585827 33565132220450613101378741)
                    ·
                      refine ⟨3146731145667244978254257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33565132220450613101378741 3146731145667244978254257)
                      ·
                        rfl

theorem cell23_6128237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_6128237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128237 prefixEnd_6128237 := by exact prefixLift 6128237
  have htrace : WordTrace (prefixWord ++ tailWord_6128237) baseStart_6128237 baseEnd_6128237 := by
    simpa [prefixWord, tailWord_6128237, baseEnd_6128237] using wordTrace_append hprefix tailTrace_6128237
  have hstable : (prefixWord ++ tailWord_6128237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128237).length < 2 ^ (prefixWord ++ tailWord_6128237).sum := by decide
  have hdescent : baseEnd_6128237 < baseStart_6128237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128280 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 1, 1, 7]
def baseStart_6128280 : Nat := 118140960795 + 6128280 * 2 ^ 59
def prefixEnd_6128280 : Nat := 4983230072969 + 3 ^ 40 * 6128280 * 2
def baseEnd_6128280 : Nat := 3146753225335388310016559

theorem tailTrace_6128280 : CollatzResearch.WordTrace tailWord_6128280 prefixEnd_6128280 3146753225335388310016559 := by
  unfold tailWord_6128280
  simp only [CollatzResearch.WordTrace]
  refine ⟨111758367119147830871443147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149011156158863774495257529 111758367119147830871443147)
  ·
    refine ⟨167637550678721746307164721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111758367119147830871443147 167637550678721746307164721)
    ·
      refine ⟨125728163009041309730373541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167637550678721746307164721 125728163009041309730373541)
      ·
        refine ⟨23574030564195245574445039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125728163009041309730373541 23574030564195245574445039)
        ·
          refine ⟨35361045846292868361667559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23574030564195245574445039 35361045846292868361667559)
          ·
            refine ⟨53041568769439302542501339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35361045846292868361667559 53041568769439302542501339)
            ·
              refine ⟨79562353154158953813752009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53041568769439302542501339 79562353154158953813752009)
              ·
                refine ⟨59671764865619215360314007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79562353154158953813752009 59671764865619215360314007)
                ·
                  refine ⟨89507647298428823040471011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59671764865619215360314007 89507647298428823040471011)
                  ·
                    refine ⟨134261470947643234560706517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89507647298428823040471011 134261470947643234560706517)
                    ·
                      refine ⟨3146753225335388310016559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134261470947643234560706517 3146753225335388310016559)
                      ·
                        rfl

theorem cell23_6128280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_6128280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128280 prefixEnd_6128280 := by exact prefixLift 6128280
  have htrace : WordTrace (prefixWord ++ tailWord_6128280) baseStart_6128280 baseEnd_6128280 := by
    simpa [prefixWord, tailWord_6128280, baseEnd_6128280] using wordTrace_append hprefix tailTrace_6128280
  have hstable : (prefixWord ++ tailWord_6128280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128280).length < 2 ^ (prefixWord ++ tailWord_6128280).sum := by decide
  have hdescent : baseEnd_6128280 < baseStart_6128280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128307 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 4]
def baseStart_6128307 : Nat := 118140960795 + 6128307 * 2 ^ 59
def prefixEnd_6128307 : Nat := 4983230072969 + 3 ^ 40 * 6128307 * 2
def baseEnd_6128307 : Nat := 3146767089313059704378935

theorem tailTrace_6128307 : CollatzResearch.WordTrace tailWord_6128307 prefixEnd_6128307 3146767089313059704378935 := by
  unfold tailWord_6128307
  simp only [CollatzResearch.WordTrace]
  refine ⟨223517719009197845354119175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149011812672798563569412783 223517719009197845354119175)
  ·
    refine ⟨335276578513796768031178763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223517719009197845354119175 335276578513796768031178763)
    ·
      refine ⟨502914867770695152046768145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335276578513796768031178763 502914867770695152046768145)
      ·
        refine ⟨377186150828021364035076109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502914867770695152046768145 377186150828021364035076109)
        ·
          refine ⟨141444806560508011513153541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 377186150828021364035076109 141444806560508011513153541)
          ·
            refine ⟨26520901230095252158716289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141444806560508011513153541 26520901230095252158716289)
            ·
              refine ⟨19890675922571439119037217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26520901230095252158716289 19890675922571439119037217)
              ·
                refine ⟨14918006941928579339277913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19890675922571439119037217 14918006941928579339277913)
                ·
                  refine ⟨11188505206446434504458435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14918006941928579339277913 11188505206446434504458435)
                  ·
                    refine ⟨16782757809669651756687653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11188505206446434504458435 16782757809669651756687653)
                    ·
                      refine ⟨3146767089313059704378935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16782757809669651756687653 3146767089313059704378935)
                      ·
                        rfl

theorem cell23_6128307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 4].length) (baseStart_6128307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128307 prefixEnd_6128307 := by exact prefixLift 6128307
  have htrace : WordTrace (prefixWord ++ tailWord_6128307) baseStart_6128307 baseEnd_6128307 := by
    simpa [prefixWord, tailWord_6128307, baseEnd_6128307] using wordTrace_append hprefix tailTrace_6128307
  have hstable : (prefixWord ++ tailWord_6128307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128307).length < 2 ^ (prefixWord ++ tailWord_6128307).sum := by decide
  have hdescent : baseEnd_6128307 < baseStart_6128307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128324 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_6128324 : Nat := 118140960795 + 6128324 * 2 ^ 59
def prefixEnd_6128324 : Nat := 4983230072969 + 3 ^ 40 * 6128324 * 2
def baseEnd_6128324 : Nat := 3146775818484186137866357

theorem tailTrace_6128324 : CollatzResearch.WordTrace tailWord_6128324 prefixEnd_6128324 3146775818484186137866357 := by
  unfold tailWord_6128324
  simp only [CollatzResearch.WordTrace]
  refine ⟨111759169525068128628744013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149012226033424171504992017 111759169525068128628744013)
  ·
    refine ⟨41909688571900548235779005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111759169525068128628744013 41909688571900548235779005)
    ·
      refine ⟨15716133214462705588417127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41909688571900548235779005 15716133214462705588417127)
      ·
        refine ⟨23574199821694058382625691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15716133214462705588417127 23574199821694058382625691)
        ·
          refine ⟨35361299732541087573938537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23574199821694058382625691 35361299732541087573938537)
          ·
            refine ⟨26520974799405815680453903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35361299732541087573938537 26520974799405815680453903)
            ·
              refine ⟨39781462199108723520680855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26520974799405815680453903 39781462199108723520680855)
              ·
                refine ⟨59672193298663085281021283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39781462199108723520680855 59672193298663085281021283)
                ·
                  refine ⟨89508289947994627921531925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59672193298663085281021283 89508289947994627921531925)
                  ·
                    refine ⟨4195701091312248183821809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89508289947994627921531925 4195701091312248183821809)
                    ·
                      refine ⟨3146775818484186137866357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4195701091312248183821809 3146775818484186137866357)
                      ·
                        rfl

theorem cell23_6128324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_6128324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128324 prefixEnd_6128324 := by exact prefixLift 6128324
  have htrace : WordTrace (prefixWord ++ tailWord_6128324) baseStart_6128324 baseEnd_6128324 := by
    simpa [prefixWord, tailWord_6128324, baseEnd_6128324] using wordTrace_append hprefix tailTrace_6128324
  have hstable : (prefixWord ++ tailWord_6128324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128324).length < 2 ^ (prefixWord ++ tailWord_6128324).sum := by decide
  have hdescent : baseEnd_6128324 < baseStart_6128324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128334 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 3, 4]
def baseStart_6128334 : Nat := 118140960795 + 6128334 * 2 ^ 59
def prefixEnd_6128334 : Nat := 4983230072969 + 3 ^ 40 * 6128334 * 2
def baseEnd_6128334 : Nat := 1048926984430243699580437

theorem tailTrace_6128334 : CollatzResearch.WordTrace tailWord_6128334 prefixEnd_6128334 1048926984430243699580437 := by
  unfold tailWord_6128334
  simp only [CollatzResearch.WordTrace]
  refine ⟨27939837972512503620669007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149012469186733352643568037 27939837972512503620669007)
  ·
    refine ⟨41909756958768755431003511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27939837972512503620669007 41909756958768755431003511)
    ·
      refine ⟨62864635438153133146505267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41909756958768755431003511 62864635438153133146505267)
      ·
        refine ⟨94296953157229699719757901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62864635438153133146505267 94296953157229699719757901)
        ·
          refine ⟨35361357433961137394909213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94296953157229699719757901 35361357433961137394909213)
          ·
            refine ⟨13260509037735426523090955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35361357433961137394909213 13260509037735426523090955)
            ·
              refine ⟨19890763556603139784636433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13260509037735426523090955 19890763556603139784636433)
              ·
                refine ⟨14918072667452354838477325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19890763556603139784636433 14918072667452354838477325)
                ·
                  refine ⟨5594277250294633064428997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14918072667452354838477325 5594277250294633064428997)
                  ·
                    refine ⟨1048926984430243699580437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5594277250294633064428997 1048926984430243699580437)
                    ·
                      rfl

theorem cell23_6128334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_6128334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128334 prefixEnd_6128334 := by exact prefixLift 6128334
  have htrace : WordTrace (prefixWord ++ tailWord_6128334) baseStart_6128334 baseEnd_6128334 := by
    simpa [prefixWord, tailWord_6128334, baseEnd_6128334] using wordTrace_append hprefix tailTrace_6128334
  have hstable : (prefixWord ++ tailWord_6128334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128334).length < 2 ^ (prefixWord ++ tailWord_6128334).sum := by decide
  have hdescent : baseEnd_6128334 < baseStart_6128334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128344 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 2, 2, 3]
def baseStart_6128344 : Nat := 118140960795 + 6128344 * 2 ^ 59
def prefixEnd_6128344 : Nat := 4983230072969 + 3 ^ 40 * 6128344 * 2
def baseEnd_6128344 : Nat := 3146786088097276059616265

theorem tailTrace_6128344 : CollatzResearch.WordTrace tailWord_6128344 prefixEnd_6128344 3146786088097276059616265 := by
  unfold tailWord_6128344
  simp only [CollatzResearch.WordTrace]
  refine ⟨111759534255031900336608043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149012712340042533782144057 111759534255031900336608043)
  ·
    refine ⟨167639301382547850504912065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111759534255031900336608043 167639301382547850504912065)
    ·
      refine ⟨125729476036910887878684049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167639301382547850504912065 125729476036910887878684049)
      ·
        refine ⟨94297107027683165909013037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125729476036910887878684049 94297107027683165909013037)
        ·
          refine ⟨35361415135381187215879889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94297107027683165909013037 35361415135381187215879889)
          ·
            refine ⟨26521061351535890411909917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35361415135381187215879889 26521061351535890411909917)
            ·
              refine ⟨9945398006825958904466219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26521061351535890411909917 9945398006825958904466219)
              ·
                refine ⟨14918097010238938356699329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9945398006825958904466219 14918097010238938356699329)
                ·
                  refine ⟨11188572757679203767524497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14918097010238938356699329 11188572757679203767524497)
                  ·
                    refine ⟨8391429568259402825643373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11188572757679203767524497 8391429568259402825643373)
                    ·
                      refine ⟨3146786088097276059616265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8391429568259402825643373 3146786088097276059616265)
                      ·
                        rfl

theorem cell23_6128344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_6128344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128344 prefixEnd_6128344 := by exact prefixLift 6128344
  have htrace : WordTrace (prefixWord ++ tailWord_6128344) baseStart_6128344 baseEnd_6128344 := by
    simpa [prefixWord, tailWord_6128344, baseEnd_6128344] using wordTrace_append hprefix tailTrace_6128344
  have hstable : (prefixWord ++ tailWord_6128344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128344).length < 2 ^ (prefixWord ++ tailWord_6128344).sum := by decide
  have hdescent : baseEnd_6128344 < baseStart_6128344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128351 : List Nat := [1, 1, 2, 3, 2, 4, 2, 3, 1, 4]
def baseStart_6128351 : Nat := 118140960795 + 6128351 * 2 ^ 59
def prefixEnd_6128351 : Nat := 4983230072969 + 3 ^ 40 * 6128351 * 2
def baseEnd_6128351 : Nat := 1048929894153952510742911

theorem tailTrace_6128351 : CollatzResearch.WordTrace tailWord_6128351 prefixEnd_6128351 1048929894153952510742911 := by
  unfold tailWord_6128351
  simp only [CollatzResearch.WordTrace]
  refine ⟨223519323821038440868720907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149012882547358960579147271 223519323821038440868720907)
  ·
    refine ⟨335278985731557661303081361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223519323821038440868720907 335278985731557661303081361)
    ·
      refine ⟨251459239298668245977311021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335278985731557661303081361 251459239298668245977311021)
      ·
        refine ⟨94297214737000592241491633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251459239298668245977311021 94297214737000592241491633)
        ·
          refine ⟨70722911052750444181118725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94297214737000592241491633 70722911052750444181118725)
          ·
            refine ⟨13260545822390708283959761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70722911052750444181118725 13260545822390708283959761)
            ·
              refine ⟨9945409366793031212969821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13260545822390708283959761 9945409366793031212969821)
              ·
                refine ⟨3729528512547386704863683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9945409366793031212969821 3729528512547386704863683)
                ·
                  refine ⟨5594292768821080057295525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3729528512547386704863683 5594292768821080057295525)
                  ·
                    refine ⟨1048929894153952510742911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5594292768821080057295525 1048929894153952510742911)
                    ·
                      rfl

theorem cell23_6128351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 1, 4].length) (baseStart_6128351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128351 prefixEnd_6128351 := by exact prefixLift 6128351
  have htrace : WordTrace (prefixWord ++ tailWord_6128351) baseStart_6128351 baseEnd_6128351 := by
    simpa [prefixWord, tailWord_6128351, baseEnd_6128351] using wordTrace_append hprefix tailTrace_6128351
  have hstable : (prefixWord ++ tailWord_6128351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128351).length < 2 ^ (prefixWord ++ tailWord_6128351).sum := by decide
  have hdescent : baseEnd_6128351 < baseStart_6128351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128391 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 3, 1, 3]
def baseStart_6128391 : Nat := 118140960795 + 6128391 * 2 ^ 59
def prefixEnd_6128391 : Nat := 4983230072969 + 3 ^ 40 * 6128391 * 2
def baseEnd_6128391 : Nat := 3146810221688037375728549

theorem tailTrace_6128391 : CollatzResearch.WordTrace tailWord_6128391 prefixEnd_6128391 3146810221688037375728549 := by
  unfold tailWord_6128391
  simp only [CollatzResearch.WordTrace]
  refine ⟨223520782740893527700177027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149013855160595685133451351 223520782740893527700177027)
  ·
    refine ⟨335281174111340291550265541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223520782740893527700177027 335281174111340291550265541)
    ·
      refine ⟨62865220145876304665674789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335281174111340291550265541 62865220145876304665674789)
      ·
        refine ⟨11787228777351807124814023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62865220145876304665674789 11787228777351807124814023)
        ·
          refine ⟨17680843166027710687221035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11787228777351807124814023 17680843166027710687221035)
          ·
            refine ⟨26521264749041566030831553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17680843166027710687221035 26521264749041566030831553)
            ·
              refine ⟨19890948561781174523123665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26521264749041566030831553 19890948561781174523123665)
              ·
                refine ⟨14918211421335880892342749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19890948561781174523123665 14918211421335880892342749)
                ·
                  refine ⟨5594329283000955334628531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14918211421335880892342749 5594329283000955334628531)
                  ·
                    refine ⟨8391493924501433001942797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5594329283000955334628531 8391493924501433001942797)
                    ·
                      refine ⟨3146810221688037375728549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8391493924501433001942797 3146810221688037375728549)
                      ·
                        rfl

theorem cell23_6128391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_6128391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128391 prefixEnd_6128391 := by exact prefixLift 6128391
  have htrace : WordTrace (prefixWord ++ tailWord_6128391) baseStart_6128391 baseEnd_6128391 := by
    simpa [prefixWord, tailWord_6128391, baseEnd_6128391] using wordTrace_append hprefix tailTrace_6128391
  have hstable : (prefixWord ++ tailWord_6128391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128391).length < 2 ^ (prefixWord ++ tailWord_6128391).sum := by decide
  have hdescent : baseEnd_6128391 < baseStart_6128391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128394 : List Nat := [3, 1, 2, 2, 1, 2, 4, 2, 1, 5]
def baseStart_6128394 : Nat := 118140960795 + 6128394 * 2 ^ 59
def prefixEnd_6128394 : Nat := 4983230072969 + 3 ^ 40 * 6128394 * 2
def baseEnd_6128394 : Nat := 1048937254043333621330345

theorem tailTrace_6128394 : CollatzResearch.WordTrace tailWord_6128394 prefixEnd_6128394 1048937254043333621330345 := by
  unfold tailWord_6128394
  simp only [CollatzResearch.WordTrace]
  refine ⟨55880223039970664803134059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149013928106588439475024157 55880223039970664803134059)
  ·
    refine ⟨83820334559955997204701089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55880223039970664803134059 83820334559955997204701089)
    ·
      refine ⟨62865250919966997903525817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83820334559955997204701089 62865250919966997903525817)
      ·
        refine ⟨47148938189975248427644363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62865250919966997903525817 47148938189975248427644363)
        ·
          refine ⟨70723407284962872641466545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47148938189975248427644363 70723407284962872641466545)
          ·
            refine ⟨53042555463722154481099909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70723407284962872641466545 53042555463722154481099909)
            ·
              refine ⟨9945479149447903965206233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53042555463722154481099909 9945479149447903965206233)
              ·
                refine ⟨7459109362085927973904675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9945479149447903965206233 7459109362085927973904675)
                ·
                  refine ⟨11188664043128891960857013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7459109362085927973904675 11188664043128891960857013)
                  ·
                    refine ⟨1048937254043333621330345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11188664043128891960857013 1048937254043333621330345)
                    ·
                      rfl

theorem cell23_6128394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_6128394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128394 prefixEnd_6128394 := by exact prefixLift 6128394
  have htrace : WordTrace (prefixWord ++ tailWord_6128394) baseStart_6128394 baseEnd_6128394 := by
    simpa [prefixWord, tailWord_6128394, baseEnd_6128394] using wordTrace_append hprefix tailTrace_6128394
  have hstable : (prefixWord ++ tailWord_6128394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128394).length < 2 ^ (prefixWord ++ tailWord_6128394).sum := by decide
  have hdescent : baseEnd_6128394 < baseStart_6128394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128402 : List Nat := [3, 2, 4, 1, 3, 1, 1, 3, 1, 4]
def baseStart_6128402 : Nat := 118140960795 + 6128402 * 2 ^ 59
def prefixEnd_6128402 : Nat := 4983230072969 + 3 ^ 40 * 6128402 * 2
def baseEnd_6128402 : Nat := 1048938623325078944230333

theorem tailTrace_6128402 : CollatzResearch.WordTrace tailWord_6128402 prefixEnd_6128402 1048938623325078944230333 := by
  unfold tailWord_6128402
  simp only [CollatzResearch.WordTrace]
  refine ⟨55880295985963419144706865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149014122629235784385884973 55880295985963419144706865)
  ·
    refine ⟨41910221989472564358530149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55880295985963419144706865 41910221989472564358530149)
    ·
      refine ⟨7858166623026105817224403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41910221989472564358530149 7858166623026105817224403)
      ·
        refine ⟨11787249934539158725836605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7858166623026105817224403 11787249934539158725836605)
        ·
          refine ⟨4420218725452184522188727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11787249934539158725836605 4420218725452184522188727)
          ·
            refine ⟨6630328088178276783283091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4420218725452184522188727 6630328088178276783283091)
            ·
              refine ⟨9945492132267415174924637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6630328088178276783283091 9945492132267415174924637)
              ·
                refine ⟨3729559549600280690596739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9945492132267415174924637 3729559549600280690596739)
                ·
                  refine ⟨5594339324400421035895109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3729559549600280690596739 5594339324400421035895109)
                  ·
                    refine ⟨1048938623325078944230333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5594339324400421035895109 1048938623325078944230333)
                    ·
                      rfl

theorem cell23_6128402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_6128402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128402 prefixEnd_6128402 := by exact prefixLift 6128402
  have htrace : WordTrace (prefixWord ++ tailWord_6128402) baseStart_6128402 baseEnd_6128402 := by
    simpa [prefixWord, tailWord_6128402, baseEnd_6128402] using wordTrace_append hprefix tailTrace_6128402
  have hstable : (prefixWord ++ tailWord_6128402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128402).length < 2 ^ (prefixWord ++ tailWord_6128402).sum := by decide
  have hdescent : baseEnd_6128402 < baseStart_6128402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128424 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 4, 4]
def baseStart_6128424 : Nat := 118140960795 + 6128424 * 2 ^ 59
def prefixEnd_6128424 : Nat := 4983230072969 + 3 ^ 40 * 6128424 * 2
def baseEnd_6128424 : Nat := 1048942388849878582205299

theorem tailTrace_6128424 : CollatzResearch.WordTrace tailWord_6128424 prefixEnd_6128424 1048942388849878582205299 := by
  unfold tailWord_6128424
  simp only [CollatzResearch.WordTrace]
  refine ⟨111760993174886987168064163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149014657566515982890752217 111760993174886987168064163)
  ·
    refine ⟨167641489762330480752096245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111760993174886987168064163 167641489762330480752096245)
    ·
      refine ⟨15716389665218482570509023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167641489762330480752096245 15716389665218482570509023)
      ·
        refine ⟨23574584497827723855763535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15716389665218482570509023 23574584497827723855763535)
        ·
          refine ⟨35361876746741585783645303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23574584497827723855763535 35361876746741585783645303)
          ·
            refine ⟨53042815120112378675467955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35361876746741585783645303 53042815120112378675467955)
            ·
              refine ⟨79564222680168568013201933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53042815120112378675467955 79564222680168568013201933)
              ·
                refine ⟨29836583505063213004950725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79564222680168568013201933 29836583505063213004950725)
                ·
                  refine ⟨5594359407199352438428261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29836583505063213004950725 5594359407199352438428261)
                  ·
                    refine ⟨1048942388849878582205299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5594359407199352438428261 1048942388849878582205299)
                    ·
                      rfl

theorem cell23_6128424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_6128424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128424 prefixEnd_6128424 := by exact prefixLift 6128424
  have htrace : WordTrace (prefixWord ++ tailWord_6128424) baseStart_6128424 baseEnd_6128424 := by
    simpa [prefixWord, tailWord_6128424, baseEnd_6128424] using wordTrace_append hprefix tailTrace_6128424
  have hstable : (prefixWord ++ tailWord_6128424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128424).length < 2 ^ (prefixWord ++ tailWord_6128424).sum := by decide
  have hdescent : baseEnd_6128424 < baseStart_6128424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128434 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3]
def baseStart_6128434 : Nat := 118140960795 + 6128434 * 2 ^ 59
def prefixEnd_6128434 : Nat := 4983230072969 + 3 ^ 40 * 6128434 * 2
def baseEnd_6128434 : Nat := 3146832301356180707490851

theorem tailTrace_6128434 : CollatzResearch.WordTrace tailWord_6128434 prefixEnd_6128434 3146832301356180707490851 := by
  unfold tailWord_6128434
  simp only [CollatzResearch.WordTrace]
  refine ⟨55880587769934436510998089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149014900719825164029328237 55880587769934436510998089)
  ·
    refine ⟨41910440827450827383248567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55880587769934436510998089 41910440827450827383248567)
    ·
      refine ⟨62865661241176241074872851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41910440827450827383248567 62865661241176241074872851)
      ·
        refine ⟨94298491861764361612309277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62865661241176241074872851 94298491861764361612309277)
        ·
          refine ⟨35361934448161635604615979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94298491861764361612309277 35361934448161635604615979)
          ·
            refine ⟨53042901672242453406923969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35361934448161635604615979 53042901672242453406923969)
            ·
              refine ⟨39782176254181840055192977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53042901672242453406923969 39782176254181840055192977)
              ·
                refine ⟨29836632190636380041394733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39782176254181840055192977 29836632190636380041394733)
                ·
                  refine ⟨11188737071488642515523025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29836632190636380041394733 11188737071488642515523025)
                  ·
                    refine ⟨8391552803616481886642269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11188737071488642515523025 8391552803616481886642269)
                    ·
                      refine ⟨3146832301356180707490851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8391552803616481886642269 3146832301356180707490851)
                      ·
                        rfl

theorem cell23_6128434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_6128434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128434 prefixEnd_6128434 := by exact prefixLift 6128434
  have htrace : WordTrace (prefixWord ++ tailWord_6128434) baseStart_6128434 baseEnd_6128434 := by
    simpa [prefixWord, tailWord_6128434, baseEnd_6128434] using wordTrace_append hprefix tailTrace_6128434
  have hstable : (prefixWord ++ tailWord_6128434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128434).length < 2 ^ (prefixWord ++ tailWord_6128434).sum := by decide
  have hdescent : baseEnd_6128434 < baseStart_6128434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128437 : List Nat := [1, 3, 3, 1, 3, 1, 1, 10]
def baseStart_6128437 : Nat := 118140960795 + 6128437 * 2 ^ 59
def prefixEnd_6128437 : Nat := 4983230072969 + 3 ^ 40 * 6128437 * 2
def baseEnd_6128437 : Nat := 116549401548079414657531

theorem tailTrace_6128437 : CollatzResearch.WordTrace tailWord_6128437 prefixEnd_6128437 116549401548079414657531 := by
  unfold tailWord_6128437
  simp only [CollatzResearch.WordTrace]
  refine ⟨223522460498726877556351565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149014973665817918370901043 223522460498726877556351565)
  ·
    refine ⟨83820922687022579083631837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223522460498726877556351565 83820922687022579083631837)
    ·
      refine ⟨31432846007633467156361939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83820922687022579083631837 31432846007633467156361939)
      ·
        refine ⟨47149269011450200734542909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31432846007633467156361939 47149269011450200734542909)
        ·
          refine ⟨17680975879293825275453591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47149269011450200734542909 17680975879293825275453591)
          ·
            refine ⟨26521463818940737913180387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17680975879293825275453591 26521463818940737913180387)
            ·
              refine ⟨39782195728411106869770581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26521463818940737913180387 39782195728411106869770581)
              ·
                refine ⟨116549401548079414657531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39782195728411106869770581 116549401548079414657531)
                ·
                  rfl

theorem cell23_6128437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 10].length) (baseStart_6128437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128437 prefixEnd_6128437 := by exact prefixLift 6128437
  have htrace : WordTrace (prefixWord ++ tailWord_6128437) baseStart_6128437 baseEnd_6128437 := by
    simpa [prefixWord, tailWord_6128437, baseEnd_6128437] using wordTrace_append hprefix tailTrace_6128437
  have hstable : (prefixWord ++ tailWord_6128437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128437).length < 2 ^ (prefixWord ++ tailWord_6128437).sum := by decide
  have hdescent : baseEnd_6128437 < baseStart_6128437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128464 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 6, 1, 3]
def baseStart_6128464 : Nat := 118140960795 + 6128464 * 2 ^ 59
def prefixEnd_6128464 : Nat := 4983230072969 + 3 ^ 40 * 6128464 * 2
def baseEnd_6128464 : Nat := 3146847705775815590115713

theorem tailTrace_6128464 : CollatzResearch.WordTrace tailWord_6128464 prefixEnd_6128464 3146847705775815590115713 := by
  unfold tailWord_6128464
  simp only [CollatzResearch.WordTrace]
  refine ⟨111761722634814530583792223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149015630179752707445056297 111761722634814530583792223)
  ·
    refine ⟨167642583952221795875688335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111761722634814530583792223 167642583952221795875688335)
    ·
      refine ⟨251463875928332693813532503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167642583952221795875688335 251463875928332693813532503)
      ·
        refine ⟨377195813892499040720298755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251463875928332693813532503 377195813892499040720298755)
        ·
          refine ⟨565793720838748561080448133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377195813892499040720298755 565793720838748561080448133)
          ·
            refine ⟨106086322657265355202584025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 565793720838748561080448133 106086322657265355202584025)
            ·
              refine ⟨79564741992949016401938019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106086322657265355202584025 79564741992949016401938019)
              ·
                refine ⟨119347112989423524602907029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79564741992949016401938019 119347112989423524602907029)
                ·
                  refine ⟨5594395921379227715761267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119347112989423524602907029 5594395921379227715761267)
                  ·
                    refine ⟨8391593882068841573641901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5594395921379227715761267 8391593882068841573641901)
                    ·
                      refine ⟨3146847705775815590115713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8391593882068841573641901 3146847705775815590115713)
                      ·
                        rfl

theorem cell23_6128464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 6, 1, 3].length) (baseStart_6128464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128464 prefixEnd_6128464 := by exact prefixLift 6128464
  have htrace : WordTrace (prefixWord ++ tailWord_6128464) baseStart_6128464 baseEnd_6128464 := by
    simpa [prefixWord, tailWord_6128464, baseEnd_6128464] using wordTrace_append hprefix tailTrace_6128464
  have hstable : (prefixWord ++ tailWord_6128464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128464).length < 2 ^ (prefixWord ++ tailWord_6128464).sum := by decide
  have hdescent : baseEnd_6128464 < baseStart_6128464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128468 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 1, 1, 5]
def baseStart_6128468 : Nat := 118140960795 + 6128468 * 2 ^ 59
def prefixEnd_6128468 : Nat := 4983230072969 + 3 ^ 40 * 6128468 * 2
def baseEnd_6128468 : Nat := 3146849759698433574465695

theorem tailTrace_6128468 : CollatzResearch.WordTrace tailWord_6128468 prefixEnd_6128468 3146849759698433574465695 := by
  unfold tailWord_6128468
  simp only [CollatzResearch.WordTrace]
  refine ⟨111761795580807284925365029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149015727441076379900486705 111761795580807284925365029)
  ·
    refine ⟨20955336671401365923505943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111761795580807284925365029 20955336671401365923505943)
    ·
      refine ⟨31433005007102048885258915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20955336671401365923505943 31433005007102048885258915)
      ·
        refine ⟨47149507510653073327888373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31433005007102048885258915 47149507510653073327888373)
        ·
          refine ⟨4420266329123725624489535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47149507510653073327888373 4420266329123725624489535)
          ·
            refine ⟨6630399493685588436734303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4420266329123725624489535 6630399493685588436734303)
            ·
              refine ⟨9945599240528382655101455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6630399493685588436734303 9945599240528382655101455)
              ·
                refine ⟨14918398860792573982652183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9945599240528382655101455 14918398860792573982652183)
                ·
                  refine ⟨22377598291188860973978275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14918398860792573982652183 22377598291188860973978275)
                  ·
                    refine ⟨33566397436783291460967413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22377598291188860973978275 33566397436783291460967413)
                    ·
                      refine ⟨3146849759698433574465695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33566397436783291460967413 3146849759698433574465695)
                      ·
                        rfl

theorem cell23_6128468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_6128468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128468 prefixEnd_6128468 := by exact prefixLift 6128468
  have htrace : WordTrace (prefixWord ++ tailWord_6128468) baseStart_6128468 baseEnd_6128468 := by
    simpa [prefixWord, tailWord_6128468, baseEnd_6128468] using wordTrace_append hprefix tailTrace_6128468
  have hstable : (prefixWord ++ tailWord_6128468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128468).length < 2 ^ (prefixWord ++ tailWord_6128468).sum := by decide
  have hdescent : baseEnd_6128468 < baseStart_6128468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128482 : List Nat := [3, 3, 2, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_6128482 : Nat := 118140960795 + 6128482 * 2 ^ 59
def prefixEnd_6128482 : Nat := 4983230072969 + 3 ^ 40 * 6128482 * 2
def baseEnd_6128482 : Nat := 3146856948427596519690631

theorem tailTrace_6128482 : CollatzResearch.WordTrace tailWord_6128482 prefixEnd_6128482 3146856948427596519690631 := by
  unfold tailWord_6128482
  simp only [CollatzResearch.WordTrace]
  refine ⟨55881025445890962560434925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149016067855709233494493133 55881025445890962560434925)
  ·
    refine ⟨20955384542209110960163097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55881025445890962560434925 20955384542209110960163097)
    ·
      refine ⟨15716538406656833220122323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20955384542209110960163097 15716538406656833220122323)
      ·
        refine ⟨23574807609985249830183485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15716538406656833220122323 23574807609985249830183485)
        ·
          refine ⟨8840552853744468686318807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23574807609985249830183485 8840552853744468686318807)
          ·
            refine ⟨13260829280616703029478211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8840552853744468686318807 13260829280616703029478211)
            ·
              refine ⟨19891243920925054544217317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13260829280616703029478211 19891243920925054544217317)
              ·
                refine ⟨3729608235173447727040747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19891243920925054544217317 3729608235173447727040747)
                ·
                  refine ⟨5594412352760171590561121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3729608235173447727040747 5594412352760171590561121)
                  ·
                    refine ⟨4195809264570128692920841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5594412352760171590561121 4195809264570128692920841)
                    ·
                      refine ⟨3146856948427596519690631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4195809264570128692920841 3146856948427596519690631)
                      ·
                        rfl

theorem cell23_6128482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_6128482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128482 prefixEnd_6128482 := by exact prefixLift 6128482
  have htrace : WordTrace (prefixWord ++ tailWord_6128482) baseStart_6128482 baseEnd_6128482 := by
    simpa [prefixWord, tailWord_6128482, baseEnd_6128482] using wordTrace_append hprefix tailTrace_6128482
  have hstable : (prefixWord ++ tailWord_6128482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128482).length < 2 ^ (prefixWord ++ tailWord_6128482).sum := by decide
  have hdescent : baseEnd_6128482 < baseStart_6128482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128497 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 1, 8]
def baseStart_6128497 : Nat := 118140960795 + 6128497 * 2 ^ 59
def prefixEnd_6128497 : Nat := 4983230072969 + 3 ^ 40 * 6128497 * 2
def baseEnd_6128497 : Nat := 1048954883545804653667687

theorem tailTrace_6128497 : CollatzResearch.WordTrace tailWord_6128497 prefixEnd_6128497 1048954883545804653667687 := by
  unfold tailWord_6128497
  simp only [CollatzResearch.WordTrace]
  refine ⟨223524648878509507803535745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149016432585673005202357163 223524648878509507803535745)
  ·
    refine ⟨167643486658882130852651809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223524648878509507803535745 167643486658882130852651809)
    ·
      refine ⟨125732614994161598139488857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167643486658882130852651809 125732614994161598139488857)
      ·
        refine ⟨94299461245621198604616643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125732614994161598139488857 94299461245621198604616643)
        ·
          refine ⟨141449191868431797906924965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94299461245621198604616643 141449191868431797906924965)
          ·
            refine ⟨26521723475330962107548431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141449191868431797906924965 26521723475330962107548431)
            ·
              refine ⟨39782585212996443161322647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26521723475330962107548431 39782585212996443161322647)
              ·
                refine ⟨59673877819494664741983971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39782585212996443161322647 59673877819494664741983971)
                ·
                  refine ⟨89510816729241997112975957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59673877819494664741983971 89510816729241997112975957)
                  ·
                    refine ⟨1048954883545804653667687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89510816729241997112975957 1048954883545804653667687)
                    ·
                      rfl

theorem cell23_6128497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_6128497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128497 prefixEnd_6128497 := by exact prefixLift 6128497
  have htrace : WordTrace (prefixWord ++ tailWord_6128497) baseStart_6128497 baseEnd_6128497 := by
    simpa [prefixWord, tailWord_6128497, baseEnd_6128497] using wordTrace_append hprefix tailTrace_6128497
  have hstable : (prefixWord ++ tailWord_6128497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128497).length < 2 ^ (prefixWord ++ tailWord_6128497).sum := by decide
  have hdescent : baseEnd_6128497 < baseStart_6128497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128507 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 5]
def baseStart_6128507 : Nat := 118140960795 + 6128507 * 2 ^ 59
def prefixEnd_6128507 : Nat := 4983230072969 + 3 ^ 40 * 6128507 * 2
def baseEnd_6128507 : Nat := 3146869785443958921878015

theorem tailTrace_6128507 : CollatzResearch.WordTrace tailWord_6128507 prefixEnd_6128507 3146869785443958921878015 := by
  unfold tailWord_6128507
  simp only [CollatzResearch.WordTrace]
  refine ⟨223525013608473279511399775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149016675738982186340933183 223525013608473279511399775)
  ·
    refine ⟨335287520412709919267099663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223525013608473279511399775 335287520412709919267099663)
    ·
      refine ⟨502931280619064878900649495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335287520412709919267099663 502931280619064878900649495)
      ·
        refine ⟨754396920928597318350974243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502931280619064878900649495 754396920928597318350974243)
        ·
          refine ⟨1131595381392895977526461365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754396920928597318350974243 1131595381392895977526461365)
          ·
            refine ⟨106087067005583997893105753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1131595381392895977526461365 106087067005583997893105753)
            ·
              refine ⟨79565300254187998419829315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106087067005583997893105753 79565300254187998419829315)
              ·
                refine ⟨119347950381281997629743973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79565300254187998419829315 119347950381281997629743973)
                ·
                  refine ⟨22377740696490374555576995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119347950381281997629743973 22377740696490374555576995)
                  ·
                    refine ⟨33566611044735561833365493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22377740696490374555576995 33566611044735561833365493)
                    ·
                      refine ⟨3146869785443958921878015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33566611044735561833365493 3146869785443958921878015)
                      ·
                        rfl

theorem cell23_6128507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 5].length) (baseStart_6128507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128507 prefixEnd_6128507 := by exact prefixLift 6128507
  have htrace : WordTrace (prefixWord ++ tailWord_6128507) baseStart_6128507 baseEnd_6128507 := by
    simpa [prefixWord, tailWord_6128507, baseEnd_6128507] using wordTrace_append hprefix tailTrace_6128507
  have hstable : (prefixWord ++ tailWord_6128507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128507).length < 2 ^ (prefixWord ++ tailWord_6128507).sum := by decide
  have hdescent : baseEnd_6128507 < baseStart_6128507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128521 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 1, 4, 2]
def baseStart_6128521 : Nat := 118140960795 + 6128521 * 2 ^ 59
def prefixEnd_6128521 : Nat := 4983230072969 + 3 ^ 40 * 6128521 * 2
def baseEnd_6128521 : Nat := 3146876974173121867102951

theorem tailTrace_6128521 : CollatzResearch.WordTrace tailWord_6128521 prefixEnd_6128521 3146876974173121867102951 := by
  unfold tailWord_6128521
  simp only [CollatzResearch.WordTrace]
  refine ⟨223525524230422559902409417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149017016153615039934939611 223525524230422559902409417)
  ·
    refine ⟨167644143172816919926807063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223525524230422559902409417 167644143172816919926807063)
    ·
      refine ⟨251466214759225379890210595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167644143172816919926807063 251466214759225379890210595)
      ·
        refine ⟨377199322138838069835315893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251466214759225379890210595 377199322138838069835315893)
        ·
          refine ⟨35362436450516069047060865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 377199322138838069835315893 35362436450516069047060865)
          ·
            refine ⟨26521827337887051785295649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35362436450516069047060865 26521827337887051785295649)
            ·
              refine ⟨19891370503415288838971737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26521827337887051785295649 19891370503415288838971737)
              ·
                refine ⟨14918527877561466629228803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19891370503415288838971737 14918527877561466629228803)
                ·
                  refine ⟨22377791816342199943843205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14918527877561466629228803 22377791816342199943843205)
                  ·
                    refine ⟨4195835965564162489470601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22377791816342199943843205 4195835965564162489470601)
                    ·
                      refine ⟨3146876974173121867102951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4195835965564162489470601 3146876974173121867102951)
                      ·
                        rfl

theorem cell23_6128521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 4, 2].length) (baseStart_6128521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128521 prefixEnd_6128521 := by exact prefixLift 6128521
  have htrace : WordTrace (prefixWord ++ tailWord_6128521) baseStart_6128521 baseEnd_6128521 := by
    simpa [prefixWord, tailWord_6128521, baseEnd_6128521] using wordTrace_append hprefix tailTrace_6128521
  have hstable : (prefixWord ++ tailWord_6128521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128521).length < 2 ^ (prefixWord ++ tailWord_6128521).sum := by decide
  have hdescent : baseEnd_6128521 < baseStart_6128521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128574 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_6128574 : Nat := 118140960795 + 6128574 * 2 ^ 59
def prefixEnd_6128574 : Nat := 4983230072969 + 3 ^ 40 * 6128574 * 2
def baseEnd_6128574 : Nat := 1048968062882603386580069

theorem tailTrace_6128574 : CollatzResearch.WordTrace tailWord_6128574 prefixEnd_6128574 1048968062882603386580069 := by
  unfold tailWord_6128574
  simp only [CollatzResearch.WordTrace]
  refine ⟨27940932162403818744261097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149018304866153699969392517 27940932162403818744261097)
  ·
    refine ⟨20955699121802864058195823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27940932162403818744261097 20955699121802864058195823)
    ·
      refine ⟨31433548682704296087293735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20955699121802864058195823 31433548682704296087293735)
      ·
        refine ⟨47150323024056444130940603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31433548682704296087293735 47150323024056444130940603)
        ·
          refine ⟨70725484536084666196410905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47150323024056444130940603 70725484536084666196410905)
          ·
            refine ⟨53044113402063499647308179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70725484536084666196410905 53044113402063499647308179)
            ·
              refine ⟨79566170103095249470962269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53044113402063499647308179 79566170103095249470962269)
              ·
                refine ⟨29837313788660718551610851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79566170103095249470962269 29837313788660718551610851)
                ·
                  refine ⟨44755970682991077827416277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29837313788660718551610851 44755970682991077827416277)
                  ·
                    refine ⟨1048968062882603386580069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44755970682991077827416277 1048968062882603386580069)
                    ·
                      rfl

theorem cell23_6128574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_6128574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128574 prefixEnd_6128574 := by exact prefixLift 6128574
  have htrace : WordTrace (prefixWord ++ tailWord_6128574) baseStart_6128574 baseEnd_6128574 := by
    simpa [prefixWord, tailWord_6128574, baseEnd_6128574] using wordTrace_append hprefix tailTrace_6128574
  have hstable : (prefixWord ++ tailWord_6128574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128574).length < 2 ^ (prefixWord ++ tailWord_6128574).sum := by decide
  have hdescent : baseEnd_6128574 < baseStart_6128574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128611 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 1, 6, 2]
def baseStart_6128611 : Nat := 118140960795 + 6128611 * 2 ^ 59
def prefixEnd_6128611 : Nat := 4983230072969 + 3 ^ 40 * 6128611 * 2
def baseEnd_6128611 : Nat := 3146923187432026514977537

theorem tailTrace_6128611 : CollatzResearch.WordTrace tailWord_6128611 prefixEnd_6128611 3146923187432026514977537 := by
  unfold tailWord_6128611
  simp only [CollatzResearch.WordTrace]
  refine ⟨223528806800096505273185687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149019204533397670182123791 223528806800096505273185687)
  ·
    refine ⟨335293210200144757909778531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223528806800096505273185687 335293210200144757909778531)
    ·
      refine ⟨502939815300217136864667797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335293210200144757909778531 502939815300217136864667797)
      ·
        refine ⟨23575303842197678290531303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 502939815300217136864667797 23575303842197678290531303)
        ·
          refine ⟨35362955763296517435796955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23575303842197678290531303 35362955763296517435796955)
          ·
            refine ⟨53044433644944776153695433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35362955763296517435796955 53044433644944776153695433)
            ·
              refine ⟨39783325233708582115271575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53044433644944776153695433 39783325233708582115271575)
              ·
                refine ⟨59674987850562873172907363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39783325233708582115271575 59674987850562873172907363)
                ·
                  refine ⟨89512481775844309759361045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59674987850562873172907363 89512481775844309759361045)
                  ·
                    refine ⟨4195897583242702019970049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89512481775844309759361045 4195897583242702019970049)
                    ·
                      refine ⟨3146923187432026514977537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4195897583242702019970049 3146923187432026514977537)
                      ·
                        rfl

theorem cell23_6128611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_6128611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128611 prefixEnd_6128611 := by exact prefixLift 6128611
  have htrace : WordTrace (prefixWord ++ tailWord_6128611) baseStart_6128611 baseEnd_6128611 := by
    simpa [prefixWord, tailWord_6128611, baseEnd_6128611] using wordTrace_append hprefix tailTrace_6128611
  have hstable : (prefixWord ++ tailWord_6128611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128611).length < 2 ^ (prefixWord ++ tailWord_6128611).sum := by decide
  have hdescent : baseEnd_6128611 < baseStart_6128611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128651 : List Nat := [1, 1, 1, 1, 6, 3, 2, 2, 6]
def baseStart_6128651 : Nat := 118140960795 + 6128651 * 2 ^ 59
def prefixEnd_6128651 : Nat := 4983230072969 + 3 ^ 40 * 6128651 * 2
def baseEnd_6128651 : Nat := 349660414073134039830817

theorem tailTrace_6128651 : CollatzResearch.WordTrace tailWord_6128651 prefixEnd_6128651 349660414073134039830817 := by
  unfold tailWord_6128651
  simp only [CollatzResearch.WordTrace]
  refine ⟨223530265719951592104641807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149020177146634394736427871 223530265719951592104641807)
  ·
    refine ⟨335295398579927388156962711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223530265719951592104641807 335295398579927388156962711)
    ·
      refine ⟨502943097869891082235444067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335295398579927388156962711 502943097869891082235444067)
      ·
        refine ⟨754414646804836623353166101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502943097869891082235444067 754414646804836623353166101)
        ·
          refine ⟨35363186568976716719679661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 754414646804836623353166101 35363186568976716719679661)
          ·
            refine ⟨13261194963366268769879873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35363186568976716719679661 13261194963366268769879873)
            ·
              refine ⟨9945896222524701577409905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13261194963366268769879873 9945896222524701577409905)
              ·
                refine ⟨7459422166893526183057429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9945896222524701577409905 7459422166893526183057429)
                ·
                  refine ⟨349660414073134039830817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7459422166893526183057429 349660414073134039830817)
                  ·
                    rfl

theorem cell23_6128651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 6].length) (baseStart_6128651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128651 prefixEnd_6128651 := by exact prefixLift 6128651
  have htrace : WordTrace (prefixWord ++ tailWord_6128651) baseStart_6128651 baseEnd_6128651 := by
    simpa [prefixWord, tailWord_6128651, baseEnd_6128651] using wordTrace_append hprefix tailTrace_6128651
  have hstable : (prefixWord ++ tailWord_6128651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128651).length < 2 ^ (prefixWord ++ tailWord_6128651).sum := by decide
  have hdescent : baseEnd_6128651 < baseStart_6128651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128682 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_6128682 : Nat := 118140960795 + 6128682 * 2 ^ 59
def prefixEnd_6128682 : Nat := 4983230072969 + 3 ^ 40 * 6128682 * 2
def baseEnd_6128682 : Nat := 3146959644558495737189711

theorem tailTrace_6128682 : CollatzResearch.WordTrace tailWord_6128682 prefixEnd_6128682 3146959644558495737189711 := by
  unfold tailWord_6128682
  simp only [CollatzResearch.WordTrace]
  refine ⟨55882849095709821099755075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149020930921892856266013533 55882849095709821099755075)
  ·
    refine ⟨83824273643564731649632613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55882849095709821099755075 83824273643564731649632613)
    ·
      refine ⟨15717051308168387184306115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83824273643564731649632613 15717051308168387184306115)
      ·
        refine ⟨23575576962252580776459173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15717051308168387184306115 23575576962252580776459173)
        ·
          refine ⟨4420420680422358895586095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23575576962252580776459173 4420420680422358895586095)
          ·
            refine ⟨6630631020633538343379143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4420420680422358895586095 6630631020633538343379143)
            ·
              refine ⟨9945946530950307515068715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6630631020633538343379143 9945946530950307515068715)
              ·
                refine ⟨14918919796425461272603073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9945946530950307515068715 14918919796425461272603073)
                ·
                  refine ⟨11189189847319095954452305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14918919796425461272603073 11189189847319095954452305)
                  ·
                    refine ⟨8391892385489321965839229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11189189847319095954452305 8391892385489321965839229)
                    ·
                      refine ⟨3146959644558495737189711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8391892385489321965839229 3146959644558495737189711)
                      ·
                        rfl

theorem cell23_6128682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_6128682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128682 prefixEnd_6128682 := by exact prefixLift 6128682
  have htrace : WordTrace (prefixWord ++ tailWord_6128682) baseStart_6128682 baseEnd_6128682 := by
    simpa [prefixWord, tailWord_6128682, baseEnd_6128682] using wordTrace_append hprefix tailTrace_6128682
  have hstable : (prefixWord ++ tailWord_6128682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128682).length < 2 ^ (prefixWord ++ tailWord_6128682).sum := by decide
  have hdescent : baseEnd_6128682 < baseStart_6128682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128698 : List Nat := [3, 1, 1, 1, 3, 1, 6, 1, 1, 5]
def baseStart_6128698 : Nat := 118140960795 + 6128698 * 2 ^ 59
def prefixEnd_6128698 : Nat := 4983230072969 + 3 ^ 40 * 6128698 * 2
def baseEnd_6128698 : Nat := 1048989286749655891529879

theorem tailTrace_6128698 : CollatzResearch.WordTrace tailWord_6128698 prefixEnd_6128698 1048989286749655891529879 := by
  unfold tailWord_6128698
  simp only [CollatzResearch.WordTrace]
  refine ⟨55882994987695329782900687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149021319967187546087735165 55882994987695329782900687)
  ·
    refine ⟨83824492481542994674351031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55882994987695329782900687 83824492481542994674351031)
    ·
      refine ⟨125736738722314492011526547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83824492481542994674351031 125736738722314492011526547)
      ·
        refine ⟨188605108083471738017289821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125736738722314492011526547 188605108083471738017289821)
        ·
          refine ⟨70726915531301901756483683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188605108083471738017289821 70726915531301901756483683)
          ·
            refine ⟨106090373296952852634725525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70726915531301901756483683 106090373296952852634725525)
            ·
              refine ⟨4972986248294664967252759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106090373296952852634725525 4972986248294664967252759)
              ·
                refine ⟨7459479372441997450879139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4972986248294664967252759 7459479372441997450879139)
                ·
                  refine ⟨11189219058662996176318709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7459479372441997450879139 11189219058662996176318709)
                  ·
                    refine ⟨1048989286749655891529879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11189219058662996176318709 1048989286749655891529879)
                    ·
                      rfl

theorem cell23_6128698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_6128698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128698 prefixEnd_6128698 := by exact prefixLift 6128698
  have htrace : WordTrace (prefixWord ++ tailWord_6128698) baseStart_6128698 baseEnd_6128698 := by
    simpa [prefixWord, tailWord_6128698, baseEnd_6128698] using wordTrace_append hprefix tailTrace_6128698
  have hstable : (prefixWord ++ tailWord_6128698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128698).length < 2 ^ (prefixWord ++ tailWord_6128698).sum := by decide
  have hdescent : baseEnd_6128698 < baseStart_6128698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128721 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 5, 2, 3]
def baseStart_6128721 : Nat := 118140960795 + 6128721 * 2 ^ 59
def prefixEnd_6128721 : Nat := 4983230072969 + 3 ^ 40 * 6128721 * 2
def baseEnd_6128721 : Nat := 3146979670304021084602031

theorem tailTrace_6128721 : CollatzResearch.WordTrace tailWord_6128721 prefixEnd_6128721 3146979670304021084602031 := by
  unfold tailWord_6128721
  simp only [CollatzResearch.WordTrace]
  refine ⟨223532818829697994059690017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149021879219798662706460011 223532818829697994059690017)
  ·
    refine ⟨167649614122273495544767513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223532818829697994059690017 167649614122273495544767513)
    ·
      refine ⟨125737210591705121658575635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167649614122273495544767513 125737210591705121658575635)
      ·
        refine ⟨188605815887557682487863453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125737210591705121658575635 188605815887557682487863453)
        ·
          refine ⟨70727180957834130932948795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188605815887557682487863453 70727180957834130932948795)
          ·
            refine ⟨106090771436751196399423193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70727180957834130932948795 106090771436751196399423193)
            ·
              refine ⟨79568078577563397299567395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106090771436751196399423193 79568078577563397299567395)
              ·
                refine ⟨119352117866345095949351093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79568078577563397299567395 119352117866345095949351093)
                ·
                  refine ⟨11189261049969852745251665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119352117866345095949351093 11189261049969852745251665)
                  ·
                    refine ⟨8391945787477389558938749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11189261049969852745251665 8391945787477389558938749)
                    ·
                      refine ⟨3146979670304021084602031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8391945787477389558938749 3146979670304021084602031)
                      ·
                        rfl

theorem cell23_6128721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_6128721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128721 prefixEnd_6128721 := by exact prefixLift 6128721
  have htrace : WordTrace (prefixWord ++ tailWord_6128721) baseStart_6128721 baseEnd_6128721 := by
    simpa [prefixWord, tailWord_6128721, baseEnd_6128721] using wordTrace_append hprefix tailTrace_6128721
  have hstable : (prefixWord ++ tailWord_6128721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128721).length < 2 ^ (prefixWord ++ tailWord_6128721).sum := by decide
  have hdescent : baseEnd_6128721 < baseStart_6128721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128751 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 3]
def baseStart_6128751 : Nat := 118140960795 + 6128751 * 2 ^ 59
def prefixEnd_6128751 : Nat := 4983230072969 + 3 ^ 40 * 6128751 * 2
def baseEnd_6128751 : Nat := 3146995074723655967226893

theorem tailTrace_6128751 : CollatzResearch.WordTrace tailWord_6128751 prefixEnd_6128751 3146995074723655967226893 := by
  unfold tailWord_6128751
  simp only [CollatzResearch.WordTrace]
  refine ⟨223533913019589309183282107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149022608679726206122188071 223533913019589309183282107)
  ·
    refine ⟨335300869529383963774923161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223533913019589309183282107 335300869529383963774923161)
    ·
      refine ⟨251475652147037972831192371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335300869529383963774923161 251475652147037972831192371)
      ·
        refine ⟨377213478220556959246788557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251475652147037972831192371 377213478220556959246788557)
        ·
          refine ⟨141455054332708859717545709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 377213478220556959246788557 141455054332708859717545709)
          ·
            refine ⟨53045645374765822394079641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141455054332708859717545709 53045645374765822394079641)
            ·
              refine ⟨39784234031074366795559731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53045645374765822394079641 39784234031074366795559731)
              ·
                refine ⟨59676351046611550193339597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39784234031074366795559731 59676351046611550193339597)
                ·
                  refine ⟨22378631642479331322502349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59676351046611550193339597 22378631642479331322502349)
                  ·
                    refine ⟨8391986865929749245938381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22378631642479331322502349 8391986865929749245938381)
                    ·
                      refine ⟨3146995074723655967226893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8391986865929749245938381 3146995074723655967226893)
                      ·
                        rfl

theorem cell23_6128751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 3].length) (baseStart_6128751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128751 prefixEnd_6128751 := by exact prefixLift 6128751
  have htrace : WordTrace (prefixWord ++ tailWord_6128751) baseStart_6128751 baseEnd_6128751 := by
    simpa [prefixWord, tailWord_6128751, baseEnd_6128751] using wordTrace_append hprefix tailTrace_6128751
  have hstable : (prefixWord ++ tailWord_6128751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128751).length < 2 ^ (prefixWord ++ tailWord_6128751).sum := by decide
  have hdescent : baseEnd_6128751 < baseStart_6128751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128768 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 4, 1, 3]
def baseStart_6128768 : Nat := 118140960795 + 6128768 * 2 ^ 59
def prefixEnd_6128768 : Nat := 4983230072969 + 3 ^ 40 * 6128768 * 2
def baseEnd_6128768 : Nat := 3147003803894782400714315

theorem tailTrace_6128768 : CollatzResearch.WordTrace tailWord_6128768 prefixEnd_6128768 3147003803894782400714315 := by
  unfold tailWord_6128768
  simp only [CollatzResearch.WordTrace]
  refine ⟨111767266530263860543325479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149023022040351814057767305 111767266530263860543325479)
  ·
    refine ⟨167650899795395790814988219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111767266530263860543325479 167650899795395790814988219)
    ·
      refine ⟨251476349693093686222482329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167650899795395790814988219 251476349693093686222482329)
      ·
        refine ⟨188607262269820264666861747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251476349693093686222482329 188607262269820264666861747)
        ·
          refine ⟨282910893404730397000292621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188607262269820264666861747 282910893404730397000292621)
          ·
            refine ⟨106091585026773898875109733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282910893404730397000292621 106091585026773898875109733)
            ·
              refine ⟨19892172192520106039083075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106091585026773898875109733 19892172192520106039083075)
              ·
                refine ⟨29838258288780159058624613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19892172192520106039083075 29838258288780159058624613)
                ·
                  refine ⟨5594673429146279823492115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29838258288780159058624613 5594673429146279823492115)
                  ·
                    refine ⟨8392010143719419735238173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5594673429146279823492115 8392010143719419735238173)
                    ·
                      refine ⟨3147003803894782400714315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8392010143719419735238173 3147003803894782400714315)
                      ·
                        rfl

theorem cell23_6128768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_6128768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128768 prefixEnd_6128768 := by exact prefixLift 6128768
  have htrace : WordTrace (prefixWord ++ tailWord_6128768) baseStart_6128768 baseEnd_6128768 := by
    simpa [prefixWord, tailWord_6128768, baseEnd_6128768] using wordTrace_append hprefix tailTrace_6128768
  have hstable : (prefixWord ++ tailWord_6128768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128768).length < 2 ^ (prefixWord ++ tailWord_6128768).sum := by decide
  have hdescent : baseEnd_6128768 < baseStart_6128768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128828 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 2, 4, 3]
def baseStart_6128828 : Nat := 118140960795 + 6128828 * 2 ^ 59
def prefixEnd_6128828 : Nat := 4983230072969 + 3 ^ 40 * 6128828 * 2
def baseEnd_6128828 : Nat := 3147034612734052165964039

theorem tailTrace_6128828 : CollatzResearch.WordTrace tailWord_6128828 prefixEnd_6128828 3147034612734052165964039 := by
  unfold tailWord_6128828
  simp only [CollatzResearch.WordTrace]
  refine ⟨111768360720155175666917569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149024480960206900889223425 111768360720155175666917569)
  ·
    refine ⟨83826270540116381750188177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111768360720155175666917569 83826270540116381750188177)
    ·
      refine ⟨62869702905087286312641133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83826270540116381750188177 62869702905087286312641133)
      ·
        refine ⟨23576138589407732367240425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62869702905087286312641133 23576138589407732367240425)
        ·
          refine ⟨17682103942055799275430319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23576138589407732367240425 17682103942055799275430319)
          ·
            refine ⟨26523155913083698913145479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17682103942055799275430319 26523155913083698913145479)
            ·
              refine ⟨39784733869625548369718219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26523155913083698913145479 39784733869625548369718219)
              ·
                refine ⟨59677100804438322554577329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39784733869625548369718219 59677100804438322554577329)
                ·
                  refine ⟨44757825603328741915932997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59677100804438322554577329 44757825603328741915932997)
                  ·
                    refine ⟨8392092300624139109237437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44757825603328741915932997 8392092300624139109237437)
                    ·
                      refine ⟨3147034612734052165964039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8392092300624139109237437 3147034612734052165964039)
                      ·
                        rfl

theorem cell23_6128828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_6128828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128828 prefixEnd_6128828 := by exact prefixLift 6128828
  have htrace : WordTrace (prefixWord ++ tailWord_6128828) baseStart_6128828 baseEnd_6128828 := by
    simpa [prefixWord, tailWord_6128828, baseEnd_6128828] using wordTrace_append hprefix tailTrace_6128828
  have hstable : (prefixWord ++ tailWord_6128828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128828).length < 2 ^ (prefixWord ++ tailWord_6128828).sum := by decide
  have hdescent : baseEnd_6128828 < baseStart_6128828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128842 : List Nat := [3, 1, 2, 1, 3, 2, 2, 3, 2, 2, 2]
def baseStart_6128842 : Nat := 118140960795 + 6128842 * 2 ^ 59
def prefixEnd_6128842 : Nat := 4983230072969 + 3 ^ 40 * 6128842 * 2
def baseEnd_6128842 : Nat := 3147041801463215111188975

theorem tailTrace_6128842 : CollatzResearch.WordTrace tailWord_6128842 prefixEnd_6128842 3147041801463215111188975 := by
  unfold tailWord_6128842
  simp only [CollatzResearch.WordTrace]
  refine ⟨55884308015564907931211195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149024821374839754483229853 55884308015564907931211195)
  ·
    refine ⟨83826462023347361896816793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55884308015564907931211195 83826462023347361896816793)
    ·
      refine ⟨62869846517510521422612595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83826462023347361896816793 62869846517510521422612595)
      ·
        refine ⟨94304769776265782133918893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62869846517510521422612595 94304769776265782133918893)
        ·
          refine ⟨35364288666099668300219585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94304769776265782133918893 35364288666099668300219585)
          ·
            refine ⟨26523216499574751225164689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35364288666099668300219585 26523216499574751225164689)
            ·
              refine ⟨19892412374681063418873517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26523216499574751225164689 19892412374681063418873517)
              ·
                refine ⟨7459654640505398782077569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19892412374681063418873517 7459654640505398782077569)
                ·
                  refine ⟨5594740980379049086558177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7459654640505398782077569 5594740980379049086558177)
                  ·
                    refine ⟨4196055735284286814918633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5594740980379049086558177 4196055735284286814918633)
                    ·
                      refine ⟨3147041801463215111188975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4196055735284286814918633 3147041801463215111188975)
                      ·
                        rfl

theorem cell23_6128842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_6128842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128842 prefixEnd_6128842 := by exact prefixLift 6128842
  have htrace : WordTrace (prefixWord ++ tailWord_6128842) baseStart_6128842 baseEnd_6128842 := by
    simpa [prefixWord, tailWord_6128842, baseEnd_6128842] using wordTrace_append hprefix tailTrace_6128842
  have hstable : (prefixWord ++ tailWord_6128842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128842).length < 2 ^ (prefixWord ++ tailWord_6128842).sum := by decide
  have hdescent : baseEnd_6128842 < baseStart_6128842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128865 : List Nat := [1, 2, 3, 1, 3, 3, 2, 3, 5]
def baseStart_6128865 : Nat := 118140960795 + 6128865 * 2 ^ 59
def prefixEnd_6128865 : Nat := 4983230072969 + 3 ^ 40 * 6128865 * 2
def baseEnd_6128865 : Nat := 349672623502029835689041

theorem tailTrace_6128865 : CollatzResearch.WordTrace tailWord_6128865 prefixEnd_6128865 349672623502029835689041 := by
  unfold tailWord_6128865
  simp only [CollatzResearch.WordTrace]
  refine ⟨223538070941176306652932049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149025380627450871101954699 223538070941176306652932049)
  ·
    refine ⟨167653553205882229989699037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223538070941176306652932049 167653553205882229989699037)
    ·
      refine ⟨62870082452205836246137139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167653553205882229989699037 62870082452205836246137139)
      ·
        refine ⟨94305123678308754369205709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62870082452205836246137139 94305123678308754369205709)
        ·
          refine ⟨35364421379365782888452141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94305123678308754369205709 35364421379365782888452141)
          ·
            refine ⟨13261658017262168583169553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35364421379365782888452141 13261658017262168583169553)
            ·
              refine ⟨9946243512946626437377165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13261658017262168583169553 9946243512946626437377165)
              ·
                refine ⟨3729841317354984914016437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9946243512946626437377165 3729841317354984914016437)
                ·
                  refine ⟨349672623502029835689041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3729841317354984914016437 349672623502029835689041)
                  ·
                    rfl

theorem cell23_6128865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 5].length) (baseStart_6128865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128865 prefixEnd_6128865 := by exact prefixLift 6128865
  have htrace : WordTrace (prefixWord ++ tailWord_6128865) baseStart_6128865 baseEnd_6128865 := by
    simpa [prefixWord, tailWord_6128865, baseEnd_6128865] using wordTrace_append hprefix tailTrace_6128865
  have hstable : (prefixWord ++ tailWord_6128865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128865).length < 2 ^ (prefixWord ++ tailWord_6128865).sum := by decide
  have hdescent : baseEnd_6128865 < baseStart_6128865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128878 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 2, 5]
def baseStart_6128878 : Nat := 118140960795 + 6128878 * 2 ^ 59
def prefixEnd_6128878 : Nat := 4983230072969 + 3 ^ 40 * 6128878 * 2
def baseEnd_6128878 : Nat := 1049020095588925656779603

theorem tailTrace_6128878 : CollatzResearch.WordTrace tailWord_6128878 prefixEnd_6128878 1049020095588925656779603 := by
  unfold tailWord_6128878
  simp only [CollatzResearch.WordTrace]
  refine ⟨27942318136266151234144411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149025696726752806582103525 27942318136266151234144411)
  ·
    refine ⟨41913477204399226851216617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27942318136266151234144411 41913477204399226851216617)
    ·
      refine ⟨31435107903299420138412463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41913477204399226851216617 31435107903299420138412463)
      ·
        refine ⟨47152661854949130207618695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31435107903299420138412463 47152661854949130207618695)
        ·
          refine ⟨70728992782423695311428043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47152661854949130207618695 70728992782423695311428043)
          ·
            refine ⟨106093489173635542967142065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70728992782423695311428043 106093489173635542967142065)
            ·
              refine ⟨79570116880226657225356549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106093489173635542967142065 79570116880226657225356549)
              ·
                refine ⟨14919396915042498229754353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79570116880226657225356549 14919396915042498229754353)
                ·
                  refine ⟨11189547686281873672315765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14919396915042498229754353 11189547686281873672315765)
                  ·
                    refine ⟨1049020095588925656779603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11189547686281873672315765 1049020095588925656779603)
                    ·
                      rfl

theorem cell23_6128878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_6128878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128878 prefixEnd_6128878 := by exact prefixLift 6128878
  have htrace : WordTrace (prefixWord ++ tailWord_6128878) baseStart_6128878 baseEnd_6128878 := by
    simpa [prefixWord, tailWord_6128878, baseEnd_6128878] using wordTrace_append hprefix tailTrace_6128878
  have hstable : (prefixWord ++ tailWord_6128878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128878).length < 2 ^ (prefixWord ++ tailWord_6128878).sum := by decide
  have hdescent : baseEnd_6128878 < baseStart_6128878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128951 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 1, 11]
def baseStart_6128951 : Nat := 118140960795 + 6128951 * 2 ^ 59
def prefixEnd_6128951 : Nat := 4983230072969 + 3 ^ 40 * 6128951 * 2
def baseEnd_6128951 : Nat := 1049032590284851728241991

theorem tailTrace_6128951 : CollatzResearch.WordTrace tailWord_6128951 prefixEnd_6128951 1049032590284851728241991 := by
  unfold tailWord_6128951
  simp only [CollatzResearch.WordTrace]
  refine ⟨223541207618864743340562707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149027471745909828893708471 223541207618864743340562707)
  ·
    refine ⟨335311811428297115010844061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223541207618864743340562707 335311811428297115010844061)
    ·
      refine ⟨125741929285611418129066523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335311811428297115010844061 125741929285611418129066523)
      ·
        refine ⟨188612893928417127193599785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125741929285611418129066523 188612893928417127193599785)
        ·
          refine ⟨141459670446312845395199839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188612893928417127193599785 141459670446312845395199839)
          ·
            refine ⟨212189505669469268092799759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141459670446312845395199839 212189505669469268092799759)
            ·
              refine ⟨318284258504203902139199639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212189505669469268092799759 318284258504203902139199639)
              ·
                refine ⟨477426387756305853208799459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318284258504203902139199639 477426387756305853208799459)
                ·
                  refine ⟨716139581634458779813199189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477426387756305853208799459 716139581634458779813199189)
                  ·
                    refine ⟨1049032590284851728241991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 716139581634458779813199189 1049032590284851728241991)
                    ·
                      rfl

theorem cell23_6128951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_6128951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128951 prefixEnd_6128951 := by exact prefixLift 6128951
  have htrace : WordTrace (prefixWord ++ tailWord_6128951) baseStart_6128951 baseEnd_6128951 := by
    simpa [prefixWord, tailWord_6128951, baseEnd_6128951] using wordTrace_append hprefix tailTrace_6128951
  have hstable : (prefixWord ++ tailWord_6128951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128951).length < 2 ^ (prefixWord ++ tailWord_6128951).sum := by decide
  have hdescent : baseEnd_6128951 < baseStart_6128951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128965 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 3, 1, 3]
def baseStart_6128965 : Nat := 118140960795 + 6128965 * 2 ^ 59
def prefixEnd_6128965 : Nat := 4983230072969 + 3 ^ 40 * 6128965 * 2
def baseEnd_6128965 : Nat := 3147104959583718129950909

theorem tailTrace_6128965 : CollatzResearch.WordTrace tailWord_6128965 prefixEnd_6128965 3147104959583718129950909 := by
  unfold tailWord_6128965
  simp only [CollatzResearch.WordTrace]
  refine ⟨223541718240814023731572349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149027812160542682487714899 223541718240814023731572349)
  ·
    refine ⟨83828144340305258899339631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223541718240814023731572349 83828144340305258899339631)
    ·
      refine ⟨125742216510457888349009447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83828144340305258899339631 125742216510457888349009447)
      ·
        refine ⟨188613324765686832523514171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125742216510457888349009447 188613324765686832523514171)
        ·
          refine ⟨282919987148530248785271257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188613324765686832523514171 282919987148530248785271257)
          ·
            refine ⟨212189990361397686588953443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282919987148530248785271257 212189990361397686588953443)
            ·
              refine ⟨318284985542096529883430165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212189990361397686588953443 318284985542096529883430165)
              ·
                refine ⟨14919608697285774838285789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 318284985542096529883430165 14919608697285774838285789)
                ·
                  refine ⟨5594853261482165564357171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14919608697285774838285789 5594853261482165564357171)
                  ·
                    refine ⟨8392279892223248346535757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5594853261482165564357171 8392279892223248346535757)
                    ·
                      refine ⟨3147104959583718129950909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8392279892223248346535757 3147104959583718129950909)
                      ·
                        rfl

theorem cell23_6128965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_6128965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128965 prefixEnd_6128965 := by exact prefixLift 6128965
  have htrace : WordTrace (prefixWord ++ tailWord_6128965) baseStart_6128965 baseEnd_6128965 := by
    simpa [prefixWord, tailWord_6128965, baseEnd_6128965] using wordTrace_append hprefix tailTrace_6128965
  have hstable : (prefixWord ++ tailWord_6128965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128965).length < 2 ^ (prefixWord ++ tailWord_6128965).sum := by decide
  have hdescent : baseEnd_6128965 < baseStart_6128965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128966 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_6128966 : Nat := 118140960795 + 6128966 * 2 ^ 59
def prefixEnd_6128966 : Nat := 4983230072969 + 3 ^ 40 * 6128966 * 2
def baseEnd_6128966 : Nat := 3147105473064372626038405

theorem tailTrace_6128966 : CollatzResearch.WordTrace tailWord_6128966 prefixEnd_6128966 3147105473064372626038405 := by
  unfold tailWord_6128966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6985679834806575028198711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 149027836475873600601572501 6985679834806575028198711)
  ·
    refine ⟨10478519752209862542298067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6985679834806575028198711 10478519752209862542298067)
    ·
      refine ⟨15717779628314793813447101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10478519752209862542298067 15717779628314793813447101)
      ·
        refine ⟨5894167360618047680042663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15717779628314793813447101 5894167360618047680042663)
        ·
          refine ⟨8841251040927071520063995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5894167360618047680042663 8841251040927071520063995)
          ·
            refine ⟨13261876561390607280095993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8841251040927071520063995 13261876561390607280095993)
            ·
              refine ⟨9946407421042955460071995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13261876561390607280095993 9946407421042955460071995)
              ·
                refine ⟨14919611131564433190107993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9946407421042955460071995 14919611131564433190107993)
                ·
                  refine ⟨11189708348673324892580995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14919611131564433190107993 11189708348673324892580995)
                  ·
                    refine ⟨16784562523009987338871493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11189708348673324892580995 16784562523009987338871493)
                    ·
                      refine ⟨3147105473064372626038405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16784562523009987338871493 3147105473064372626038405)
                      ·
                        rfl

theorem cell23_6128966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_6128966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128966 prefixEnd_6128966 := by exact prefixLift 6128966
  have htrace : WordTrace (prefixWord ++ tailWord_6128966) baseStart_6128966 baseEnd_6128966 := by
    simpa [prefixWord, tailWord_6128966, baseEnd_6128966] using wordTrace_append hprefix tailTrace_6128966
  have hstable : (prefixWord ++ tailWord_6128966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128966).length < 2 ^ (prefixWord ++ tailWord_6128966).sum := by decide
  have hdescent : baseEnd_6128966 < baseStart_6128966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6128992 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 2, 3, 2]
def baseStart_6128992 : Nat := 118140960795 + 6128992 * 2 ^ 59
def prefixEnd_6128992 : Nat := 4983230072969 + 3 ^ 40 * 6128992 * 2
def baseEnd_6128992 : Nat := 3147118823561389524313285

theorem tailTrace_6128992 : CollatzResearch.WordTrace tailWord_6128992 prefixEnd_6128992 3147118823561389524313285 := by
  unfold tailWord_6128992
  simp only [CollatzResearch.WordTrace]
  refine ⟨111771351505858103671402615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149028468674477471561870153 111771351505858103671402615)
  ·
    refine ⟨167657027258787155507103923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111771351505858103671402615 167657027258787155507103923)
    ·
      refine ⟨251485540888180733260655885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167657027258787155507103923 251485540888180733260655885)
      ·
        refine ⟨94307077833067774972745957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251485540888180733260655885 94307077833067774972745957)
        ·
          refine ⟨17682577093700207807389867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94307077833067774972745957 17682577093700207807389867)
          ·
            refine ⟨26523865640550311711084801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17682577093700207807389867 26523865640550311711084801)
            ·
              refine ⟨19892899230412733783313601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26523865640550311711084801 19892899230412733783313601)
              ·
                refine ⟨14919674422809550337485201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19892899230412733783313601 14919674422809550337485201)
                ·
                  refine ⟨11189755817107162753113901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14919674422809550337485201 11189755817107162753113901)
                  ·
                    refine ⟨4196158431415186032417713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11189755817107162753113901 4196158431415186032417713)
                    ·
                      refine ⟨3147118823561389524313285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4196158431415186032417713 3147118823561389524313285)
                      ·
                        rfl

theorem cell23_6128992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_6128992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6128992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6128992 prefixEnd_6128992 := by exact prefixLift 6128992
  have htrace : WordTrace (prefixWord ++ tailWord_6128992) baseStart_6128992 baseEnd_6128992 := by
    simpa [prefixWord, tailWord_6128992, baseEnd_6128992] using wordTrace_append hprefix tailTrace_6128992
  have hstable : (prefixWord ++ tailWord_6128992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6128992).length < 2 ^ (prefixWord ++ tailWord_6128992).sum := by decide
  have hdescent : baseEnd_6128992 < baseStart_6128992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6128992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129005 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_6129005 : Nat := 118140960795 + 6129005 * 2 ^ 59
def prefixEnd_6129005 : Nat := 4983230072969 + 3 ^ 40 * 6129005 * 2
def baseEnd_6129005 : Nat := 3147125498809897973450725

theorem tailTrace_6129005 : CollatzResearch.WordTrace tailWord_6129005 prefixEnd_6129005 3147125498809897973450725 := by
  unfold tailWord_6129005
  simp only [CollatzResearch.WordTrace]
  refine ⟨223543177160669110563028469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149028784773779407042018979 223543177160669110563028469)
  ·
    refine ⟨20957172858812729115283919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223543177160669110563028469 20957172858812729115283919)
    ·
      refine ⟨31435759288219093672925879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20957172858812729115283919 31435759288219093672925879)
      ·
        refine ⟨47153638932328640509388819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31435759288219093672925879 47153638932328640509388819)
        ·
          refine ⟨70730458398492960764083229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47153638932328640509388819 70730458398492960764083229)
          ·
            refine ⟨26523921899434860286531211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70730458398492960764083229 26523921899434860286531211)
            ·
              refine ⟨39785882849152290429796817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26523921899434860286531211 39785882849152290429796817)
              ·
                refine ⟨29839412136864217822347613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39785882849152290429796817 29839412136864217822347613)
                ·
                  refine ⟨11189779551324081683380355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29839412136864217822347613 11189779551324081683380355)
                  ·
                    refine ⟨16784669326986122525070533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11189779551324081683380355 16784669326986122525070533)
                    ·
                      refine ⟨3147125498809897973450725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16784669326986122525070533 3147125498809897973450725)
                      ·
                        rfl

theorem cell23_6129005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_6129005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129005 prefixEnd_6129005 := by exact prefixLift 6129005
  have htrace : WordTrace (prefixWord ++ tailWord_6129005) baseStart_6129005 baseEnd_6129005 := by
    simpa [prefixWord, tailWord_6129005, baseEnd_6129005] using wordTrace_append hprefix tailTrace_6129005
  have hstable : (prefixWord ++ tailWord_6129005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129005).length < 2 ^ (prefixWord ++ tailWord_6129005).sum := by decide
  have hdescent : baseEnd_6129005 < baseStart_6129005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129008 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 5]
def baseStart_6129008 : Nat := 118140960795 + 6129008 * 2 ^ 59
def prefixEnd_6129008 : Nat := 4983230072969 + 3 ^ 40 * 6129008 * 2
def baseEnd_6129008 : Nat := 3147127039251861461713211

theorem tailTrace_6129008 : CollatzResearch.WordTrace tailWord_6129008 prefixEnd_6129008 3147127039251861461713211 := by
  unfold tailWord_6129008
  simp only [CollatzResearch.WordTrace]
  refine ⟨111771643289829121037693839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149028857719772161383591785 111771643289829121037693839)
  ·
    refine ⟨167657464934743681556540759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111771643289829121037693839 167657464934743681556540759)
    ·
      refine ⟨251486197402115522334811139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167657464934743681556540759 251486197402115522334811139)
      ·
        refine ⟨377229296103173283502216709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251486197402115522334811139 377229296103173283502216709)
        ·
          refine ⟨70730493019344990656665633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 377229296103173283502216709 70730493019344990656665633)
          ·
            refine ⟨53047869764508742992499225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70730493019344990656665633 53047869764508742992499225)
            ·
              refine ⟨39785902323381557244374419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53047869764508742992499225 39785902323381557244374419)
              ·
                refine ⟨59678853485072335866561629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39785902323381557244374419 59678853485072335866561629)
                ·
                  refine ⟨22379570056902125949960611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59678853485072335866561629 22379570056902125949960611)
                  ·
                    refine ⟨33569355085353188924940917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22379570056902125949960611 33569355085353188924940917)
                    ·
                      refine ⟨3147127039251861461713211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33569355085353188924940917 3147127039251861461713211)
                      ·
                        rfl

theorem cell23_6129008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_6129008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129008 prefixEnd_6129008 := by exact prefixLift 6129008
  have htrace : WordTrace (prefixWord ++ tailWord_6129008) baseStart_6129008 baseEnd_6129008 := by
    simpa [prefixWord, tailWord_6129008, baseEnd_6129008] using wordTrace_append hprefix tailTrace_6129008
  have hstable : (prefixWord ++ tailWord_6129008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129008).length < 2 ^ (prefixWord ++ tailWord_6129008).sum := by decide
  have hdescent : baseEnd_6129008 < baseStart_6129008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129015 : List Nat := [1, 1, 3, 1, 1, 2, 3, 5, 2, 4]
def baseStart_6129015 : Nat := 118140960795 + 6129015 * 2 ^ 59
def prefixEnd_6129015 : Nat := 4983230072969 + 3 ^ 40 * 6129015 * 2
def baseEnd_6129015 : Nat := 1049043544538814311441893

theorem tailTrace_6129015 : CollatzResearch.WordTrace tailWord_6129015 prefixEnd_6129015 1049043544538814311441893 := by
  unfold tailWord_6129015
  simp only [CollatzResearch.WordTrace]
  refine ⟨223543541890632882270892499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149029027927088588180594999 223543541890632882270892499)
  ·
    refine ⟨335315312835949323406338749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223543541890632882270892499 335315312835949323406338749)
    ·
      refine ⟨125743242313480996277377031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335315312835949323406338749 125743242313480996277377031)
      ·
        refine ⟨188614863470221494416065547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125743242313480996277377031 188614863470221494416065547)
        ·
          refine ⟨282922295205332241624098321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188614863470221494416065547 282922295205332241624098321)
          ·
            refine ⟨212191721403999181218073741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282922295205332241624098321 212191721403999181218073741)
            ·
              refine ⟨79571895526499692956777653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212191721403999181218073741 79571895526499692956777653)
              ·
                refine ⟨7459865205609346214697905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79571895526499692956777653 7459865205609346214697905)
                ·
                  refine ⟨5594898904207009661023429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7459865205609346214697905 5594898904207009661023429)
                  ·
                    refine ⟨1049043544538814311441893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5594898904207009661023429 1049043544538814311441893)
                    ·
                      rfl

theorem cell23_6129015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_6129015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129015 prefixEnd_6129015 := by exact prefixLift 6129015
  have htrace : WordTrace (prefixWord ++ tailWord_6129015) baseStart_6129015 baseEnd_6129015 := by
    simpa [prefixWord, tailWord_6129015, baseEnd_6129015] using wordTrace_append hprefix tailTrace_6129015
  have hstable : (prefixWord ++ tailWord_6129015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129015).length < 2 ^ (prefixWord ++ tailWord_6129015).sum := by decide
  have hdescent : baseEnd_6129015 < baseStart_6129015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129018 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4]
def baseStart_6129018 : Nat := 118140960795 + 6129018 * 2 ^ 59
def prefixEnd_6129018 : Nat := 4983230072969 + 3 ^ 40 * 6129018 * 2
def baseEnd_6129018 : Nat := 3147132174058406422588165

theorem tailTrace_6129018 : CollatzResearch.WordTrace tailWord_6129018 prefixEnd_6129018 3147132174058406422588165 := by
  unfold tailWord_6129018
  simp only [CollatzResearch.WordTrace]
  refine ⟨55885912827405503445812927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149029100873081342522167805 55885912827405503445812927)
  ·
    refine ⟨83828869241108255168719391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55885912827405503445812927 83828869241108255168719391)
    ·
      refine ⟨125743303861662382753079087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83828869241108255168719391 125743303861662382753079087)
      ·
        refine ⟨188614955792493574129618631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125743303861662382753079087 188614955792493574129618631)
        ·
          refine ⟨282922433688740361194427947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188614955792493574129618631 282922433688740361194427947)
          ·
            refine ⟨424383650533110541791641921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282922433688740361194427947 424383650533110541791641921)
            ·
              refine ⟨318287737899832906343731441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424383650533110541791641921 318287737899832906343731441)
              ·
                refine ⟨238715803424874679757798581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318287737899832906343731441 238715803424874679757798581)
                ·
                  refine ⟨22379606571082001227293617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 238715803424874679757798581 22379606571082001227293617)
                  ·
                    refine ⟨16784704928311500920470213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22379606571082001227293617 16784704928311500920470213)
                    ·
                      refine ⟨3147132174058406422588165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16784704928311500920470213 3147132174058406422588165)
                      ·
                        rfl

theorem cell23_6129018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_6129018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129018 prefixEnd_6129018 := by exact prefixLift 6129018
  have htrace : WordTrace (prefixWord ++ tailWord_6129018) baseStart_6129018 baseEnd_6129018 := by
    simpa [prefixWord, tailWord_6129018, baseEnd_6129018] using wordTrace_append hprefix tailTrace_6129018
  have hstable : (prefixWord ++ tailWord_6129018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129018).length < 2 ^ (prefixWord ++ tailWord_6129018).sum := by decide
  have hdescent : baseEnd_6129018 < baseStart_6129018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129026 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_6129026 : Nat := 118140960795 + 6129026 * 2 ^ 59
def prefixEnd_6129026 : Nat := 4983230072969 + 3 ^ 40 * 6129026 * 2
def baseEnd_6129026 : Nat := 3147136281903642391288129

theorem tailTrace_6129026 : CollatzResearch.WordTrace tailWord_6129026 prefixEnd_6129026 3147136281903642391288129 := by
  unfold tailWord_6129026
  simp only [CollatzResearch.WordTrace]
  refine ⟨55885985773398257787385733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149029295395728687433028621 55885985773398257787385733)
  ·
    refine ⟨10478622332512173335134825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55885985773398257787385733 10478622332512173335134825)
    ·
      refine ⟨7858966749384130001351119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10478622332512173335134825 7858966749384130001351119)
      ·
        refine ⟨11788450124076195002026679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7858966749384130001351119 11788450124076195002026679)
        ·
          refine ⟨17682675186114292503040019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11788450124076195002026679 17682675186114292503040019)
          ·
            refine ⟨26524012779171438754560029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17682675186114292503040019 26524012779171438754560029)
            ·
              refine ⟨9946504792189289532960011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26524012779171438754560029 9946504792189289532960011)
              ·
                refine ⟨14919757188283934299440017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9946504792189289532960011 14919757188283934299440017)
                ·
                  refine ⟨11189817891212950724580013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14919757188283934299440017 11189817891212950724580013)
                  ·
                    refine ⟨4196181709204856521717505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11189817891212950724580013 4196181709204856521717505)
                    ·
                      refine ⟨3147136281903642391288129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4196181709204856521717505 3147136281903642391288129)
                      ·
                        rfl

theorem cell23_6129026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_6129026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129026 prefixEnd_6129026 := by exact prefixLift 6129026
  have htrace : WordTrace (prefixWord ++ tailWord_6129026) baseStart_6129026 baseEnd_6129026 := by
    simpa [prefixWord, tailWord_6129026, baseEnd_6129026] using wordTrace_append hprefix tailTrace_6129026
  have hstable : (prefixWord ++ tailWord_6129026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129026).length < 2 ^ (prefixWord ++ tailWord_6129026).sum := by decide
  have hdescent : baseEnd_6129026 < baseStart_6129026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129069 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_6129069 : Nat := 118140960795 + 6129069 * 2 ^ 59
def prefixEnd_6129069 : Nat := 4983230072969 + 3 ^ 40 * 6129069 * 2
def baseEnd_6129069 : Nat := 3147158361571785723050431

theorem tailTrace_6129069 : CollatzResearch.WordTrace tailWord_6129069 prefixEnd_6129069 3147158361571785723050431 := by
  unfold tailWord_6129069
  simp only [CollatzResearch.WordTrace]
  refine ⟨223545511432437249493358261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149030340954958166328905507 223545511432437249493358261)
  ·
    refine ⟨20957391696790992140002337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223545511432437249493358261 20957391696790992140002337)
    ·
      refine ⟨15718043772593244105001753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20957391696790992140002337 15718043772593244105001753)
      ·
        refine ⟨11788532829444933078751315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15718043772593244105001753 11788532829444933078751315)
        ·
          refine ⟨17682799244167399618126973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11788532829444933078751315 17682799244167399618126973)
          ·
            refine ⟨6631049716562774856797615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17682799244167399618126973 6631049716562774856797615)
            ·
              refine ⟨9946574574844162285196423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6631049716562774856797615 9946574574844162285196423)
              ·
                refine ⟨14919861862266243427794635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9946574574844162285196423 14919861862266243427794635)
                ·
                  refine ⟨22379792793399365141691953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14919861862266243427794635 22379792793399365141691953)
                  ·
                    refine ⟨16784844595049523856268965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22379792793399365141691953 16784844595049523856268965)
                    ·
                      refine ⟨3147158361571785723050431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16784844595049523856268965 3147158361571785723050431)
                      ·
                        rfl

theorem cell23_6129069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_6129069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129069 prefixEnd_6129069 := by exact prefixLift 6129069
  have htrace : WordTrace (prefixWord ++ tailWord_6129069) baseStart_6129069 baseEnd_6129069 := by
    simpa [prefixWord, tailWord_6129069, baseEnd_6129069] using wordTrace_append hprefix tailTrace_6129069
  have hstable : (prefixWord ++ tailWord_6129069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129069).length < 2 ^ (prefixWord ++ tailWord_6129069).sum := by decide
  have hdescent : baseEnd_6129069 < baseStart_6129069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129088 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 1, 8]
def baseStart_6129088 : Nat := 118140960795 + 6129088 * 2 ^ 59
def prefixEnd_6129088 : Nat := 4983230072969 + 3 ^ 40 * 6129088 * 2
def baseEnd_6129088 : Nat := 1049056039234740382904281

theorem tailTrace_6129088 : CollatzResearch.WordTrace tailWord_6129088 prefixEnd_6129088 1049056039234740382904281 := by
  unfold tailWord_6129088
  simp only [CollatzResearch.WordTrace]
  refine ⟨111773102209684207869149959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149030802946245610492199945 111773102209684207869149959)
  ·
    refine ⟨167659653314526311803724939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111773102209684207869149959 167659653314526311803724939)
    ·
      refine ⟨251489479971789467705587409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167659653314526311803724939 251489479971789467705587409)
      ·
        refine ⟨188617109978842100779190557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251489479971789467705587409 188617109978842100779190557)
        ·
          refine ⟨70731416242065787792196459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188617109978842100779190557 70731416242065787792196459)
          ·
            refine ⟨106097124363098681688294689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70731416242065787792196459 106097124363098681688294689)
            ·
              refine ⟨79572843272324011266221017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106097124363098681688294689 79572843272324011266221017)
              ·
                refine ⟨59679632454243008449665763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79572843272324011266221017 59679632454243008449665763)
                ·
                  refine ⟨89519448681364512674498645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59679632454243008449665763 89519448681364512674498645)
                  ·
                    refine ⟨1049056039234740382904281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89519448681364512674498645 1049056039234740382904281)
                    ·
                      rfl

theorem cell23_6129088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 8].length) (baseStart_6129088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129088 prefixEnd_6129088 := by exact prefixLift 6129088
  have htrace : WordTrace (prefixWord ++ tailWord_6129088) baseStart_6129088 baseEnd_6129088 := by
    simpa [prefixWord, tailWord_6129088, baseEnd_6129088] using wordTrace_append hprefix tailTrace_6129088
  have hstable : (prefixWord ++ tailWord_6129088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129088).length < 2 ^ (prefixWord ++ tailWord_6129088).sum := by decide
  have hdescent : baseEnd_6129088 < baseStart_6129088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129133 : List Nat := [1, 5, 1, 3, 2, 2, 1, 2, 1, 3, 2]
def baseStart_6129133 : Nat := 118140960795 + 6129133 * 2 ^ 59
def prefixEnd_6129133 : Nat := 4983230072969 + 3 ^ 40 * 6129133 * 2
def baseEnd_6129133 : Nat := 3147191224333673472650137

theorem tailTrace_6129133 : CollatzResearch.WordTrace tailWord_6129133 prefixEnd_6129133 3147191224333673472650137 := by
  unfold tailWord_6129133
  simp only [CollatzResearch.WordTrace]
  refine ⟨223547845704205388423688053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149031897136136925615792035 223547845704205388423688053)
  ·
    refine ⟨20957610534769255164720755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223547845704205388423688053 20957610534769255164720755)
    ·
      refine ⟨31436415802153882747081133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20957610534769255164720755 31436415802153882747081133)
      ·
        refine ⟨11788655925807706030155425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31436415802153882747081133 11788655925807706030155425)
        ·
          refine ⟨8841491944355779522616569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11788655925807706030155425 8841491944355779522616569)
          ·
            refine ⟨6631118958266834641962427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8841491944355779522616569 6631118958266834641962427)
            ·
              refine ⟨9946678437400251962943641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6631118958266834641962427 9946678437400251962943641)
              ·
                refine ⟨7460008828050188972207731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9946678437400251962943641 7460008828050188972207731)
                ·
                  refine ⟨11190013242075283458311597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7460008828050188972207731 11190013242075283458311597)
                  ·
                    refine ⟨4196254965778231296866849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11190013242075283458311597 4196254965778231296866849)
                    ·
                      refine ⟨3147191224333673472650137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4196254965778231296866849 3147191224333673472650137)
                      ·
                        rfl

theorem cell23_6129133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_6129133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129133 prefixEnd_6129133 := by exact prefixLift 6129133
  have htrace : WordTrace (prefixWord ++ tailWord_6129133) baseStart_6129133 baseEnd_6129133 := by
    simpa [prefixWord, tailWord_6129133, baseEnd_6129133] using wordTrace_append hprefix tailTrace_6129133
  have hstable : (prefixWord ++ tailWord_6129133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129133).length < 2 ^ (prefixWord ++ tailWord_6129133).sum := by decide
  have hdescent : baseEnd_6129133 < baseStart_6129133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129145 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 4, 3, 3]
def baseStart_6129145 : Nat := 118140960795 + 6129145 * 2 ^ 59
def prefixEnd_6129145 : Nat := 4983230072969 + 3 ^ 40 * 6129145 * 2
def baseEnd_6129145 : Nat := 3147197386101527425700081

theorem tailTrace_6129145 : CollatzResearch.WordTrace tailWord_6129145 prefixEnd_6129145 3147197386101527425700081 := by
  unfold tailWord_6129145
  simp only [CollatzResearch.WordTrace]
  refine ⟨223548283380161914473124889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149032188920107942982083259 223548283380161914473124889)
  ·
    refine ⟨167661212535121435854843667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223548283380161914473124889 167661212535121435854843667)
    ·
      refine ⟨251491818802682153782265501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167661212535121435854843667 251491818802682153782265501)
      ·
        refine ⟨94309432051005807668349563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251491818802682153782265501 94309432051005807668349563)
        ·
          refine ⟨141464148076508711502524345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94309432051005807668349563 141464148076508711502524345)
          ·
            refine ⟨106098111057381533626893259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141464148076508711502524345 106098111057381533626893259)
            ·
              refine ⟨159147166586072300440339889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106098111057381533626893259 159147166586072300440339889)
              ·
                refine ⟨119360374939554225330254917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159147166586072300440339889 119360374939554225330254917)
                ·
                  refine ⟨22380070301166417249422797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119360374939554225330254917 22380070301166417249422797)
                  ·
                    refine ⟨8392526362937406468533549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22380070301166417249422797 8392526362937406468533549)
                    ·
                      refine ⟨3147197386101527425700081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8392526362937406468533549 3147197386101527425700081)
                      ·
                        rfl

theorem cell23_6129145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_6129145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129145 prefixEnd_6129145 := by exact prefixLift 6129145
  have htrace : WordTrace (prefixWord ++ tailWord_6129145) baseStart_6129145 baseEnd_6129145 := by
    simpa [prefixWord, tailWord_6129145, baseEnd_6129145] using wordTrace_append hprefix tailTrace_6129145
  have hstable : (prefixWord ++ tailWord_6129145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129145).length < 2 ^ (prefixWord ++ tailWord_6129145).sum := by decide
  have hdescent : baseEnd_6129145 < baseStart_6129145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129150 : List Nat := [4, 2, 2, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_6129150 : Nat := 118140960795 + 6129150 * 2 ^ 59
def prefixEnd_6129150 : Nat := 4983230072969 + 3 ^ 40 * 6129150 * 2
def baseEnd_6129150 : Nat := 3147199953504799906137559

theorem tailTrace_6129150 : CollatzResearch.WordTrace tailWord_6129150 prefixEnd_6129150 3147199953504799906137559 := by
  unfold tailWord_6129150
  simp only [CollatzResearch.WordTrace]
  refine ⟨27943558218142975040882113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149032310496762533551371269 27943558218142975040882113)
  ·
    refine ⟨20957668663607231280661585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27943558218142975040882113 20957668663607231280661585)
    ·
      refine ⟨15718251497705423460496189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20957668663607231280661585 15718251497705423460496189)
      ·
        refine ⟨5894344311639533797686071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15718251497705423460496189 5894344311639533797686071)
        ·
          refine ⟨8841516467459300696529107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5894344311639533797686071 8841516467459300696529107)
          ·
            refine ⟨13262274701188951044793661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8841516467459300696529107 13262274701188951044793661)
            ·
              refine ⟨4973353012945856641797623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13262274701188951044793661 4973353012945856641797623)
              ·
                refine ⟨7460029519418784962696435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4973353012945856641797623 7460029519418784962696435)
                ·
                  refine ⟨11190044279128177444044653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7460029519418784962696435 11190044279128177444044653)
                  ·
                    refine ⟨4196266604673066541516745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11190044279128177444044653 4196266604673066541516745)
                    ·
                      refine ⟨3147199953504799906137559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4196266604673066541516745 3147199953504799906137559)
                      ·
                        rfl

theorem cell23_6129150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_6129150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129150 prefixEnd_6129150 := by exact prefixLift 6129150
  have htrace : WordTrace (prefixWord ++ tailWord_6129150) baseStart_6129150 baseEnd_6129150 := by
    simpa [prefixWord, tailWord_6129150, baseEnd_6129150] using wordTrace_append hprefix tailTrace_6129150
  have hstable : (prefixWord ++ tailWord_6129150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129150).length < 2 ^ (prefixWord ++ tailWord_6129150).sum := by decide
  have hdescent : baseEnd_6129150 < baseStart_6129150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129202 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2]
def baseStart_6129202 : Nat := 118140960795 + 6129202 * 2 ^ 59
def prefixEnd_6129202 : Nat := 4983230072969 + 3 ^ 40 * 6129202 * 2
def baseEnd_6129202 : Nat := 3147226654498833702687319

theorem tailTrace_6129202 : CollatzResearch.WordTrace tailWord_6129202 prefixEnd_6129202 3147226654498833702687319 := by
  unfold tailWord_6129202
  simp only [CollatzResearch.WordTrace]
  refine ⟨55887590585238853301987465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149033574893970275471966573 55887590585238853301987465)
  ·
    refine ⟨41915692938929139976490599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55887590585238853301987465 41915692938929139976490599)
    ·
      refine ⟨62873539408393709964735899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41915692938929139976490599 62873539408393709964735899)
      ·
        refine ⟨94310309112590564947103849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62873539408393709964735899 94310309112590564947103849)
        ·
          refine ⟨70732731834442923710327887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94310309112590564947103849 70732731834442923710327887)
          ·
            refine ⟨106099097751664385565491831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70732731834442923710327887 106099097751664385565491831)
            ·
              refine ⟨159148646627496578348237747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106099097751664385565491831 159148646627496578348237747)
              ·
                refine ⟨238722969941244867522356621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159148646627496578348237747 238722969941244867522356621)
                ·
                  refine ⟨89521113727966825320883733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238722969941244867522356621 89521113727966825320883733)
                  ·
                    refine ⟨4196302205998444936916425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89521113727966825320883733 4196302205998444936916425)
                    ·
                      refine ⟨3147226654498833702687319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4196302205998444936916425 3147226654498833702687319)
                      ·
                        rfl

theorem cell23_6129202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_6129202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129202 prefixEnd_6129202 := by exact prefixLift 6129202
  have htrace : WordTrace (prefixWord ++ tailWord_6129202) baseStart_6129202 baseEnd_6129202 := by
    simpa [prefixWord, tailWord_6129202, baseEnd_6129202] using wordTrace_append hprefix tailTrace_6129202
  have hstable : (prefixWord ++ tailWord_6129202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129202).length < 2 ^ (prefixWord ++ tailWord_6129202).sum := by decide
  have hdescent : baseEnd_6129202 < baseStart_6129202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129215 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 6]
def baseStart_6129215 : Nat := 118140960795 + 6129215 * 2 ^ 59
def prefixEnd_6129215 : Nat := 4983230072969 + 3 ^ 40 * 6129215 * 2
def baseEnd_6129215 : Nat := 3147233329747342151824759

theorem tailTrace_6129215 : CollatzResearch.WordTrace tailWord_6129215 prefixEnd_6129215 3147233329747342151824759 := by
  unfold tailWord_6129215
  simp only [CollatzResearch.WordTrace]
  refine ⟨223550836489908316428173099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149033890993272210952115399 223550836489908316428173099)
  ·
    refine ⟨335326254734862474642259649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223550836489908316428173099 335326254734862474642259649)
    ·
      refine ⟨251494691051146855981694737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335326254734862474642259649 251494691051146855981694737)
      ·
        refine ⟨188621018288360141986271053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251494691051146855981694737 188621018288360141986271053)
        ·
          refine ⟨70732881858135053244851645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188621018288360141986271053 70732881858135053244851645)
          ·
            refine ⟨26524830696800644966819367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70732881858135053244851645 26524830696800644966819367)
            ·
              refine ⟨39787246045200967450229051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26524830696800644966819367 39787246045200967450229051)
              ·
                refine ⟨59680869067801451175343577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39787246045200967450229051 59680869067801451175343577)
                ·
                  refine ⟨44760651800851088381507683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59680869067801451175343577 44760651800851088381507683)
                  ·
                    refine ⟨67140977701276632572261525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44760651800851088381507683 67140977701276632572261525)
                    ·
                      refine ⟨3147233329747342151824759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67140977701276632572261525 3147233329747342151824759)
                      ·
                        rfl

theorem cell23_6129215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_6129215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129215 prefixEnd_6129215 := by exact prefixLift 6129215
  have htrace : WordTrace (prefixWord ++ tailWord_6129215) baseStart_6129215 baseEnd_6129215 := by
    simpa [prefixWord, tailWord_6129215, baseEnd_6129215] using wordTrace_append hprefix tailTrace_6129215
  have hstable : (prefixWord ++ tailWord_6129215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129215).length < 2 ^ (prefixWord ++ tailWord_6129215).sum := by decide
  have hdescent : baseEnd_6129215 < baseStart_6129215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129292 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 3, 1, 4]
def baseStart_6129292 : Nat := 118140960795 + 6129292 * 2 ^ 59
def prefixEnd_6129292 : Nat := 4983230072969 + 3 ^ 40 * 6129292 * 2
def baseEnd_6129292 : Nat := 3147272867757738350561905

theorem tailTrace_6129292 : CollatzResearch.WordTrace tailWord_6129292 prefixEnd_6129292 3147272867757738350561905 := by
  unfold tailWord_6129292
  simp only [CollatzResearch.WordTrace]
  refine ⟨111776822455314679289363065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149035763273752905719150753 111776822455314679289363065)
  ·
    refine ⟨83832616841486009467022299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111776822455314679289363065 83832616841486009467022299)
    ·
      refine ⟨125748925262229014200533449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83832616841486009467022299 125748925262229014200533449)
      ·
        refine ⟨94311693946671760650400087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125748925262229014200533449 94311693946671760650400087)
        ·
          refine ⟨141467540920007640975600131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94311693946671760650400087 141467540920007640975600131)
          ·
            refine ⟨212201311380011461463400197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141467540920007640975600131 212201311380011461463400197)
            ·
              refine ⟨39787745883752149024387537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212201311380011461463400197 39787745883752149024387537)
              ·
                refine ⟨29840809412814111768290653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39787745883752149024387537 29840809412814111768290653)
                ·
                  refine ⟨11190303529805291913108995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29840809412814111768290653 11190303529805291913108995)
                  ·
                    refine ⟨16785455294707937869663493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11190303529805291913108995 16785455294707937869663493)
                    ·
                      refine ⟨3147272867757738350561905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16785455294707937869663493 3147272867757738350561905)
                      ·
                        rfl

theorem cell23_6129292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_6129292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129292 prefixEnd_6129292 := by exact prefixLift 6129292
  have htrace : WordTrace (prefixWord ++ tailWord_6129292) baseStart_6129292 baseEnd_6129292 := by
    simpa [prefixWord, tailWord_6129292, baseEnd_6129292] using wordTrace_append hprefix tailTrace_6129292
  have hstable : (prefixWord ++ tailWord_6129292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129292).length < 2 ^ (prefixWord ++ tailWord_6129292).sum := by decide
  have hdescent : baseEnd_6129292 < baseStart_6129292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129315 : List Nat := [1, 1, 1, 4, 1, 1, 3, 11]
def baseStart_6129315 : Nat := 118140960795 + 6129315 * 2 ^ 59
def prefixEnd_6129315 : Nat := 4983230072969 + 3 ^ 40 * 6129315 * 2
def baseEnd_6129315 : Nat := 116566099178251546687937

theorem tailTrace_6129315 : CollatzResearch.WordTrace tailWord_6129315 prefixEnd_6129315 116566099178251546687937 := by
  unfold tailWord_6129315
  simp only [CollatzResearch.WordTrace]
  refine ⟨223554483789546033506813399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149036322526364022337875599 223554483789546033506813399)
  ·
    refine ⟨335331725684319050260220099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223554483789546033506813399 335331725684319050260220099)
    ·
      refine ⟨502997588526478575390330149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335331725684319050260220099 502997588526478575390330149)
      ·
        refine ⟨94312047848714732885686903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 502997588526478575390330149 94312047848714732885686903)
        ·
          refine ⟨141468071773072099328530355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94312047848714732885686903 141468071773072099328530355)
          ·
            refine ⟨212202107659608148992795533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141468071773072099328530355 212202107659608148992795533)
            ·
              refine ⟨79575790372353055872298325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212202107659608148992795533 79575790372353055872298325)
              ·
                refine ⟨116566099178251546687937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 79575790372353055872298325 116566099178251546687937)
                ·
                  rfl

theorem cell23_6129315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 11].length) (baseStart_6129315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129315 prefixEnd_6129315 := by exact prefixLift 6129315
  have htrace : WordTrace (prefixWord ++ tailWord_6129315) baseStart_6129315 baseEnd_6129315 := by
    simpa [prefixWord, tailWord_6129315, baseEnd_6129315] using wordTrace_append hprefix tailTrace_6129315
  have hstable : (prefixWord ++ tailWord_6129315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129315).length < 2 ^ (prefixWord ++ tailWord_6129315).sum := by decide
  have hdescent : baseEnd_6129315 < baseStart_6129315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129343 : List Nat := [1, 1, 2, 2, 2, 3, 3, 4, 1, 2, 2]
def baseStart_6129343 : Nat := 118140960795 + 6129343 * 2 ^ 59
def prefixEnd_6129343 : Nat := 4983230072969 + 3 ^ 40 * 6129343 * 2
def baseEnd_6129343 : Nat := 3147299055271117651024171

theorem tailTrace_6129343 : CollatzResearch.WordTrace tailWord_6129343 prefixEnd_6129343 3147299055271117651024171 := by
  unfold tailWord_6129343
  simp only [CollatzResearch.WordTrace]
  refine ⟨223555505033444594288832683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149037003355629729525888455 223555505033444594288832683)
  ·
    refine ⟨335333257550166891433249025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223555505033444594288832683 335333257550166891433249025)
    ·
      refine ⟨251499943162625168574936769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335333257550166891433249025 251499943162625168574936769)
      ·
        refine ⟨188624957371968876431202577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251499943162625168574936769 188624957371968876431202577)
        ·
          refine ⟨141468718028976657323401933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188624957371968876431202577 141468718028976657323401933)
          ·
            refine ⟨53050769260866246496275725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141468718028976657323401933 53050769260866246496275725)
            ·
              refine ⟨19894038472824842436103397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53050769260866246496275725 19894038472824842436103397)
              ·
                refine ⟨3730132213654657956769387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19894038472824842436103397 3730132213654657956769387)
                ·
                  refine ⟨5595198320481986935154081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3730132213654657956769387 5595198320481986935154081)
                  ·
                    refine ⟨4196398740361490201365561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5595198320481986935154081 4196398740361490201365561)
                    ·
                      refine ⟨3147299055271117651024171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4196398740361490201365561 3147299055271117651024171)
                      ·
                        rfl

theorem cell23_6129343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 1, 2, 2].length) (baseStart_6129343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129343 prefixEnd_6129343 := by exact prefixLift 6129343
  have htrace : WordTrace (prefixWord ++ tailWord_6129343) baseStart_6129343 baseEnd_6129343 := by
    simpa [prefixWord, tailWord_6129343, baseEnd_6129343] using wordTrace_append hprefix tailTrace_6129343
  have hstable : (prefixWord ++ tailWord_6129343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129343).length < 2 ^ (prefixWord ++ tailWord_6129343).sum := by decide
  have hdescent : baseEnd_6129343 < baseStart_6129343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129356 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 1, 2, 4]
def baseStart_6129356 : Nat := 118140960795 + 6129356 * 2 ^ 59
def prefixEnd_6129356 : Nat := 4983230072969 + 3 ^ 40 * 6129356 * 2
def baseEnd_6129356 : Nat := 3147305730519626100161611

theorem tailTrace_6129356 : CollatzResearch.WordTrace tailWord_6129356 prefixEnd_6129356 3147305730519626100161611 := by
  unfold tailWord_6129356
  simp only [CollatzResearch.WordTrace]
  refine ⟨111777989591198748754527961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149037319454931665006037281 111777989591198748754527961)
  ·
    refine ⟨83833492193399061565895971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111777989591198748754527961 83833492193399061565895971)
    ·
      refine ⟨125750238290098592348843957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83833492193399061565895971 125750238290098592348843957)
      ·
        refine ⟨11789084839696743032704121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125750238290098592348843957 11789084839696743032704121)
        ·
          refine ⟨8841813629772557274528091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11789084839696743032704121 8841813629772557274528091)
          ·
            refine ⟨13262720444658835911792137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8841813629772557274528091 13262720444658835911792137)
            ·
              refine ⟨9947040333494126933844103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13262720444658835911792137 9947040333494126933844103)
              ·
                refine ⟨14920560500241190400766155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9947040333494126933844103 14920560500241190400766155)
                ·
                  refine ⟨22380840750361785601149233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14920560500241190400766155 22380840750361785601149233)
                  ·
                    refine ⟨16785630562771339200861925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22380840750361785601149233 16785630562771339200861925)
                    ·
                      refine ⟨3147305730519626100161611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16785630562771339200861925 3147305730519626100161611)
                      ·
                        rfl

theorem cell23_6129356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_6129356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129356 prefixEnd_6129356 := by exact prefixLift 6129356
  have htrace : WordTrace (prefixWord ++ tailWord_6129356) baseStart_6129356 baseEnd_6129356 := by
    simpa [prefixWord, tailWord_6129356, baseEnd_6129356] using wordTrace_append hprefix tailTrace_6129356
  have hstable : (prefixWord ++ tailWord_6129356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129356).length < 2 ^ (prefixWord ++ tailWord_6129356).sum := by decide
  have hdescent : baseEnd_6129356 < baseStart_6129356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129393 : List Nat := [1, 2, 2, 2, 2, 5, 1, 2, 2, 1, 3]
def baseStart_6129393 : Nat := 118140960795 + 6129393 * 2 ^ 59
def prefixEnd_6129393 : Nat := 4983230072969 + 3 ^ 40 * 6129393 * 2
def baseEnd_6129393 : Nat := 3147324729303842455398941

theorem tailTrace_6129393 : CollatzResearch.WordTrace tailWord_6129393 prefixEnd_6129393 3147324729303842455398941 := by
  unfold tailWord_6129393
  simp only [CollatzResearch.WordTrace]
  refine ⟨223557328683263452828152833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149038219122175635218768555 223557328683263452828152833)
  ·
    refine ⟨167667996512447589621114625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223557328683263452828152833 167667996512447589621114625)
    ·
      refine ⟨125750997384335692215835969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167667996512447589621114625 125750997384335692215835969)
      ·
        refine ⟨94313248038251769161876977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125750997384335692215835969 94313248038251769161876977)
        ·
          refine ⟨70734936028688826871407733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94313248038251769161876977 70734936028688826871407733)
          ·
            refine ⟨6631400252689577519194475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70734936028688826871407733 6631400252689577519194475)
            ·
              refine ⟨9947100379034366278791713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6631400252689577519194475 9947100379034366278791713)
              ·
                refine ⟨7460325284275774709093785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9947100379034366278791713 7460325284275774709093785)
                ·
                  refine ⟨5595243963206831031820339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7460325284275774709093785 5595243963206831031820339)
                  ·
                    refine ⟨8392865944810246547730509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5595243963206831031820339 8392865944810246547730509)
                    ·
                      refine ⟨3147324729303842455398941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8392865944810246547730509 3147324729303842455398941)
                      ·
                        rfl

theorem cell23_6129393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_6129393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129393 prefixEnd_6129393 := by exact prefixLift 6129393
  have htrace : WordTrace (prefixWord ++ tailWord_6129393) baseStart_6129393 baseEnd_6129393 := by
    simpa [prefixWord, tailWord_6129393, baseEnd_6129393] using wordTrace_append hprefix tailTrace_6129393
  have hstable : (prefixWord ++ tailWord_6129393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129393).length < 2 ^ (prefixWord ++ tailWord_6129393).sum := by decide
  have hdescent : baseEnd_6129393 < baseStart_6129393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129399 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 3, 4, 2]
def baseStart_6129399 : Nat := 118140960795 + 6129399 * 2 ^ 59
def prefixEnd_6129399 : Nat := 4983230072969 + 3 ^ 40 * 6129399 * 2
def baseEnd_6129399 : Nat := 3147327810187769431923913

theorem tailTrace_6129399 : CollatzResearch.WordTrace tailWord_6129399 prefixEnd_6129399 3147327810187769431923913 := by
  unfold tailWord_6129399
  simp only [CollatzResearch.WordTrace]
  refine ⟨223557547521241715852871251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149038365014161143901914167 223557547521241715852871251)
  ·
    refine ⟨335336321281862573779306877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223557547521241715852871251 335336321281862573779306877)
    ·
      refine ⟨125751120480698465167240079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335336321281862573779306877 125751120480698465167240079)
      ·
        refine ⟨188626680721047697750860119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125751120480698465167240079 188626680721047697750860119)
        ·
          refine ⟨282940021081571546626290179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188626680721047697750860119 282940021081571546626290179)
          ·
            refine ⟨424410031622357319939435269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282940021081571546626290179 424410031622357319939435269)
            ·
              refine ⟨79576880929191997488644113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 424410031622357319939435269 79576880929191997488644113)
              ·
                refine ⟨59682660696893998116483085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79576880929191997488644113 59682660696893998116483085)
                ·
                  refine ⟨22380997761335249293681157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59682660696893998116483085 22380997761335249293681157)
                  ·
                    refine ⟨4196437080250359242565217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22380997761335249293681157 4196437080250359242565217)
                    ·
                      refine ⟨3147327810187769431923913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4196437080250359242565217 3147327810187769431923913)
                      ·
                        rfl

theorem cell23_6129399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 4, 2].length) (baseStart_6129399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129399 prefixEnd_6129399 := by exact prefixLift 6129399
  have htrace : WordTrace (prefixWord ++ tailWord_6129399) baseStart_6129399 baseEnd_6129399 := by
    simpa [prefixWord, tailWord_6129399, baseEnd_6129399] using wordTrace_append hprefix tailTrace_6129399
  have hstable : (prefixWord ++ tailWord_6129399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129399).length < 2 ^ (prefixWord ++ tailWord_6129399).sum := by decide
  have hdescent : baseEnd_6129399 < baseStart_6129399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129402 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5]
def baseStart_6129402 : Nat := 118140960795 + 6129402 * 2 ^ 59
def prefixEnd_6129402 : Nat := 4983230072969 + 3 ^ 40 * 6129402 * 2
def baseEnd_6129402 : Nat := 3147329350629732920186399

theorem tailTrace_6129402 : CollatzResearch.WordTrace tailWord_6129402 prefixEnd_6129402 3147329350629732920186399 := by
  unfold tailWord_6129402
  simp only [CollatzResearch.WordTrace]
  refine ⟨55889414235057711841307615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149038437960153898243486973 55889414235057711841307615)
  ·
    refine ⟨83834121352586567761961423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55889414235057711841307615 83834121352586567761961423)
    ·
      refine ⟨125751182028879851642942135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83834121352586567761961423 125751182028879851642942135)
      ·
        refine ⟨188626773043319777464413203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125751182028879851642942135 188626773043319777464413203)
        ·
          refine ⟨282940159564979666196619805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188626773043319777464413203 282940159564979666196619805)
          ·
            refine ⟨106102559836867374823732427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282940159564979666196619805 106102559836867374823732427)
            ·
              refine ⟨159153839755301062235598641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106102559836867374823732427 159153839755301062235598641)
              ·
                refine ⟨119365379816475796676698981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159153839755301062235598641 119365379816475796676698981)
                ·
                  refine ⟨22381008715589211876881059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119365379816475796676698981 22381008715589211876881059)
                  ·
                    refine ⟨33571513073383817815321589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22381008715589211876881059 33571513073383817815321589)
                    ·
                      refine ⟨3147329350629732920186399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33571513073383817815321589 3147329350629732920186399)
                      ·
                        rfl

theorem cell23_6129402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_6129402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129402 prefixEnd_6129402 := by exact prefixLift 6129402
  have htrace : WordTrace (prefixWord ++ tailWord_6129402) baseStart_6129402 baseEnd_6129402 := by
    simpa [prefixWord, tailWord_6129402, baseEnd_6129402] using wordTrace_append hprefix tailTrace_6129402
  have hstable : (prefixWord ++ tailWord_6129402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129402).length < 2 ^ (prefixWord ++ tailWord_6129402).sum := by decide
  have hdescent : baseEnd_6129402 < baseStart_6129402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129410 : List Nat := [3, 4, 1, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_6129410 : Nat := 118140960795 + 6129410 * 2 ^ 59
def prefixEnd_6129410 : Nat := 4983230072969 + 3 ^ 40 * 6129410 * 2
def baseEnd_6129410 : Nat := 3147333458474968888886363

theorem tailTrace_6129410 : CollatzResearch.WordTrace tailWord_6129410 prefixEnd_6129410 3147333458474968888886363 := by
  unfold tailWord_6129410
  simp only [CollatzResearch.WordTrace]
  refine ⟨55889487181050466182880421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149038632482801243154347789 55889487181050466182880421)
  ·
    refine ⟨10479278846446962409290079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55889487181050466182880421 10479278846446962409290079)
    ·
      refine ⟨15718918269670443613935119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10479278846446962409290079 15718918269670443613935119)
      ·
        refine ⟨23578377404505665420902679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15718918269670443613935119 23578377404505665420902679)
        ·
          refine ⟨35367566106758498131354019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23578377404505665420902679 35367566106758498131354019)
          ·
            refine ⟨53051349160137747197031029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35367566106758498131354019 53051349160137747197031029)
            ·
              refine ⟨4973563983762913799721659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53051349160137747197031029 4973563983762913799721659)
              ·
                refine ⟨7460345975644370699582489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4973563983762913799721659 7460345975644370699582489)
                ·
                  refine ⟨5595259481733278024686867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7460345975644370699582489 5595259481733278024686867)
                  ·
                    refine ⟨8392889222599917037030301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5595259481733278024686867 8392889222599917037030301)
                    ·
                      refine ⟨3147333458474968888886363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8392889222599917037030301 3147333458474968888886363)
                      ·
                        rfl

theorem cell23_6129410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_6129410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129410 prefixEnd_6129410 := by exact prefixLift 6129410
  have htrace : WordTrace (prefixWord ++ tailWord_6129410) baseStart_6129410 baseEnd_6129410 := by
    simpa [prefixWord, tailWord_6129410, baseEnd_6129410] using wordTrace_append hprefix tailTrace_6129410
  have hstable : (prefixWord ++ tailWord_6129410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129410).length < 2 ^ (prefixWord ++ tailWord_6129410).sum := by decide
  have hdescent : baseEnd_6129410 < baseStart_6129410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129428 : List Nat := [2, 4, 4, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_6129428 : Nat := 118140960795 + 6129428 * 2 ^ 59
def prefixEnd_6129428 : Nat := 4983230072969 + 3 ^ 40 * 6129428 * 2
def baseEnd_6129428 : Nat := 3147342701126749818461281

theorem tailTrace_6129428 : CollatzResearch.WordTrace tailWord_6129428 prefixEnd_6129428 3147342701126749818461281 := by
  unfold tailWord_6129428
  simp only [CollatzResearch.WordTrace]
  refine ⟨111779302619068326902838469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149039070158757769203784625 111779302619068326902838469)
  ·
    refine ⟨20958619241075311294282213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111779302619068326902838469 20958619241075311294282213)
    ·
      refine ⟨3929741107701620867677915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20958619241075311294282213 3929741107701620867677915)
      ·
        refine ⟨5894611661552431301516873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3929741107701620867677915 5894611661552431301516873)
        ·
          refine ⟨4420958746164323476137655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5894611661552431301516873 4420958746164323476137655)
          ·
            refine ⟨6631438119246485214206483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4420958746164323476137655 6631438119246485214206483)
            ·
              refine ⟨9947157178869727821309725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6631438119246485214206483 9947157178869727821309725)
              ·
                refine ⟨3730183942076147932991147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9947157178869727821309725 3730183942076147932991147)
                ·
                  refine ⟨5595275913114221899486721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3730183942076147932991147 5595275913114221899486721)
                  ·
                    refine ⟨4196456934835666424615041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5595275913114221899486721 4196456934835666424615041)
                    ·
                      refine ⟨3147342701126749818461281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4196456934835666424615041 3147342701126749818461281)
                      ·
                        rfl

theorem cell23_6129428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_6129428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129428 prefixEnd_6129428 := by exact prefixLift 6129428
  have htrace : WordTrace (prefixWord ++ tailWord_6129428) baseStart_6129428 baseEnd_6129428 := by
    simpa [prefixWord, tailWord_6129428, baseEnd_6129428] using wordTrace_append hprefix tailTrace_6129428
  have hstable : (prefixWord ++ tailWord_6129428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129428).length < 2 ^ (prefixWord ++ tailWord_6129428).sum := by decide
  have hdescent : baseEnd_6129428 < baseStart_6129428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129509 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 3, 4, 3]
def baseStart_6129509 : Nat := 118140960795 + 6129509 * 2 ^ 59
def prefixEnd_6129509 : Nat := 4983230072969 + 3 ^ 40 * 6129509 * 2
def baseEnd_6129509 : Nat := 3147384293059764001548407

theorem tailTrace_6129509 : CollatzResearch.WordTrace tailWord_6129509 prefixEnd_6129509 3147384293059764001548407 := by
  unfold tailWord_6129509
  simp only [CollatzResearch.WordTrace]
  refine ⟨223561559550843204639375581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149041039700562136426250387 223561559550843204639375581)
  ·
    refine ⟨83835584831566201739765843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223561559550843204639375581 83835584831566201739765843)
    ·
      refine ⟨125753377247349302609648765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83835584831566201739765843 125753377247349302609648765)
      ·
        refine ⟨47157516467755988478618287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125753377247349302609648765 47157516467755988478618287)
        ·
          refine ⟨70736274701633982717927431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47157516467755988478618287 70736274701633982717927431)
          ·
            refine ⟨106104412052450974076891147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70736274701633982717927431 106104412052450974076891147)
            ·
              refine ⟨159156618078676461115336721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106104412052450974076891147 159156618078676461115336721)
              ·
                refine ⟨119367463559007345836502541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159156618078676461115336721 119367463559007345836502541)
                ·
                  refine ⟨44762798834627754688688453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119367463559007345836502541 44762798834627754688688453)
                  ·
                    refine ⟨8393024781492704004129085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44762798834627754688688453 8393024781492704004129085)
                    ·
                      refine ⟨3147384293059764001548407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8393024781492704004129085 3147384293059764001548407)
                      ·
                        rfl

theorem cell23_6129509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_6129509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129509 prefixEnd_6129509 := by exact prefixLift 6129509
  have htrace : WordTrace (prefixWord ++ tailWord_6129509) baseStart_6129509 baseEnd_6129509 := by
    simpa [prefixWord, tailWord_6129509, baseEnd_6129509] using wordTrace_append hprefix tailTrace_6129509
  have hstable : (prefixWord ++ tailWord_6129509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129509).length < 2 ^ (prefixWord ++ tailWord_6129509).sum := by decide
  have hdescent : baseEnd_6129509 < baseStart_6129509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129529 : List Nat := [1, 2, 1, 3, 2, 2, 1, 5, 6]
def baseStart_6129529 : Nat := 118140960795 + 6129529 * 2 ^ 59
def prefixEnd_6129529 : Nat := 4983230072969 + 3 ^ 40 * 6129529 * 2
def baseEnd_6129529 : Nat := 349710506963650435922035

theorem tailTrace_6129529 : CollatzResearch.WordTrace tailWord_6129529 prefixEnd_6129529 349710506963650435922035 := by
  unfold tailWord_6129529
  simp only [CollatzResearch.WordTrace]
  refine ⟨223562289010770748055103641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149041526007180498703402427 223562289010770748055103641)
  ·
    refine ⟨167671716758078061041327731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223562289010770748055103641 167671716758078061041327731)
    ·
      refine ⟨251507575137117091561991597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167671716758078061041327731 251507575137117091561991597)
      ·
        refine ⟨94315340676418909335746849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251507575137117091561991597 94315340676418909335746849)
        ·
          refine ⟨70736505507314182001810137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94315340676418909335746849 70736505507314182001810137)
          ·
            refine ⟨53052379130485636501357603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70736505507314182001810137 53052379130485636501357603)
            ·
              refine ⟨79578568695728454752036405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53052379130485636501357603 79578568695728454752036405)
              ·
                refine ⟨7460490815224542633003413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79578568695728454752036405 7460490815224542633003413)
                ·
                  refine ⟨349710506963650435922035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7460490815224542633003413 349710506963650435922035)
                  ·
                    rfl

theorem cell23_6129529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 6].length) (baseStart_6129529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129529 prefixEnd_6129529 := by exact prefixLift 6129529
  have htrace : WordTrace (prefixWord ++ tailWord_6129529) baseStart_6129529 baseEnd_6129529 := by
    simpa [prefixWord, tailWord_6129529, baseEnd_6129529] using wordTrace_append hprefix tailTrace_6129529
  have hstable : (prefixWord ++ tailWord_6129529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129529).length < 2 ^ (prefixWord ++ tailWord_6129529).sum := by decide
  have hdescent : baseEnd_6129529 < baseStart_6129529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129599 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 5]
def baseStart_6129599 : Nat := 118140960795 + 6129599 * 2 ^ 59
def prefixEnd_6129599 : Nat := 4983230072969 + 3 ^ 40 * 6129599 * 2
def baseEnd_6129599 : Nat := 3147430506318668649422993

theorem tailTrace_6129599 : CollatzResearch.WordTrace tailWord_6129599 prefixEnd_6129599 3147430506318668649422993 := by
  unfold tailWord_6129599
  simp only [CollatzResearch.WordTrace]
  refine ⟨223564842120517150010151851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149043228080344766673434567 223564842120517150010151851)
  ·
    refine ⟨335347263180775725015227777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223564842120517150010151851 335347263180775725015227777)
    ·
      refine ⟨251510447385581793761420833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335347263180775725015227777 251510447385581793761420833)
      ·
        refine ⟨188632835539186345321065625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251510447385581793761420833 188632835539186345321065625)
        ·
          refine ⟨141474626654389758990799219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188632835539186345321065625 141474626654389758990799219)
          ·
            refine ⟨212211939981584638486198829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141474626654389758990799219 212211939981584638486198829)
            ·
              refine ⟨79579477493094239432324561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212211939981584638486198829 79579477493094239432324561)
              ·
                refine ⟨59684608119820679574243421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79579477493094239432324561 59684608119820679574243421)
                ·
                  refine ⟨22381728044932754840341283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59684608119820679574243421 22381728044932754840341283)
                  ·
                    refine ⟨33572592067399132260511925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22381728044932754840341283 33572592067399132260511925)
                    ·
                      refine ⟨3147430506318668649422993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33572592067399132260511925 3147430506318668649422993)
                      ·
                        rfl

theorem cell23_6129599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_6129599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129599 prefixEnd_6129599 := by exact prefixLift 6129599
  have htrace : WordTrace (prefixWord ++ tailWord_6129599) baseStart_6129599 baseEnd_6129599 := by
    simpa [prefixWord, tailWord_6129599, baseEnd_6129599] using wordTrace_append hprefix tailTrace_6129599
  have hstable : (prefixWord ++ tailWord_6129599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129599).length < 2 ^ (prefixWord ++ tailWord_6129599).sum := by decide
  have hdescent : baseEnd_6129599 < baseStart_6129599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129659 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 5]
def baseStart_6129659 : Nat := 118140960795 + 6129659 * 2 ^ 59
def prefixEnd_6129659 : Nat := 4983230072969 + 3 ^ 40 * 6129659 * 2
def baseEnd_6129659 : Nat := 3147461315157938414672717

theorem tailTrace_6129659 : CollatzResearch.WordTrace tailWord_6129659 prefixEnd_6129659 3147461315157938414672717 := by
  unfold tailWord_6129659
  simp only [CollatzResearch.WordTrace]
  refine ⟨223567030500299780257336031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149044687000199853504890687 223567030500299780257336031)
  ·
    refine ⟨335350545750449670386004047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223567030500299780257336031 335350545750449670386004047)
    ·
      refine ⟨503025818625674505579006071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335350545750449670386004047 503025818625674505579006071)
      ·
        refine ⟨754538727938511758368509107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503025818625674505579006071 754538727938511758368509107)
        ·
          refine ⟨1131808091907767637552763661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754538727938511758368509107 1131808091907767637552763661)
          ·
            refine ⟨424428034465412864082286373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1131808091907767637552763661 424428034465412864082286373)
            ·
              refine ⟨79580256462264912015428695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 424428034465412864082286373 79580256462264912015428695)
              ·
                refine ⟨119370384693397368023143043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79580256462264912015428695 119370384693397368023143043)
                ·
                  refine ⟨179055577040096052034714565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119370384693397368023143043 179055577040096052034714565)
                  ·
                    refine ⟨33572920695018009756508981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 179055577040096052034714565 33572920695018009756508981)
                    ·
                      refine ⟨3147461315157938414672717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33572920695018009756508981 3147461315157938414672717)
                      ·
                        rfl

theorem cell23_6129659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 5].length) (baseStart_6129659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129659 prefixEnd_6129659 := by exact prefixLift 6129659
  have htrace : WordTrace (prefixWord ++ tailWord_6129659) baseStart_6129659 baseEnd_6129659 := by
    simpa [prefixWord, tailWord_6129659, baseEnd_6129659] using wordTrace_append hprefix tailTrace_6129659
  have hstable : (prefixWord ++ tailWord_6129659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129659).length < 2 ^ (prefixWord ++ tailWord_6129659).sum := by decide
  have hdescent : baseEnd_6129659 < baseStart_6129659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129670 : List Nat := [6, 2, 1, 2, 12]
def baseStart_6129670 : Nat := 118140960795 + 6129670 * 2 ^ 59
def prefixEnd_6129670 : Nat := 4983230072969 + 3 ^ 40 * 6129670 * 2
def baseEnd_6129670 : Nat := 4317512981406224789623

theorem tailTrace_6129670 : CollatzResearch.WordTrace tailWord_6129670 prefixEnd_6129670 4317512981406224789623 := by
  unfold tailWord_6129670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6986482240726872785499577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 149044954468839952757324309 6986482240726872785499577)
  ·
    refine ⟨5239861680545154589124683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6986482240726872785499577 5239861680545154589124683)
    ·
      refine ⟨7859792520817731883687025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5239861680545154589124683 7859792520817731883687025)
      ·
        refine ⟨5894844390613298912765269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7859792520817731883687025 5894844390613298912765269)
        ·
          refine ⟨4317512981406224789623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5894844390613298912765269 4317512981406224789623)
          ·
            rfl

theorem cell23_6129670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 12].length) (baseStart_6129670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129670 prefixEnd_6129670 := by exact prefixLift 6129670
  have htrace : WordTrace (prefixWord ++ tailWord_6129670) baseStart_6129670 baseEnd_6129670 := by
    simpa [prefixWord, tailWord_6129670, baseEnd_6129670] using wordTrace_append hprefix tailTrace_6129670
  have hstable : (prefixWord ++ tailWord_6129670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129670).length < 2 ^ (prefixWord ++ tailWord_6129670).sum := by decide
  have hdescent : baseEnd_6129670 < baseStart_6129670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129763 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 2, 5, 2]
def baseStart_6129763 : Nat := 118140960795 + 6129763 * 2 ^ 59
def prefixEnd_6129763 : Nat := 4983230072969 + 3 ^ 40 * 6129763 * 2
def baseEnd_6129763 : Nat := 3147514717146006007772239

theorem tailTrace_6129763 : CollatzResearch.WordTrace tailWord_6129763 prefixEnd_6129763 3147514717146006007772239 := by
  unfold tailWord_6129763
  simp only [CollatzResearch.WordTrace]
  refine ⟨223570823691923006019121943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149047215794615337346081295 223570823691923006019121943)
  ·
    refine ⟨335356235537884509028682915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223570823691923006019121943 335356235537884509028682915)
    ·
      refine ⟨503034353306826763543024373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335356235537884509028682915 503034353306826763543024373)
      ·
        refine ⟨47159470622515009082158535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 503034353306826763543024373 47159470622515009082158535)
        ·
          refine ⟨70739205933772513623237803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47159470622515009082158535 70739205933772513623237803)
          ·
            refine ⟨106108808900658770434856705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70739205933772513623237803 106108808900658770434856705)
            ·
              refine ⟨79581606675494077826142529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106108808900658770434856705 79581606675494077826142529)
              ·
                refine ⟨59686205006620558369606897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79581606675494077826142529 59686205006620558369606897)
                ·
                  refine ⟨44764653754965418777205173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59686205006620558369606897 44764653754965418777205173)
                  ·
                    refine ⟨4196686289528008010362985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44764653754965418777205173 4196686289528008010362985)
                    ·
                      refine ⟨3147514717146006007772239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4196686289528008010362985 3147514717146006007772239)
                      ·
                        rfl

theorem cell23_6129763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_6129763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129763 prefixEnd_6129763 := by exact prefixLift 6129763
  have htrace : WordTrace (prefixWord ++ tailWord_6129763) baseStart_6129763 baseEnd_6129763 := by
    simpa [prefixWord, tailWord_6129763, baseEnd_6129763] using wordTrace_append hprefix tailTrace_6129763
  have hstable : (prefixWord ++ tailWord_6129763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129763).length < 2 ^ (prefixWord ++ tailWord_6129763).sum := by decide
  have hdescent : baseEnd_6129763 < baseStart_6129763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129773 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_6129773 : Nat := 118140960795 + 6129773 * 2 ^ 59
def prefixEnd_6129773 : Nat := 4983230072969 + 3 ^ 40 * 6129773 * 2
def baseEnd_6129773 : Nat := 1049173283984183656215731

theorem tailTrace_6129773 : CollatzResearch.WordTrace tailWord_6129773 prefixEnd_6129773 1049173283984183656215731 := by
  unfold tailWord_6129773
  simp only [CollatzResearch.WordTrace]
  refine ⟨223571188421886777726985973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149047458947924518484657315 223571188421886777726985973)
  ·
    refine ⟨20959798914551885411904935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223571188421886777726985973 20959798914551885411904935)
    ·
      refine ⟨31439698371827828117857403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20959798914551885411904935 31439698371827828117857403)
      ·
        refine ⟨47159547557741742176786105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31439698371827828117857403 47159547557741742176786105)
        ·
          refine ⟨35369660668306306632589579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47159547557741742176786105 35369660668306306632589579)
          ·
            refine ⟨53054491002459459948884369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35369660668306306632589579 53054491002459459948884369)
            ·
              refine ⟨39790868251844594961663277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53054491002459459948884369 39790868251844594961663277)
              ·
                refine ⟨14921575594441723110623729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39790868251844594961663277 14921575594441723110623729)
                ·
                  refine ⟨11191181695831292332967797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14921575594441723110623729 11191181695831292332967797)
                  ·
                    refine ⟨1049173283984183656215731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11191181695831292332967797 1049173283984183656215731)
                    ·
                      rfl

theorem cell23_6129773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_6129773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129773 prefixEnd_6129773 := by exact prefixLift 6129773
  have htrace : WordTrace (prefixWord ++ tailWord_6129773) baseStart_6129773 baseEnd_6129773 := by
    simpa [prefixWord, tailWord_6129773, baseEnd_6129773] using wordTrace_append hprefix tailTrace_6129773
  have hstable : (prefixWord ++ tailWord_6129773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129773).length < 2 ^ (prefixWord ++ tailWord_6129773).sum := by decide
  have hdescent : baseEnd_6129773 < baseStart_6129773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129810 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_6129810 : Nat := 118140960795 + 6129810 * 2 ^ 59
def prefixEnd_6129810 : Nat := 4983230072969 + 3 ^ 40 * 6129810 * 2
def baseEnd_6129810 : Nat := 3147538850736767323884523

theorem tailTrace_6129810 : CollatzResearch.WordTrace tailWord_6129810 prefixEnd_6129810 3147538850736767323884523 := by
  unfold tailWord_6129810
  simp only [CollatzResearch.WordTrace]
  refine ⟨55893134480688183261520721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149048358615168488697388589 55893134480688183261520721)
  ·
    refine ⟨41919850860516137446140541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55893134480688183261520721 41919850860516137446140541)
    ·
      refine ⟨15719944072693551542302703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41919850860516137446140541 15719944072693551542302703)
      ·
        refine ⟨23579916109040327313454055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15719944072693551542302703 23579916109040327313454055)
        ·
          refine ⟨35369874163560490970181083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23579916109040327313454055 35369874163560490970181083)
          ·
            refine ⟨53054811245340736455271625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35369874163560490970181083 53054811245340736455271625)
            ·
              refine ⟨39791108434005552341453719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53054811245340736455271625 39791108434005552341453719)
              ·
                refine ⟨59686662651008328512180579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39791108434005552341453719 59686662651008328512180579)
                ·
                  refine ⟨89529993976512492768270869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59686662651008328512180579 89529993976512492768270869)
                  ·
                    refine ⟨4196718467649023098512697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89529993976512492768270869 4196718467649023098512697)
                    ·
                      refine ⟨3147538850736767323884523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4196718467649023098512697 3147538850736767323884523)
                      ·
                        rfl

theorem cell23_6129810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_6129810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129810 prefixEnd_6129810 := by exact prefixLift 6129810
  have htrace : WordTrace (prefixWord ++ tailWord_6129810) baseStart_6129810 baseEnd_6129810 := by
    simpa [prefixWord, tailWord_6129810, baseEnd_6129810] using wordTrace_append hprefix tailTrace_6129810
  have hstable : (prefixWord ++ tailWord_6129810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129810).length < 2 ^ (prefixWord ++ tailWord_6129810).sum := by decide
  have hdescent : baseEnd_6129810 < baseStart_6129810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129813 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 4, 2, 3]
def baseStart_6129813 : Nat := 118140960795 + 6129813 * 2 ^ 59
def prefixEnd_6129813 : Nat := 4983230072969 + 3 ^ 40 * 6129813 * 2
def baseEnd_6129813 : Nat := 3147540391178730812147009

theorem tailTrace_6129813 : CollatzResearch.WordTrace tailWord_6129813 prefixEnd_6129813 3147540391178730812147009 := by
  unfold tailWord_6129813
  simp only [CollatzResearch.WordTrace]
  refine ⟨223572647341741864558442093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149048431561161243038961395 223572647341741864558442093)
  ·
    refine ⟨83839742753153199209415785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223572647341741864558442093 83839742753153199209415785)
    ·
      refine ⟨62879807064864899407061839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83839742753153199209415785 62879807064864899407061839)
      ·
        refine ⟨94319710597297349110592759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62879807064864899407061839 94319710597297349110592759)
        ·
          refine ⟨141479565895946023665889139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94319710597297349110592759 141479565895946023665889139)
          ·
            refine ⟨212219348843919035498833709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141479565895946023665889139 212219348843919035498833709)
            ·
              refine ⟨79582255816469638312062641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212219348843919035498833709 79582255816469638312062641)
              ·
                refine ⟨59686691862352228734046981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79582255816469638312062641 59686691862352228734046981)
                ·
                  refine ⟨11191254724191042887633809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59686691862352228734046981 11191254724191042887633809)
                  ·
                    refine ⟨8393441043143282165725357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11191254724191042887633809 8393441043143282165725357)
                    ·
                      refine ⟨3147540391178730812147009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8393441043143282165725357 3147540391178730812147009)
                      ·
                        rfl

theorem cell23_6129813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_6129813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129813 prefixEnd_6129813 := by exact prefixLift 6129813
  have htrace : WordTrace (prefixWord ++ tailWord_6129813) baseStart_6129813 baseEnd_6129813 := by
    simpa [prefixWord, tailWord_6129813, baseEnd_6129813] using wordTrace_append hprefix tailTrace_6129813
  have hstable : (prefixWord ++ tailWord_6129813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129813).length < 2 ^ (prefixWord ++ tailWord_6129813).sum := by decide
  have hdescent : baseEnd_6129813 < baseStart_6129813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129854 : List Nat := [4, 2, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_6129854 : Nat := 118140960795 + 6129854 * 2 ^ 59
def prefixEnd_6129854 : Nat := 4983230072969 + 3 ^ 40 * 6129854 * 2
def baseEnd_6129854 : Nat := 1049187147961855050578107

theorem tailTrace_6129854 : CollatzResearch.WordTrace tailWord_6129854 prefixEnd_6129854 1049187147961855050578107 := by
  unfold tailWord_6129854
  simp only [CollatzResearch.WordTrace]
  refine ⟨27946767841824166070085577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149049428489728885707123077 27946767841824166070085577)
  ·
    refine ⟨20960075881368124552564183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27946767841824166070085577 20960075881368124552564183)
    ·
      refine ⟨31440113822052186828846275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20960075881368124552564183 31440113822052186828846275)
      ·
        refine ⟨47160170733078280243269413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31440113822052186828846275 47160170733078280243269413)
        ·
          refine ⟨8842532012452177545613015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47160170733078280243269413 8842532012452177545613015)
          ·
            refine ⟨13263798018678266318419523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8842532012452177545613015 13263798018678266318419523)
            ·
              refine ⟨19895697028017399477629285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13263798018678266318419523 19895697028017399477629285)
              ·
                refine ⟨3730443192753262402055491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19895697028017399477629285 3730443192753262402055491)
                ·
                  refine ⟨5595664789129893603083237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3730443192753262402055491 5595664789129893603083237)
                  ·
                    refine ⟨1049187147961855050578107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5595664789129893603083237 1049187147961855050578107)
                    ·
                      rfl

theorem cell23_6129854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_6129854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129854 prefixEnd_6129854 := by exact prefixLift 6129854
  have htrace : WordTrace (prefixWord ++ tailWord_6129854) baseStart_6129854 baseEnd_6129854 := by
    simpa [prefixWord, tailWord_6129854, baseEnd_6129854] using wordTrace_append hprefix tailTrace_6129854
  have hstable : (prefixWord ++ tailWord_6129854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129854).length < 2 ^ (prefixWord ++ tailWord_6129854).sum := by decide
  have hdescent : baseEnd_6129854 < baseStart_6129854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129900 : List Nat := [2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 4]
def baseStart_6129900 : Nat := 118140960795 + 6129900 * 2 ^ 59
def prefixEnd_6129900 : Nat := 4983230072969 + 3 ^ 40 * 6129900 * 2
def baseEnd_6129900 : Nat := 3147585063995671971759109

theorem tailTrace_6129900 : CollatzResearch.WordTrace tailWord_6129900 prefixEnd_6129900 3147585063995671971759109 := by
  unfold tailWord_6129900
  simp only [CollatzResearch.WordTrace]
  refine ⟨111787910246213339208429577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149050546994951118944572769 111787910246213339208429577)
  ·
    refine ⟨83840932684660004406322183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111787910246213339208429577 83840932684660004406322183)
    ·
      refine ⟨125761399026990006609483275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83840932684660004406322183 125761399026990006609483275)
      ·
        refine ⟨188642098540485009914224913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125761399026990006609483275 188642098540485009914224913)
        ·
          refine ⟨141481573905363757435668685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188642098540485009914224913 141481573905363757435668685)
          ·
            refine ⟨53055590214511409038375757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141481573905363757435668685 53055590214511409038375757)
            ·
              refine ⟨19895846330441778389390909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53055590214511409038375757 19895846330441778389390909)
              ·
                refine ⟨7460942373915666896021591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19895846330441778389390909 7460942373915666896021591)
                ·
                  refine ⟨11191413560873500344032387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7460942373915666896021591 11191413560873500344032387)
                  ·
                    refine ⟨16787120341310250516048581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11191413560873500344032387 16787120341310250516048581)
                    ·
                      refine ⟨3147585063995671971759109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16787120341310250516048581 3147585063995671971759109)
                      ·
                        rfl

theorem cell23_6129900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_6129900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129900 prefixEnd_6129900 := by exact prefixLift 6129900
  have htrace : WordTrace (prefixWord ++ tailWord_6129900) baseStart_6129900 baseEnd_6129900 := by
    simpa [prefixWord, tailWord_6129900, baseEnd_6129900] using wordTrace_append hprefix tailTrace_6129900
  have hstable : (prefixWord ++ tailWord_6129900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129900).length < 2 ^ (prefixWord ++ tailWord_6129900).sum := by decide
  have hdescent : baseEnd_6129900 < baseStart_6129900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129930 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4]
def baseStart_6129930 : Nat := 118140960795 + 6129930 * 2 ^ 59
def prefixEnd_6129930 : Nat := 4983230072969 + 3 ^ 40 * 6129930 * 2
def baseEnd_6129930 : Nat := 3147600468415306854383971

theorem tailTrace_6129930 : CollatzResearch.WordTrace tailWord_6129930 prefixEnd_6129930 3147600468415306854383971 := by
  unfold tailWord_6129930
  simp only [CollatzResearch.WordTrace]
  refine ⟨55894228670579498385112811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149051276454878662360300829 55894228670579498385112811)
  ·
    refine ⟨83841343005869247577669217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55894228670579498385112811 83841343005869247577669217)
    ·
      refine ⟨62881007254401935683251913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83841343005869247577669217 62881007254401935683251913)
      ·
        refine ⟨47160755440801451762438935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62881007254401935683251913 47160755440801451762438935)
        ·
          refine ⟨70741133161202177643658403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47160755440801451762438935 70741133161202177643658403)
          ·
            refine ⟨106111699741803266465487605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70741133161202177643658403 106111699741803266465487605)
            ·
              refine ⟨9947971850794056231139463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106111699741803266465487605 9947971850794056231139463)
              ·
                refine ⟨14921957776191084346709195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9947971850794056231139463 14921957776191084346709195)
                ·
                  refine ⟨22382936664286626520063793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14921957776191084346709195 22382936664286626520063793)
                  ·
                    refine ⟨16787202498214969890047845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22382936664286626520063793 16787202498214969890047845)
                    ·
                      refine ⟨3147600468415306854383971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16787202498214969890047845 3147600468415306854383971)
                      ·
                        rfl

theorem cell23_6129930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_6129930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129930 prefixEnd_6129930 := by exact prefixLift 6129930
  have htrace : WordTrace (prefixWord ++ tailWord_6129930) baseStart_6129930 baseEnd_6129930 := by
    simpa [prefixWord, tailWord_6129930, baseEnd_6129930] using wordTrace_append hprefix tailTrace_6129930
  have hstable : (prefixWord ++ tailWord_6129930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129930).length < 2 ^ (prefixWord ++ tailWord_6129930).sum := by decide
  have hdescent : baseEnd_6129930 < baseStart_6129930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129937 : List Nat := [1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 3]
def baseStart_6129937 : Nat := 118140960795 + 6129937 * 2 ^ 59
def prefixEnd_6129937 : Nat := 4983230072969 + 3 ^ 40 * 6129937 * 2
def baseEnd_6129937 : Nat := 3147604062779888326996439

theorem tailTrace_6129937 : CollatzResearch.WordTrace tailWord_6129937 prefixEnd_6129937 3147604062779888326996439 := by
  unfold tailWord_6129937
  simp only [CollatzResearch.WordTrace]
  refine ⟨223577169993292633735956065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149051446662195089157304043 223577169993292633735956065)
  ·
    refine ⟨167682877494969475301967049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223577169993292633735956065 167682877494969475301967049)
    ·
      refine ⟨125762158121227106476475287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167682877494969475301967049 125762158121227106476475287)
      ·
        refine ⟨188643237181840659714712931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125762158121227106476475287 188643237181840659714712931)
        ·
          refine ⟨282964855772760989572069397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188643237181840659714712931 282964855772760989572069397)
          ·
            refine ⟨13263977614348171386190753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 282964855772760989572069397 13263977614348171386190753)
            ·
              refine ⟨9947983210761128539643065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13263977614348171386190753 9947983210761128539643065)
              ·
                refine ⟨7460987408070846404732299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9947983210761128539643065 7460987408070846404732299)
                ·
                  refine ⟨11191481112106269607098449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7460987408070846404732299 11191481112106269607098449)
                  ·
                    refine ⟨8393610834079702205323837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11191481112106269607098449 8393610834079702205323837)
                    ·
                      refine ⟨3147604062779888326996439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8393610834079702205323837 3147604062779888326996439)
                      ·
                        rfl

theorem cell23_6129937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_6129937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129937 prefixEnd_6129937 := by exact prefixLift 6129937
  have htrace : WordTrace (prefixWord ++ tailWord_6129937) baseStart_6129937 baseEnd_6129937 := by
    simpa [prefixWord, tailWord_6129937, baseEnd_6129937] using wordTrace_append hprefix tailTrace_6129937
  have hstable : (prefixWord ++ tailWord_6129937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129937).length < 2 ^ (prefixWord ++ tailWord_6129937).sum := by decide
  have hdescent : baseEnd_6129937 < baseStart_6129937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129951 : List Nat := [1, 1, 2, 4, 3, 1, 3, 3, 1, 2, 2]
def baseStart_6129951 : Nat := 118140960795 + 6129951 * 2 ^ 59
def prefixEnd_6129951 : Nat := 4983230072969 + 3 ^ 40 * 6129951 * 2
def baseEnd_6129951 : Nat := 3147611251509051272221375

theorem tailTrace_6129951 : CollatzResearch.WordTrace tailWord_6129951 prefixEnd_6129951 3147611251509051272221375 := by
  unfold tailWord_6129951
  simp only [CollatzResearch.WordTrace]
  refine ⟨223577680615241914126965707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149051787076827942751310471 223577680615241914126965707)
  ·
    refine ⟨335366520922862871190448561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223577680615241914126965707 335366520922862871190448561)
    ·
      refine ⟨251524890692147153392836421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335366520922862871190448561 251524890692147153392836421)
      ·
        refine ⟨47160917004777591261156829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251524890692147153392836421 47160917004777591261156829)
        ·
          refine ⟨17685343876791596722933811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47160917004777591261156829 17685343876791596722933811)
          ·
            refine ⟨26528015815187395084400717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17685343876791596722933811 26528015815187395084400717)
            ·
              refine ⟨9948005930695273156650269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26528015815187395084400717 9948005930695273156650269)
              ·
                refine ⟨3730502224010727433743851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9948005930695273156650269 3730502224010727433743851)
                ·
                  refine ⟨5595753336016091150615777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3730502224010727433743851 5595753336016091150615777)
                  ·
                    refine ⟨4196815002012068362961833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5595753336016091150615777 4196815002012068362961833)
                    ·
                      refine ⟨3147611251509051272221375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4196815002012068362961833 3147611251509051272221375)
                      ·
                        rfl

theorem cell23_6129951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_6129951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129951 prefixEnd_6129951 := by exact prefixLift 6129951
  have htrace : WordTrace (prefixWord ++ tailWord_6129951) baseStart_6129951 baseEnd_6129951 := by
    simpa [prefixWord, tailWord_6129951, baseEnd_6129951] using wordTrace_append hprefix tailTrace_6129951
  have hstable : (prefixWord ++ tailWord_6129951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129951).length < 2 ^ (prefixWord ++ tailWord_6129951).sum := by decide
  have hdescent : baseEnd_6129951 < baseStart_6129951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129983 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 1, 8]
def baseStart_6129983 : Nat := 118140960795 + 6129983 * 2 ^ 59
def prefixEnd_6129983 : Nat := 4983230072969 + 3 ^ 40 * 6129983 * 2
def baseEnd_6129983 : Nat := 1049209227629998382340409

theorem tailTrace_6129983 : CollatzResearch.WordTrace tailWord_6129983 prefixEnd_6129983 1049209227629998382340409 := by
  unfold tailWord_6129983
  simp only [CollatzResearch.WordTrace]
  refine ⟨223578847751125983592130603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149052565167417322394753735 223578847751125983592130603)
  ·
    refine ⟨335368271626688975388195905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223578847751125983592130603 335368271626688975388195905)
    ·
      refine ⟨251526203720016731541146929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335368271626688975388195905 251526203720016731541146929)
      ·
        refine ⟨188644652790012548655860197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251526203720016731541146929 188644652790012548655860197)
        ·
          refine ⟨35370872398127352872973787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188644652790012548655860197 35370872398127352872973787)
          ·
            refine ⟨53056308597191029309460681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35370872398127352872973787 53056308597191029309460681)
            ·
              refine ⟨39792231447893271982095511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53056308597191029309460681 39792231447893271982095511)
              ·
                refine ⟨59688347171839907973143267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39792231447893271982095511 59688347171839907973143267)
                ·
                  refine ⟨89532520757759861959714901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59688347171839907973143267 89532520757759861959714901)
                  ·
                    refine ⟨1049209227629998382340409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89532520757759861959714901 1049209227629998382340409)
                    ·
                      rfl

theorem cell23_6129983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 8].length) (baseStart_6129983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129983 prefixEnd_6129983 := by exact prefixLift 6129983
  have htrace : WordTrace (prefixWord ++ tailWord_6129983) baseStart_6129983 baseEnd_6129983 := by
    simpa [prefixWord, tailWord_6129983, baseEnd_6129983] using wordTrace_append hprefix tailTrace_6129983
  have hstable : (prefixWord ++ tailWord_6129983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129983).length < 2 ^ (prefixWord ++ tailWord_6129983).sum := by decide
  have hdescent : baseEnd_6129983 < baseStart_6129983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129988 : List Nat := [2, 3, 4, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_6129988 : Nat := 118140960795 + 6129988 * 2 ^ 59
def prefixEnd_6129988 : Nat := 4983230072969 + 3 ^ 40 * 6129988 * 2
def baseEnd_6129988 : Nat := 3147630250293267627458705

theorem tailTrace_6129988 : CollatzResearch.WordTrace tailWord_6129988 prefixEnd_6129988 3147630250293267627458705 := by
  unfold tailWord_6129988
  simp only [CollatzResearch.WordTrace]
  refine ⟨111789515058053934723031309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149052686744071912964041745 111789515058053934723031309)
  ·
    refine ⟨41921068146770225521136741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111789515058053934723031309 41921068146770225521136741)
    ·
      refine ⟨7860200277519417285213139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41921068146770225521136741 7860200277519417285213139)
      ·
        refine ⟨11790300416279125927819709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7860200277519417285213139 11790300416279125927819709)
        ·
          refine ⟨4421362656104672222932391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11790300416279125927819709 4421362656104672222932391)
          ·
            refine ⟨6632043984157008334398587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4421362656104672222932391 6632043984157008334398587)
            ·
              refine ⟨9948065976235512501597881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6632043984157008334398587 9948065976235512501597881)
              ·
                refine ⟨7461049482176634376198411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9948065976235512501597881 7461049482176634376198411)
                ·
                  refine ⟨11191574223264951564297617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7461049482176634376198411 11191574223264951564297617)
                  ·
                    refine ⟨8393680667448713673223213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11191574223264951564297617 8393680667448713673223213)
                    ·
                      refine ⟨3147630250293267627458705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8393680667448713673223213 3147630250293267627458705)
                      ·
                        rfl

theorem cell23_6129988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_6129988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6129988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6129988 prefixEnd_6129988 := by exact prefixLift 6129988
  have htrace : WordTrace (prefixWord ++ tailWord_6129988) baseStart_6129988 baseEnd_6129988 := by
    simpa [prefixWord, tailWord_6129988, baseEnd_6129988] using wordTrace_append hprefix tailTrace_6129988
  have hstable : (prefixWord ++ tailWord_6129988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129988).length < 2 ^ (prefixWord ++ tailWord_6129988).sum := by decide
  have hdescent : baseEnd_6129988 < baseStart_6129988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130003 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 4]
def baseStart_6130003 : Nat := 118140960795 + 6130003 * 2 ^ 59
def prefixEnd_6130003 : Nat := 4983230072969 + 3 ^ 40 * 6130003 * 2
def baseEnd_6130003 : Nat := 3147637952503085068771135

theorem tailTrace_6130003 : CollatzResearch.WordTrace tailWord_6130003 prefixEnd_6130003 3147637952503085068771135 := by
  unfold tailWord_6130003
  simp only [CollatzResearch.WordTrace]
  refine ⟨223579577211053527007858663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149053051474035684671905775 223579577211053527007858663)
  ·
    refine ⟨335369365816580290511787995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223579577211053527007858663 335369365816580290511787995)
    ·
      refine ⟨503054048724870435767681993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335369365816580290511787995 503054048724870435767681993)
      ·
        refine ⟨377290536543652826825761495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503054048724870435767681993 377290536543652826825761495)
        ·
          refine ⟨565935804815479240238642243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377290536543652826825761495 565935804815479240238642243)
          ·
            refine ⟨848903707223218860357963365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565935804815479240238642243 848903707223218860357963365)
            ·
              refine ⟨159169445104353536317118131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 848903707223218860357963365 159169445104353536317118131)
              ·
                refine ⟨238754167656530304475677197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159169445104353536317118131 238754167656530304475677197)
                ·
                  refine ⟨89532812871198864178378949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238754167656530304475677197 89532812871198864178378949)
                  ·
                    refine ⟨16787402413349787033446053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89532812871198864178378949 16787402413349787033446053)
                    ·
                      refine ⟨3147637952503085068771135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16787402413349787033446053 3147637952503085068771135)
                      ·
                        rfl

theorem cell23_6130003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_6130003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130003 prefixEnd_6130003 := by exact prefixLift 6130003
  have htrace : WordTrace (prefixWord ++ tailWord_6130003) baseStart_6130003 baseEnd_6130003 := by
    simpa [prefixWord, tailWord_6130003, baseEnd_6130003] using wordTrace_append hprefix tailTrace_6130003
  have hstable : (prefixWord ++ tailWord_6130003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130003).length < 2 ^ (prefixWord ++ tailWord_6130003).sum := by decide
  have hdescent : baseEnd_6130003 < baseStart_6130003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130007 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 1, 4, 2]
def baseStart_6130007 : Nat := 118140960795 + 6130007 * 2 ^ 59
def prefixEnd_6130007 : Nat := 4983230072969 + 3 ^ 40 * 6130007 * 2
def baseEnd_6130007 : Nat := 3147640006425703053121117

theorem tailTrace_6130007 : CollatzResearch.WordTrace tailWord_6130007 prefixEnd_6130007 3147640006425703053121117 := by
  unfold tailWord_6130007
  simp only [CollatzResearch.WordTrace]
  refine ⟨223579723103039035691004275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149053148735359357127336183 223579723103039035691004275)
  ·
    refine ⟨335369584654558553536506413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223579723103039035691004275 335369584654558553536506413)
    ·
      refine ⟨125763594245459457576189905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335369584654558553536506413 125763594245459457576189905)
      ·
        refine ⟨94322695684094593182142429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125763594245459457576189905 94322695684094593182142429)
        ·
          refine ⟨35371010881535472443303411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94322695684094593182142429 35371010881535472443303411)
          ·
            refine ⟨53056516322303208664955117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35371010881535472443303411 53056516322303208664955117)
            ·
              refine ⟨19896193620863703249358169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53056516322303208664955117 19896193620863703249358169)
              ·
                refine ⟨14922145215647777437018627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19896193620863703249358169 14922145215647777437018627)
                ·
                  refine ⟨22383217823471666155527941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14922145215647777437018627 22383217823471666155527941)
                  ·
                    refine ⟨4196853341900937404161489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22383217823471666155527941 4196853341900937404161489)
                    ·
                      refine ⟨3147640006425703053121117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4196853341900937404161489 3147640006425703053121117)
                      ·
                        rfl

theorem cell23_6130007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_6130007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130007 prefixEnd_6130007 := by exact prefixLift 6130007
  have htrace : WordTrace (prefixWord ++ tailWord_6130007) baseStart_6130007 baseEnd_6130007 := by
    simpa [prefixWord, tailWord_6130007, baseEnd_6130007] using wordTrace_append hprefix tailTrace_6130007
  have hstable : (prefixWord ++ tailWord_6130007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130007).length < 2 ^ (prefixWord ++ tailWord_6130007).sum := by decide
  have hdescent : baseEnd_6130007 < baseStart_6130007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130020 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_6130020 : Nat := 118140960795 + 6130020 * 2 ^ 59
def prefixEnd_6130020 : Nat := 4983230072969 + 3 ^ 40 * 6130020 * 2
def baseEnd_6130020 : Nat := 3147646681674211502258557

theorem tailTrace_6130020 : CollatzResearch.WordTrace tailWord_6130020 prefixEnd_6130020 3147646681674211502258557 := by
  unfold tailWord_6130020
  simp only [CollatzResearch.WordTrace]
  refine ⟨111790098625995969455613757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149053464834661292607485009 111790098625995969455613757)
  ·
    refine ⟨41921286984748488545855159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111790098625995969455613757 41921286984748488545855159)
    ·
      refine ⟨62881930477122732818782739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41921286984748488545855159 62881930477122732818782739)
      ·
        refine ⟨94322895715684099228174109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62881930477122732818782739 94322895715684099228174109)
        ·
          refine ⟨35371085893381537210565291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94322895715684099228174109 35371085893381537210565291)
          ·
            refine ⟨53056628840072305815847937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35371085893381537210565291 53056628840072305815847937)
            ·
              refine ⟨39792471630054229361885953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53056628840072305815847937 39792471630054229361885953)
              ·
                refine ⟨29844353722540672021414465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39792471630054229361885953 29844353722540672021414465)
                ·
                  refine ⟨22383265291905504016060849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29844353722540672021414465 22383265291905504016060849)
                  ·
                    refine ⟨16787448968929128012045637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22383265291905504016060849 16787448968929128012045637)
                    ·
                      refine ⟨3147646681674211502258557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16787448968929128012045637 3147646681674211502258557)
                      ·
                        rfl

theorem cell23_6130020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_6130020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130020 prefixEnd_6130020 := by exact prefixLift 6130020
  have htrace : WordTrace (prefixWord ++ tailWord_6130020) baseStart_6130020 baseEnd_6130020 := by
    simpa [prefixWord, tailWord_6130020, baseEnd_6130020] using wordTrace_append hprefix tailTrace_6130020
  have hstable : (prefixWord ++ tailWord_6130020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130020).length < 2 ^ (prefixWord ++ tailWord_6130020).sum := by decide
  have hdescent : baseEnd_6130020 < baseStart_6130020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130033 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 8]
def baseStart_6130033 : Nat := 118140960795 + 6130033 * 2 ^ 59
def prefixEnd_6130033 : Nat := 4983230072969 + 3 ^ 40 * 6130033 * 2
def baseEnd_6130033 : Nat := 3147653356922719951395997

theorem tailTrace_6130033 : CollatzResearch.WordTrace tailWord_6130033 prefixEnd_6130033 3147653356922719951395997 := by
  unfold tailWord_6130033
  simp only [CollatzResearch.WordTrace]
  refine ⟨223580671400944842131450753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149053780933963228087633835 223580671400944842131450753)
  ·
    refine ⟨167685503550708631598588065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223580671400944842131450753 167685503550708631598588065)
    ·
      refine ⟨125764127663031473698941049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167685503550708631598588065 125764127663031473698941049)
      ·
        refine ⟨94323095747273605274205787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125764127663031473698941049 94323095747273605274205787)
        ·
          refine ⟨141484643620910407911308681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94323095747273605274205787 141484643620910407911308681)
          ·
            refine ⟨106113482715682805933481511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141484643620910407911308681 106113482715682805933481511)
            ·
              refine ⟨159170224073524208900222267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106113482715682805933481511 159170224073524208900222267)
              ·
                refine ⟨238755336110286313350333401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159170224073524208900222267 238755336110286313350333401)
                ·
                  refine ⟨179066502082714735012750051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238755336110286313350333401 179066502082714735012750051)
                  ·
                    refine ⟨268599753124072102519125077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 179066502082714735012750051 268599753124072102519125077)
                    ·
                      refine ⟨3147653356922719951395997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 268599753124072102519125077 3147653356922719951395997)
                      ·
                        rfl

theorem cell23_6130033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_6130033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130033 prefixEnd_6130033 := by exact prefixLift 6130033
  have htrace : WordTrace (prefixWord ++ tailWord_6130033) baseStart_6130033 baseEnd_6130033 := by
    simpa [prefixWord, tailWord_6130033, baseEnd_6130033] using wordTrace_append hprefix tailTrace_6130033
  have hstable : (prefixWord ++ tailWord_6130033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130033).length < 2 ^ (prefixWord ++ tailWord_6130033).sum := by decide
  have hdescent : baseEnd_6130033 < baseStart_6130033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130037 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_6130037 : Nat := 118140960795 + 6130037 * 2 ^ 59
def prefixEnd_6130037 : Nat := 4983230072969 + 3 ^ 40 * 6130037 * 2
def baseEnd_6130037 : Nat := 3147655410845337935745979

theorem tailTrace_6130037 : CollatzResearch.WordTrace tailWord_6130037 prefixEnd_6130037 3147655410845337935745979 := by
  unfold tailWord_6130037
  simp only [CollatzResearch.WordTrace]
  refine ⟨223580817292930350814596365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149053878195286900543064243 223580817292930350814596365)
  ·
    refine ⟨83842806484848881555473637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223580817292930350814596365 83842806484848881555473637)
    ·
      refine ⟨15720526215909165291651307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83842806484848881555473637 15720526215909165291651307)
      ·
        refine ⟨23580789323863747937476961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15720526215909165291651307 23580789323863747937476961)
        ·
          refine ⟨17685591992897810953107721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23580789323863747937476961 17685591992897810953107721)
          ·
            refine ⟨13264193994673358214830791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17685591992897810953107721 13264193994673358214830791)
            ·
              refine ⟨19896290992010037322246187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13264193994673358214830791 19896290992010037322246187)
              ·
                refine ⟨29844436488015055983369281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19896290992010037322246187 29844436488015055983369281)
                ·
                  refine ⟨22383327366011291987526961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29844436488015055983369281 22383327366011291987526961)
                  ·
                    refine ⟨16787495524508468990645221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22383327366011291987526961 16787495524508468990645221)
                    ·
                      refine ⟨3147655410845337935745979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16787495524508468990645221 3147655410845337935745979)
                      ·
                        rfl

theorem cell23_6130037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_6130037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130037 prefixEnd_6130037 := by exact prefixLift 6130037
  have htrace : WordTrace (prefixWord ++ tailWord_6130037) baseStart_6130037 baseEnd_6130037 := by
    simpa [prefixWord, tailWord_6130037, baseEnd_6130037] using wordTrace_append hprefix tailTrace_6130037
  have hstable : (prefixWord ++ tailWord_6130037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130037).length < 2 ^ (prefixWord ++ tailWord_6130037).sum := by decide
  have hdescent : baseEnd_6130037 < baseStart_6130037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130060 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 1, 7]
def baseStart_6130060 : Nat := 118140960795 + 6130060 * 2 ^ 59
def prefixEnd_6130060 : Nat := 4983230072969 + 3 ^ 40 * 6130060 * 2
def baseEnd_6130060 : Nat := 1049222406966797115252791

theorem tailTrace_6130060 : CollatzResearch.WordTrace tailWord_6130060 prefixEnd_6130060 1049222406966797115252791 := by
  unfold tailWord_6130060
  simp only [CollatzResearch.WordTrace]
  refine ⟨111790828085923512871341817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149054437447898017161789089 111790828085923512871341817)
  ·
    refine ⟨83843121064442634653506363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111790828085923512871341817 83843121064442634653506363)
    ·
      refine ⟨125764681596663951980259545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83843121064442634653506363 125764681596663951980259545)
      ·
        refine ⟨94323511197497963985194659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125764681596663951980259545 94323511197497963985194659)
        ·
          refine ⟨141485266796246945977791989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94323511197497963985194659 141485266796246945977791989)
          ·
            refine ⟨13264243762148151185417999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141485266796246945977791989 13264243762148151185417999)
            ·
              refine ⟨19896365643222226778126999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13264243762148151185417999 19896365643222226778126999)
              ·
                refine ⟨29844548464833340167190499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19896365643222226778126999 29844548464833340167190499)
                ·
                  refine ⟨44766822697250010250785749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29844548464833340167190499 44766822697250010250785749)
                  ·
                    refine ⟨1049222406966797115252791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44766822697250010250785749 1049222406966797115252791)
                    ·
                      rfl

theorem cell23_6130060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_6130060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130060 prefixEnd_6130060 := by exact prefixLift 6130060
  have htrace : WordTrace (prefixWord ++ tailWord_6130060) baseStart_6130060 baseEnd_6130060 := by
    simpa [prefixWord, tailWord_6130060, baseEnd_6130060] using wordTrace_append hprefix tailTrace_6130060
  have hstable : (prefixWord ++ tailWord_6130060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130060).length < 2 ^ (prefixWord ++ tailWord_6130060).sum := by decide
  have hdescent : baseEnd_6130060 < baseStart_6130060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130120 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 8]
def baseStart_6130120 : Nat := 118140960795 + 6130120 * 2 ^ 59
def prefixEnd_6130120 : Nat := 4983230072969 + 3 ^ 40 * 6130120 * 2
def baseEnd_6130120 : Nat := 349744225526629012334233

theorem tailTrace_6130120 : CollatzResearch.WordTrace tailWord_6130120 prefixEnd_6130120 349744225526629012334233 := by
  unfold tailWord_6130120
  simp only [CollatzResearch.WordTrace]
  refine ⟨111791922275814827994933907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149055896367753103993245209 111791922275814827994933907)
  ·
    refine ⟨167687883413722241992400861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111791922275814827994933907 167687883413722241992400861)
    ·
      refine ⟨62882956280145840747150323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167687883413722241992400861 62882956280145840747150323)
      ·
        refine ⟨94324434420218761120725485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62882956280145840747150323 94324434420218761120725485)
        ·
          refine ⟨35371662907582035420272057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94324434420218761120725485 35371662907582035420272057)
          ·
            refine ⟨26528747180686526565204043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35371662907582035420272057 26528747180686526565204043)
            ·
              refine ⟨39793120771029789847806065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26528747180686526565204043 39793120771029789847806065)
              ·
                refine ⟨29844840578272342385854549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39793120771029789847806065 29844840578272342385854549)
                ·
                  refine ⟨349744225526629012334233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29844840578272342385854549 349744225526629012334233)
                  ·
                    rfl

theorem cell23_6130120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 8].length) (baseStart_6130120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130120 prefixEnd_6130120 := by exact prefixLift 6130120
  have htrace : WordTrace (prefixWord ++ tailWord_6130120) baseStart_6130120 baseEnd_6130120 := by
    simpa [prefixWord, tailWord_6130120, baseEnd_6130120] using wordTrace_append hprefix tailTrace_6130120
  have hstable : (prefixWord ++ tailWord_6130120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130120).length < 2 ^ (prefixWord ++ tailWord_6130120).sum := by decide
  have hdescent : baseEnd_6130120 < baseStart_6130120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130154 : List Nat := [3, 1, 3, 1, 3, 1, 4, 1, 6]
def baseStart_6130154 : Nat := 118140960795 + 6130154 * 2 ^ 59
def prefixEnd_6130154 : Nat := 4983230072969 + 3 ^ 40 * 6130154 * 2
def baseEnd_6130154 : Nat := 349746165342434886442549

theorem tailTrace_6130154 : CollatzResearch.WordTrace tailWord_6130154 prefixEnd_6130154 349746165342434886442549 := by
  unfold tailWord_6130154
  simp only [CollatzResearch.WordTrace]
  refine ⟨55896271158376619949151379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149056723089004319864403677 55896271158376619949151379)
  ·
    refine ⟨83844406737564929923727069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55896271158376619949151379 83844406737564929923727069)
    ·
      refine ⟨31441652526586848721397651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83844406737564929923727069 31441652526586848721397651)
      ·
        refine ⟨47162478789880273082096477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31441652526586848721397651 47162478789880273082096477)
        ·
          refine ⟨17685929546205102405786179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47162478789880273082096477 17685929546205102405786179)
          ·
            refine ⟨26528894319307653608679269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17685929546205102405786179 26528894319307653608679269)
            ·
              refine ⟨4974167684870185051627363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26528894319307653608679269 4974167684870185051627363)
              ·
                refine ⟨7461251527305277577441045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4974167684870185051627363 7461251527305277577441045)
                ·
                  refine ⟨349746165342434886442549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7461251527305277577441045 349746165342434886442549)
                  ·
                    rfl

theorem cell23_6130154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 6].length) (baseStart_6130154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130154 prefixEnd_6130154 := by exact prefixLift 6130154
  have htrace : WordTrace (prefixWord ++ tailWord_6130154) baseStart_6130154 baseEnd_6130154 := by
    simpa [prefixWord, tailWord_6130154, baseEnd_6130154] using wordTrace_append hprefix tailTrace_6130154
  have hstable : (prefixWord ++ tailWord_6130154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130154).length < 2 ^ (prefixWord ++ tailWord_6130154).sum := by decide
  have hdescent : baseEnd_6130154 < baseStart_6130154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130220 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 7]
def baseStart_6130220 : Nat := 118140960795 + 6130220 * 2 ^ 59
def prefixEnd_6130220 : Nat := 4983230072969 + 3 ^ 40 * 6130220 * 2
def baseEnd_6130220 : Nat := 3147749377805110719757637

theorem tailTrace_6130220 : CollatzResearch.WordTrace tailWord_6130220 prefixEnd_6130220 3147749377805110719757637 := by
  unfold tailWord_6130220
  simp only [CollatzResearch.WordTrace]
  refine ⟨111793745925633686534254057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149058327900844915379005409 111793745925633686534254057)
  ·
    refine ⟨83845309444225264900690543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111793745925633686534254057 83845309444225264900690543)
    ·
      refine ⟨125767964166337897351035815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83845309444225264900690543 125767964166337897351035815)
      ·
        refine ⟨188651946249506846026553723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125767964166337897351035815 188651946249506846026553723)
        ·
          refine ⟨282977919374260269039830585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188651946249506846026553723 282977919374260269039830585)
          ·
            refine ⟨212233439530695201779872939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282977919374260269039830585 212233439530695201779872939)
            ·
              refine ⟨318350159296042802669809409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212233439530695201779872939 318350159296042802669809409)
              ·
                refine ⟨238762619472032102002357057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318350159296042802669809409 238762619472032102002357057)
                ·
                  refine ⟨179071964604024076501767793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238762619472032102002357057 179071964604024076501767793)
                  ·
                    refine ⟨134303973453018057376325845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 179071964604024076501767793 134303973453018057376325845)
                    ·
                      refine ⟨3147749377805110719757637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134303973453018057376325845 3147749377805110719757637)
                      ·
                        rfl

theorem cell23_6130220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_6130220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130220 prefixEnd_6130220 := by exact prefixLift 6130220
  have htrace : WordTrace (prefixWord ++ tailWord_6130220) baseStart_6130220 baseEnd_6130220 := by
    simpa [prefixWord, tailWord_6130220, baseEnd_6130220] using wordTrace_append hprefix tailTrace_6130220
  have hstable : (prefixWord ++ tailWord_6130220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130220).length < 2 ^ (prefixWord ++ tailWord_6130220).sum := by decide
  have hdescent : baseEnd_6130220 < baseStart_6130220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130227 : List Nat := [1, 1, 1, 2, 4, 2, 5, 7]
def baseStart_6130227 : Nat := 118140960795 + 6130227 * 2 ^ 59
def prefixEnd_6130227 : Nat := 4983230072969 + 3 ^ 40 * 6130227 * 2
def baseEnd_6130227 : Nat := 116583443413692303421115

theorem tailTrace_6130227 : CollatzResearch.WordTrace tailWord_6130227 prefixEnd_6130227 116583443413692303421115 := by
  unfold tailWord_6130227
  simp only [CollatzResearch.WordTrace]
  refine ⟨223587747162242013264012935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149058498108161342176008623 223587747162242013264012935)
  ·
    refine ⟨335381620743363019896019403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223587747162242013264012935 335381620743363019896019403)
    ·
      refine ⟨503072431115044529844029105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335381620743363019896019403 503072431115044529844029105)
      ·
        refine ⟨377304323336283397383021829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503072431115044529844029105 377304323336283397383021829)
        ·
          refine ⟨70744560625553137009316593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 377304323336283397383021829 70744560625553137009316593)
          ·
            refine ⟨53058420469164852756987445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70744560625553137009316593 53058420469164852756987445)
            ·
              refine ⟨4974226918984204945967573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53058420469164852756987445 4974226918984204945967573)
              ·
                refine ⟨116583443413692303421115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4974226918984204945967573 116583443413692303421115)
                ·
                  rfl

theorem cell23_6130227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 7].length) (baseStart_6130227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130227 prefixEnd_6130227 := by exact prefixLift 6130227
  have htrace : WordTrace (prefixWord ++ tailWord_6130227) baseStart_6130227 baseEnd_6130227 := by
    simpa [prefixWord, tailWord_6130227, baseEnd_6130227] using wordTrace_append hprefix tailTrace_6130227
  have hstable : (prefixWord ++ tailWord_6130227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130227).length < 2 ^ (prefixWord ++ tailWord_6130227).sum := by decide
  have hdescent : baseEnd_6130227 < baseStart_6130227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130238 : List Nat := [4, 2, 1, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_6130238 : Nat := 118140960795 + 6130238 * 2 ^ 59
def prefixEnd_6130238 : Nat := 4983230072969 + 3 ^ 40 * 6130238 * 2
def baseEnd_6130238 : Nat := 3147758620456891649332555

theorem tailTrace_6130238 : CollatzResearch.WordTrace tailWord_6130238 prefixEnd_6130238 3147758620456891649332555 := by
  unfold tailWord_6130238
  simp only [CollatzResearch.WordTrace]
  refine ⟨27948518545650270267832921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149058765576801441428442245 27948518545650270267832921)
  ·
    refine ⟨20961388909237702700874691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27948518545650270267832921 20961388909237702700874691)
    ·
      refine ⟨31442083363856554051312037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20961388909237702700874691 31442083363856554051312037)
      ·
        refine ⟨5895390630723103884621007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31442083363856554051312037 5895390630723103884621007)
        ·
          refine ⟨8843085946084655826931511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5895390630723103884621007 8843085946084655826931511)
          ·
            refine ⟨13264628919126983740397267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8843085946084655826931511 13264628919126983740397267)
            ·
              refine ⟨19896943378690475610595901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13264628919126983740397267 19896943378690475610595901)
              ·
                refine ⟨7461353767008928353973463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19896943378690475610595901 7461353767008928353973463)
                ·
                  refine ⟨11192030650513392530960195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7461353767008928353973463 11192030650513392530960195)
                  ·
                    refine ⟨16788045975770088796440293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11192030650513392530960195 16788045975770088796440293)
                    ·
                      refine ⟨3147758620456891649332555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16788045975770088796440293 3147758620456891649332555)
                      ·
                        rfl

theorem cell23_6130238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_6130238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130238 prefixEnd_6130238 := by exact prefixLift 6130238
  have htrace : WordTrace (prefixWord ++ tailWord_6130238) baseStart_6130238 baseEnd_6130238 := by
    simpa [prefixWord, tailWord_6130238, baseEnd_6130238] using wordTrace_append hprefix tailTrace_6130238
  have hstable : (prefixWord ++ tailWord_6130238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130238).length < 2 ^ (prefixWord ++ tailWord_6130238).sum := by decide
  have hdescent : baseEnd_6130238 < baseStart_6130238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130241 : List Nat := [1, 2, 5, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_6130241 : Nat := 118140960795 + 6130241 * 2 ^ 59
def prefixEnd_6130241 : Nat := 4983230072969 + 3 ^ 40 * 6130241 * 2
def baseEnd_6130241 : Nat := 3147760160898855137595041

theorem tailTrace_6130241 : CollatzResearch.WordTrace tailWord_6130241 prefixEnd_6130241 3147760160898855137595041 := by
  unfold tailWord_6130241
  simp only [CollatzResearch.WordTrace]
  refine ⟨223588257784191293655022577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149058838522794195770015051 223588257784191293655022577)
  ·
    refine ⟨167691193338143470241266933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223588257784191293655022577 167691193338143470241266933)
    ·
      refine ⟨15721049375450950335118775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167691193338143470241266933 15721049375450950335118775)
      ·
        refine ⟨23581574063176425502678163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15721049375450950335118775 23581574063176425502678163)
        ·
          refine ⟨35372361094764638254017245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23581574063176425502678163 35372361094764638254017245)
          ·
            refine ⟨13264635410536739345256467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35372361094764638254017245 13264635410536739345256467)
            ·
              refine ⟨19896953115805109017884701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13264635410536739345256467 19896953115805109017884701)
              ·
                refine ⟨7461357418426915881706763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19896953115805109017884701 7461357418426915881706763)
                ·
                  refine ⟨11192036127640373822560145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7461357418426915881706763 11192036127640373822560145)
                  ·
                    refine ⟨8394027095730280366920109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11192036127640373822560145 8394027095730280366920109)
                    ·
                      refine ⟨3147760160898855137595041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8394027095730280366920109 3147760160898855137595041)
                      ·
                        rfl

theorem cell23_6130241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_6130241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130241 prefixEnd_6130241 := by exact prefixLift 6130241
  have htrace : WordTrace (prefixWord ++ tailWord_6130241) baseStart_6130241 baseEnd_6130241 := by
    simpa [prefixWord, tailWord_6130241, baseEnd_6130241] using wordTrace_append hprefix tailTrace_6130241
  have hstable : (prefixWord ++ tailWord_6130241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130241).length < 2 ^ (prefixWord ++ tailWord_6130241).sum := by decide
  have hdescent : baseEnd_6130241 < baseStart_6130241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130264 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 5, 3, 2]
def baseStart_6130264 : Nat := 118140960795 + 6130264 * 2 ^ 59
def prefixEnd_6130264 : Nat := 4983230072969 + 3 ^ 40 * 6130264 * 2
def baseEnd_6130264 : Nat := 3147771970953908547607435

theorem tailTrace_6130264 : CollatzResearch.WordTrace tailWord_6130264 prefixEnd_6130264 3147771970953908547607435 := by
  unfold tailWord_6130264
  simp only [CollatzResearch.WordTrace]
  refine ⟨111794548331553984291554923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149059397775405312388739897 111794548331553984291554923)
  ·
    refine ⟨167691822497330976437332385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111794548331553984291554923 167691822497330976437332385)
    ·
      refine ⟨125768866872998232327999289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167691822497330976437332385 125768866872998232327999289)
      ·
        refine ⟨94326650154748674245999467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125768866872998232327999289 94326650154748674245999467)
        ·
          refine ⟨141489975232123011368999201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94326650154748674245999467 141489975232123011368999201)
          ·
            refine ⟨106117481424092258526749401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141489975232123011368999201 106117481424092258526749401)
            ·
              refine ⟨79588111068069193895062051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106117481424092258526749401 79588111068069193895062051)
              ·
                refine ⟨119382166602103790842593077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79588111068069193895062051 119382166602103790842593077)
                ·
                  refine ⟨11192078118947230391493101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119382166602103790842593077 11192078118947230391493101)
                  ·
                    refine ⟨4197029294605211396809913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11192078118947230391493101 4197029294605211396809913)
                    ·
                      refine ⟨3147771970953908547607435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4197029294605211396809913 3147771970953908547607435)
                      ·
                        rfl

theorem cell23_6130264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_6130264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130264 prefixEnd_6130264 := by exact prefixLift 6130264
  have htrace : WordTrace (prefixWord ++ tailWord_6130264) baseStart_6130264 baseEnd_6130264 := by
    simpa [prefixWord, tailWord_6130264, baseEnd_6130264] using wordTrace_append hprefix tailTrace_6130264
  have hstable : (prefixWord ++ tailWord_6130264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130264).length < 2 ^ (prefixWord ++ tailWord_6130264).sum := by decide
  have hdescent : baseEnd_6130264 < baseStart_6130264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130268 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_6130268 : Nat := 118140960795 + 6130268 * 2 ^ 59
def prefixEnd_6130268 : Nat := 4983230072969 + 3 ^ 40 * 6130268 * 2
def baseEnd_6130268 : Nat := 3147774024876526531957417

theorem tailTrace_6130268 : CollatzResearch.WordTrace tailWord_6130268 prefixEnd_6130268 3147774024876526531957417 := by
  unfold tailWord_6130268
  simp only [CollatzResearch.WordTrace]
  refine ⟨111794621277546738633127729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149059495036728984844170305 111794621277546738633127729)
  ·
    refine ⟨83845965958160053974845797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111794621277546738633127729 83845965958160053974845797)
    ·
      refine ⟨15721118617155010120283587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83845965958160053974845797 15721118617155010120283587)
      ·
        refine ⟨23581677925732515180425381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15721118617155010120283587 23581677925732515180425381)
        ·
          refine ⟨4421564611074846596329759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23581677925732515180425381 4421564611074846596329759)
          ·
            refine ⟨6632346916612269894494639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4421564611074846596329759 6632346916612269894494639)
            ·
              refine ⟨9948520374918404841741959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6632346916612269894494639 9948520374918404841741959)
              ·
                refine ⟨14922780562377607262612939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9948520374918404841741959 14922780562377607262612939)
                ·
                  refine ⟨22384170843566410893919409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14922780562377607262612939 22384170843566410893919409)
                  ·
                    refine ⟨16788128132674808170439557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22384170843566410893919409 16788128132674808170439557)
                    ·
                      refine ⟨3147774024876526531957417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16788128132674808170439557 3147774024876526531957417)
                      ·
                        rfl

theorem cell23_6130268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_6130268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130268 prefixEnd_6130268 := by exact prefixLift 6130268
  have htrace : WordTrace (prefixWord ++ tailWord_6130268) baseStart_6130268 baseEnd_6130268 := by
    simpa [prefixWord, tailWord_6130268, baseEnd_6130268] using wordTrace_append hprefix tailTrace_6130268
  have hstable : (prefixWord ++ tailWord_6130268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130268).length < 2 ^ (prefixWord ++ tailWord_6130268).sum := by decide
  have hdescent : baseEnd_6130268 < baseStart_6130268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130297 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 1, 3, 5]
def baseStart_6130297 : Nat := 118140960795 + 6130297 * 2 ^ 59
def prefixEnd_6130297 : Nat := 4983230072969 + 3 ^ 40 * 6130297 * 2
def baseEnd_6130297 : Nat := 3147788915815506918494783

theorem tailTrace_6130297 : CollatzResearch.WordTrace tailWord_6130297 prefixEnd_6130297 3147788915815506918494783 := by
  unfold tailWord_6130297
  simp only [CollatzResearch.WordTrace]
  refine ⟨223590300271988415219061145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149060200181325610146040763 223590300271988415219061145)
  ·
    refine ⟨167692725203991311414295859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223590300271988415219061145 167692725203991311414295859)
    ·
      refine ⟨251539087805986967121443789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167692725203991311414295859 251539087805986967121443789)
      ·
        refine ⟨94327157927245112670541421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251539087805986967121443789 94327157927245112670541421)
        ·
          refine ⟨35372684222716917251453033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94327157927245112670541421 35372684222716917251453033)
          ·
            refine ⟨26529513167037687938589775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35372684222716917251453033 26529513167037687938589775)
            ·
              refine ⟨39794269750556531907884663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26529513167037687938589775 39794269750556531907884663)
              ·
                refine ⟨59691404625834797861826995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39794269750556531907884663 59691404625834797861826995)
                ·
                  refine ⟨89537106938752196792740493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59691404625834797861826995 89537106938752196792740493)
                  ·
                    refine ⟨33576415102032073797277685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89537106938752196792740493 33576415102032073797277685)
                    ·
                      refine ⟨3147788915815506918494783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33576415102032073797277685 3147788915815506918494783)
                      ·
                        rfl

theorem cell23_6130297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_6130297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130297 prefixEnd_6130297 := by exact prefixLift 6130297
  have htrace : WordTrace (prefixWord ++ tailWord_6130297) baseStart_6130297 baseEnd_6130297 := by
    simpa [prefixWord, tailWord_6130297, baseEnd_6130297] using wordTrace_append hprefix tailTrace_6130297
  have hstable : (prefixWord ++ tailWord_6130297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130297).length < 2 ^ (prefixWord ++ tailWord_6130297).sum := by decide
  have hdescent : baseEnd_6130297 < baseStart_6130297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130306 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_6130306 : Nat := 118140960795 + 6130306 * 2 ^ 59
def prefixEnd_6130306 : Nat := 4983230072969 + 3 ^ 40 * 6130306 * 2
def baseEnd_6130306 : Nat := 3147793537141397383282243

theorem tailTrace_6130306 : CollatzResearch.WordTrace tailWord_6130306 prefixEnd_6130306 3147793537141397383282243 := by
  unfold tailWord_6130306
  simp only [CollatzResearch.WordTrace]
  refine ⟨55897657132238952439034693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149060419019303873170759181 55897657132238952439034693)
  ·
    refine ⟨10480810712294803582319005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55897657132238952439034693 10480810712294803582319005)
    ·
      refine ⟨3930304017110551343369627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10480810712294803582319005 3930304017110551343369627)
      ·
        refine ⟨5895456025665827015054441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3930304017110551343369627 5895456025665827015054441)
        ·
          refine ⟨4421592019249370261290831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5895456025665827015054441 4421592019249370261290831)
          ·
            refine ⟨6632388028874055391936247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4421592019249370261290831 6632388028874055391936247)
            ·
              refine ⟨9948582043311083087904371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6632388028874055391936247 9948582043311083087904371)
              ·
                refine ⟨14922873064966624631856557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9948582043311083087904371 14922873064966624631856557)
                ·
                  refine ⟨5596077399362484236946209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14922873064966624631856557 5596077399362484236946209)
                  ·
                    refine ⟨4197058049521863177709657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5596077399362484236946209 4197058049521863177709657)
                    ·
                      refine ⟨3147793537141397383282243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4197058049521863177709657 3147793537141397383282243)
                      ·
                        rfl

theorem cell23_6130306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_6130306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130306 prefixEnd_6130306 := by exact prefixLift 6130306
  have htrace : WordTrace (prefixWord ++ tailWord_6130306) baseStart_6130306 baseEnd_6130306 := by
    simpa [prefixWord, tailWord_6130306, baseEnd_6130306] using wordTrace_append hprefix tailTrace_6130306
  have hstable : (prefixWord ++ tailWord_6130306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130306).length < 2 ^ (prefixWord ++ tailWord_6130306).sum := by decide
  have hdescent : baseEnd_6130306 < baseStart_6130306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130307 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 4]
def baseStart_6130307 : Nat := 118140960795 + 6130307 * 2 ^ 59
def prefixEnd_6130307 : Nat := 4983230072969 + 3 ^ 40 * 6130307 * 2
def baseEnd_6130307 : Nat := 3147794050622051879369737

theorem tailTrace_6130307 : CollatzResearch.WordTrace tailWord_6130307 prefixEnd_6130307 3147794050622051879369737 := by
  unfold tailWord_6130307
  simp only [CollatzResearch.WordTrace]
  refine ⟨223590665001952186926925175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149060443334634791284616783 223590665001952186926925175)
  ·
    refine ⟨335385997502928280390387763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223590665001952186926925175 335385997502928280390387763)
    ·
      refine ⟨503078996254392420585581645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335385997502928280390387763 503078996254392420585581645)
      ·
        refine ⟨188654623595397157719593117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 503078996254392420585581645 188654623595397157719593117)
        ·
          refine ⟨70745483848273934144847419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188654623595397157719593117 70745483848273934144847419)
          ·
            refine ⟨106118225772410901217271129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70745483848273934144847419 106118225772410901217271129)
            ·
              refine ⟨79588669329308175912953347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106118225772410901217271129 79588669329308175912953347)
              ·
                refine ⟨119383003993962263869430021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79588669329308175912953347 119383003993962263869430021)
                ·
                  refine ⟨22384313248867924475518129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119383003993962263869430021 22384313248867924475518129)
                  ·
                    refine ⟨16788234936650943356638597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22384313248867924475518129 16788234936650943356638597)
                    ·
                      refine ⟨3147794050622051879369737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16788234936650943356638597 3147794050622051879369737)
                      ·
                        rfl

theorem cell23_6130307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_6130307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130307 prefixEnd_6130307 := by exact prefixLift 6130307
  have htrace : WordTrace (prefixWord ++ tailWord_6130307) baseStart_6130307 baseEnd_6130307 := by
    simpa [prefixWord, tailWord_6130307, baseEnd_6130307] using wordTrace_append hprefix tailTrace_6130307
  have hstable : (prefixWord ++ tailWord_6130307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130307).length < 2 ^ (prefixWord ++ tailWord_6130307).sum := by decide
  have hdescent : baseEnd_6130307 < baseStart_6130307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130311 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 4, 2, 2]
def baseStart_6130311 : Nat := 118140960795 + 6130311 * 2 ^ 59
def prefixEnd_6130311 : Nat := 4983230072969 + 3 ^ 40 * 6130311 * 2
def baseEnd_6130311 : Nat := 3147796104544669863719719

theorem tailTrace_6130311 : CollatzResearch.WordTrace tailWord_6130311 prefixEnd_6130311 3147796104544669863719719 := by
  unfold tailWord_6130311
  simp only [CollatzResearch.WordTrace]
  refine ⟨223590810893937695610070787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149060540595958463740047191 223590810893937695610070787)
  ·
    refine ⟨335386216340906543415106181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223590810893937695610070787 335386216340906543415106181)
    ·
      refine ⟨62884915563919976890332409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335386216340906543415106181 62884915563919976890332409)
      ·
        refine ⟨47163686672939982667749307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62884915563919976890332409 47163686672939982667749307)
        ·
          refine ⟨70745530009409974001623961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47163686672939982667749307 70745530009409974001623961)
          ·
            refine ⟨53059147507057480501217971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70745530009409974001623961 53059147507057480501217971)
            ·
              refine ⟨79588721260586220751826957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53059147507057480501217971 79588721260586220751826957)
              ·
                refine ⟨29845770472719832781935109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79588721260586220751826957 29845770472719832781935109)
                ·
                  refine ⟨5596081963634968646612833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29845770472719832781935109 5596081963634968646612833)
                  ·
                    refine ⟨4197061472726226484959625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5596081963634968646612833 4197061472726226484959625)
                    ·
                      refine ⟨3147796104544669863719719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4197061472726226484959625 3147796104544669863719719)
                      ·
                        rfl

theorem cell23_6130311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_6130311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130311 prefixEnd_6130311 := by exact prefixLift 6130311
  have htrace : WordTrace (prefixWord ++ tailWord_6130311) baseStart_6130311 baseEnd_6130311 := by
    simpa [prefixWord, tailWord_6130311, baseEnd_6130311] using wordTrace_append hprefix tailTrace_6130311
  have hstable : (prefixWord ++ tailWord_6130311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130311).length < 2 ^ (prefixWord ++ tailWord_6130311).sum := by decide
  have hdescent : baseEnd_6130311 < baseStart_6130311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130328 : List Nat := [2, 1, 2, 4, 1, 1, 3, 3, 2, 2, 2]
def baseStart_6130328 : Nat := 118140960795 + 6130328 * 2 ^ 59
def prefixEnd_6130328 : Nat := 4983230072969 + 3 ^ 40 * 6130328 * 2
def baseEnd_6130328 : Nat := 3147804833715796297207141

theorem tailTrace_6130328 : CollatzResearch.WordTrace tailWord_6130328 prefixEnd_6130328 3147804833715796297207141 := by
  unfold tailWord_6130328
  simp only [CollatzResearch.WordTrace]
  refine ⟨111795715467438053756719819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149060953956584071675626425 111795715467438053756719819)
  ·
    refine ⟨167693573201157080635079729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111795715467438053756719819 167693573201157080635079729)
    ·
      refine ⟨125770179900867810476309797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167693573201157080635079729 125770179900867810476309797)
      ·
        refine ⟨23581908731412714464308087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125770179900867810476309797 23581908731412714464308087)
        ·
          refine ⟨35372863097119071696462131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23581908731412714464308087 35372863097119071696462131)
          ·
            refine ⟨53059294645678607544693197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35372863097119071696462131 53059294645678607544693197)
            ·
              refine ⟨19897235492129477829259949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53059294645678607544693197 19897235492129477829259949)
              ·
                refine ⟨7461463309548554185972481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19897235492129477829259949 7461463309548554185972481)
                ·
                  refine ⟨5596097482161415639479361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7461463309548554185972481 5596097482161415639479361)
                  ·
                    refine ⟨4197073111621061729609521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5596097482161415639479361 4197073111621061729609521)
                    ·
                      refine ⟨3147804833715796297207141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4197073111621061729609521 3147804833715796297207141)
                      ·
                        rfl

theorem cell23_6130328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_6130328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130328 prefixEnd_6130328 := by exact prefixLift 6130328
  have htrace : WordTrace (prefixWord ++ tailWord_6130328) baseStart_6130328 baseEnd_6130328 := by
    simpa [prefixWord, tailWord_6130328, baseEnd_6130328] using wordTrace_append hprefix tailTrace_6130328
  have hstable : (prefixWord ++ tailWord_6130328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130328).length < 2 ^ (prefixWord ++ tailWord_6130328).sum := by decide
  have hdescent : baseEnd_6130328 < baseStart_6130328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130334 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 9]
def baseStart_6130334 : Nat := 118140960795 + 6130334 * 2 ^ 59
def prefixEnd_6130334 : Nat := 4983230072969 + 3 ^ 40 * 6130334 * 2
def baseEnd_6130334 : Nat := 349756434955524808192457

theorem tailTrace_6130334 : CollatzResearch.WordTrace tailWord_6130334 prefixEnd_6130334 349756434955524808192457 := by
  unfold tailWord_6130334
  simp only [CollatzResearch.WordTrace]
  refine ⟨27948956221606796317269757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149061099848569580358772037 27948956221606796317269757)
  ·
    refine ⟨10480858583102548618976159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27948956221606796317269757 10480858583102548618976159)
    ·
      refine ⟨15721287874653822928464239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10480858583102548618976159 15721287874653822928464239)
      ·
        refine ⟨23581931811980734392696359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15721287874653822928464239 23581931811980734392696359)
        ·
          refine ⟨35372897717971101589044539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23581931811980734392696359 35372897717971101589044539)
          ·
            refine ⟨53059346576956652383566809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35372897717971101589044539 53059346576956652383566809)
            ·
              refine ⟨39794509932717489287675107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53059346576956652383566809 39794509932717489287675107)
              ·
                refine ⟨59691764899076233931512661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39794509932717489287675107 59691764899076233931512661)
                ·
                  refine ⟨349756434955524808192457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59691764899076233931512661 349756434955524808192457)
                  ·
                    rfl

theorem cell23_6130334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_6130334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130334 prefixEnd_6130334 := by exact prefixLift 6130334
  have htrace : WordTrace (prefixWord ++ tailWord_6130334) baseStart_6130334 baseEnd_6130334 := by
    simpa [prefixWord, tailWord_6130334, baseEnd_6130334] using wordTrace_append hprefix tailTrace_6130334
  have hstable : (prefixWord ++ tailWord_6130334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130334).length < 2 ^ (prefixWord ++ tailWord_6130334).sum := by decide
  have hdescent : baseEnd_6130334 < baseStart_6130334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130364 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 2, 5]
def baseStart_6130364 : Nat := 118140960795 + 6130364 * 2 ^ 59
def prefixEnd_6130364 : Nat := 4983230072969 + 3 ^ 40 * 6130364 * 2
def baseEnd_6130364 : Nat := 1049274439673119385452325

theorem tailTrace_6130364 : CollatzResearch.WordTrace tailWord_6130364 prefixEnd_6130364 1049274439673119385452325 := by
  unfold tailWord_6130364
  simp only [CollatzResearch.WordTrace]
  refine ⟨111796371981372842830875073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149061829308497123774500097 111796371981372842830875073)
  ·
    refine ⟨83847278986029632123156305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111796371981372842830875073 83847278986029632123156305)
    ·
      refine ⟨62885459239522224092367229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83847278986029632123156305 62885459239522224092367229)
      ·
        refine ⟨23582047214820834034637711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62885459239522224092367229 23582047214820834034637711)
        ·
          refine ⟨35373070822231251051956567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23582047214820834034637711 35373070822231251051956567)
          ·
            refine ⟨53059606233346876577934851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35373070822231251051956567 53059606233346876577934851)
            ·
              refine ⟨79589409350020314866902277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53059606233346876577934851 79589409350020314866902277)
              ·
                refine ⟨14923014253128809037544177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79589409350020314866902277 14923014253128809037544177)
                ·
                  refine ⟨11192260689846606778158133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14923014253128809037544177 11192260689846606778158133)
                  ·
                    refine ⟨1049274439673119385452325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11192260689846606778158133 1049274439673119385452325)
                    ·
                      rfl

theorem cell23_6130364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_6130364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130364 prefixEnd_6130364 := by exact prefixLift 6130364
  have htrace : WordTrace (prefixWord ++ tailWord_6130364) baseStart_6130364 baseEnd_6130364 := by
    simpa [prefixWord, tailWord_6130364, baseEnd_6130364] using wordTrace_append hprefix tailTrace_6130364
  have hstable : (prefixWord ++ tailWord_6130364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130364).length < 2 ^ (prefixWord ++ tailWord_6130364).sum := by decide
  have hdescent : baseEnd_6130364 < baseStart_6130364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130368 : List Nat := [2, 1, 1, 2, 4, 4, 2, 2, 5]
def baseStart_6130368 : Nat := 118140960795 + 6130368 * 2 ^ 59
def prefixEnd_6130368 : Nat := 4983230072969 + 3 ^ 40 * 6130368 * 2
def baseEnd_6130368 : Nat := 349758374771330682300773

theorem tailTrace_6130368 : CollatzResearch.WordTrace tailWord_6130368 prefixEnd_6130368 349758374771330682300773 := by
  unfold tailWord_6130368
  simp only [CollatzResearch.WordTrace]
  refine ⟨111796444927365597172447879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149061926569820796229930505 111796444927365597172447879)
  ·
    refine ⟨167694667391048395758671819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111796444927365597172447879 167694667391048395758671819)
    ·
      refine ⟨251542001086572593638007729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167694667391048395758671819 251542001086572593638007729)
      ·
        refine ⟨188656500814929445228505797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251542001086572593638007729 188656500814929445228505797)
        ·
          refine ⟨35373093902799270980344837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188656500814929445228505797 35373093902799270980344837)
          ·
            refine ⟨6632455106774863308814657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35373093902799270980344837 6632455106774863308814657)
            ·
              refine ⟨4974341330081147481610993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6632455106774863308814657 4974341330081147481610993)
              ·
                refine ⟨3730755997560860611208245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4974341330081147481610993 3730755997560860611208245)
                ·
                  refine ⟨349758374771330682300773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3730755997560860611208245 349758374771330682300773)
                  ·
                    rfl

theorem cell23_6130368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 5].length) (baseStart_6130368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130368 prefixEnd_6130368 := by exact prefixLift 6130368
  have htrace : WordTrace (prefixWord ++ tailWord_6130368) baseStart_6130368 baseEnd_6130368 := by
    simpa [prefixWord, tailWord_6130368, baseEnd_6130368] using wordTrace_append hprefix tailTrace_6130368
  have hstable : (prefixWord ++ tailWord_6130368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130368).length < 2 ^ (prefixWord ++ tailWord_6130368).sum := by decide
  have hdescent : baseEnd_6130368 < baseStart_6130368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130401 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 2, 1, 4]
def baseStart_6130401 : Nat := 118140960795 + 6130401 * 2 ^ 59
def prefixEnd_6130401 : Nat := 4983230072969 + 3 ^ 40 * 6130401 * 2
def baseEnd_6130401 : Nat := 3147842317803574511594305

theorem tailTrace_6130401 : CollatzResearch.WordTrace tailWord_6130401 prefixEnd_6130401 3147842317803574511594305 := by
  unfold tailWord_6130401
  simp only [CollatzResearch.WordTrace]
  refine ⟨223594093463611640980847057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149062728975741093987231371 223594093463611640980847057)
  ·
    refine ⟨167695570097708730735635293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223594093463611640980847057 167695570097708730735635293)
    ·
      refine ⟨62885838786640774025863235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167695570097708730735635293 62885838786640774025863235)
      ·
        refine ⟨94328758179961161038794853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62885838786640774025863235 94328758179961161038794853)
        ·
          refine ⟨17686642158742717694774035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94328758179961161038794853 17686642158742717694774035)
          ·
            refine ⟨26529963238114076542161053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17686642158742717694774035 26529963238114076542161053)
            ·
              refine ⟨9948736214292778703310395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26529963238114076542161053 9948736214292778703310395)
              ·
                refine ⟨14923104321439168054965593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9948736214292778703310395 14923104321439168054965593)
                ·
                  refine ⟨11192328241079376041224195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14923104321439168054965593 11192328241079376041224195)
                  ·
                    refine ⟨16788492361619064061836293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11192328241079376041224195 16788492361619064061836293)
                    ·
                      refine ⟨3147842317803574511594305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16788492361619064061836293 3147842317803574511594305)
                      ·
                        rfl

theorem cell23_6130401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_6130401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130401 prefixEnd_6130401 := by exact prefixLift 6130401
  have htrace : WordTrace (prefixWord ++ tailWord_6130401) baseStart_6130401 baseEnd_6130401 := by
    simpa [prefixWord, tailWord_6130401, baseEnd_6130401] using wordTrace_append hprefix tailTrace_6130401
  have hstable : (prefixWord ++ tailWord_6130401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130401).length < 2 ^ (prefixWord ++ tailWord_6130401).sum := by decide
  have hdescent : baseEnd_6130401 < baseStart_6130401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130414 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_6130414 : Nat := 118140960795 + 6130414 * 2 ^ 59
def prefixEnd_6130414 : Nat := 4983230072969 + 3 ^ 40 * 6130414 * 2
def baseEnd_6130414 : Nat := 3147848993052082960731745

theorem tailTrace_6130414 : CollatzResearch.WordTrace tailWord_6130414 prefixEnd_6130414 3147848993052082960731745 := by
  unfold tailWord_6130414
  simp only [CollatzResearch.WordTrace]
  refine ⟨27949320951570568025133787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149063045075043029467380197 27949320951570568025133787)
  ·
    refine ⟨41923981427355852037700681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27949320951570568025133787 41923981427355852037700681)
    ·
      refine ⟨31442986070516889028275511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41923981427355852037700681 31442986070516889028275511)
      ·
        refine ⟨47164479105775333542413267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31442986070516889028275511 47164479105775333542413267)
        ·
          refine ⟨70746718658663000313619901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47164479105775333542413267 70746718658663000313619901)
          ·
            refine ⟨26530019496998625117607463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70746718658663000313619901 26530019496998625117607463)
            ·
              refine ⟨39795029245497937676411195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26530019496998625117607463 39795029245497937676411195)
              ·
                refine ⟨59692543868246906514616793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39795029245497937676411195 59692543868246906514616793)
                ·
                  refine ⟨44769407901185179885962595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59692543868246906514616793 44769407901185179885962595)
                  ·
                    refine ⟨67154111851777769828943893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44769407901185179885962595 67154111851777769828943893)
                    ·
                      refine ⟨3147848993052082960731745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67154111851777769828943893 3147848993052082960731745)
                      ·
                        rfl

theorem cell23_6130414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_6130414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130414 prefixEnd_6130414 := by exact prefixLift 6130414
  have htrace : WordTrace (prefixWord ++ tailWord_6130414) baseStart_6130414 baseEnd_6130414 := by
    simpa [prefixWord, tailWord_6130414, baseEnd_6130414] using wordTrace_append hprefix tailTrace_6130414
  have hstable : (prefixWord ++ tailWord_6130414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130414).length < 2 ^ (prefixWord ++ tailWord_6130414).sum := by decide
  have hdescent : baseEnd_6130414 < baseStart_6130414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130428 : List Nat := [2, 2, 2, 1, 3, 2, 2, 4, 1, 4]
def baseStart_6130428 : Nat := 118140960795 + 6130428 * 2 ^ 59
def prefixEnd_6130428 : Nat := 4983230072969 + 3 ^ 40 * 6130428 * 2
def baseEnd_6130428 : Nat := 1049285393927081968652227

theorem tailTrace_6130428 : CollatzResearch.WordTrace tailWord_6130428 prefixEnd_6130428 1049285393927081968652227 := by
  unfold tailWord_6130428
  simp only [CollatzResearch.WordTrace]
  refine ⟨111797539117256912296039969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149063385489675883061386625 111797539117256912296039969)
  ·
    refine ⟨83848154337942684222029977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111797539117256912296039969 83848154337942684222029977)
    ·
      refine ⟨62886115753457013166522483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83848154337942684222029977 62886115753457013166522483)
      ·
        refine ⟨94329173630185519749783725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62886115753457013166522483 94329173630185519749783725)
        ·
          refine ⟨35373440111319569906168897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94329173630185519749783725 35373440111319569906168897)
          ·
            refine ⟨26530080083489677429626673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35373440111319569906168897 26530080083489677429626673)
            ·
              refine ⟨19897560062617258072220005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26530080083489677429626673 19897560062617258072220005)
              ·
                refine ⟨3730792511740735888541251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19897560062617258072220005 3730792511740735888541251)
                ·
                  refine ⟨5596188767611103832811877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3730792511740735888541251 5596188767611103832811877)
                  ·
                    refine ⟨1049285393927081968652227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5596188767611103832811877 1049285393927081968652227)
                    ·
                      rfl

theorem cell23_6130428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_6130428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130428 prefixEnd_6130428 := by exact prefixLift 6130428
  have htrace : WordTrace (prefixWord ++ tailWord_6130428) baseStart_6130428 baseEnd_6130428 := by
    simpa [prefixWord, tailWord_6130428, baseEnd_6130428] using wordTrace_append hprefix tailTrace_6130428
  have hstable : (prefixWord ++ tailWord_6130428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130428).length < 2 ^ (prefixWord ++ tailWord_6130428).sum := by decide
  have hdescent : baseEnd_6130428 < baseStart_6130428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130451 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 3, 1, 3]
def baseStart_6130451 : Nat := 118140960795 + 6130451 * 2 ^ 59
def prefixEnd_6130451 : Nat := 4983230072969 + 3 ^ 40 * 6130451 * 2
def baseEnd_6130451 : Nat := 3147867991836299315969075

theorem tailTrace_6130451 : CollatzResearch.WordTrace tailWord_6130451 prefixEnd_6130451 3147867991836299315969075 := by
  unfold tailWord_6130451
  simp only [CollatzResearch.WordTrace]
  refine ⟨223595917113430499520167207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149063944742286999680111471 223595917113430499520167207)
  ·
    refine ⟨335393875670145749280250811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223595917113430499520167207 335393875670145749280250811)
    ·
      refine ⟨503090813505218623920376217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335393875670145749280250811 503090813505218623920376217)
      ·
        refine ⟨377318110128913967940282163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503090813505218623920376217 377318110128913967940282163)
        ·
          refine ⟨565977165193370951910423245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377318110128913967940282163 565977165193370951910423245)
          ·
            refine ⟨212241436947514106966408717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 565977165193370951910423245 212241436947514106966408717)
            ·
              refine ⟨79590538855317790112403269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212241436947514106966408717 79590538855317790112403269)
              ·
                refine ⟨14923226035372085646075613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79590538855317790112403269 14923226035372085646075613)
                ·
                  refine ⟨5596209763264532117278355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14923226035372085646075613 5596209763264532117278355)
                  ·
                    refine ⟨8394314644896798175917533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5596209763264532117278355 8394314644896798175917533)
                    ·
                      refine ⟨3147867991836299315969075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8394314644896798175917533 3147867991836299315969075)
                      ·
                        rfl

theorem cell23_6130451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 1, 3].length) (baseStart_6130451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130451 prefixEnd_6130451 := by exact prefixLift 6130451
  have htrace : WordTrace (prefixWord ++ tailWord_6130451) baseStart_6130451 baseEnd_6130451 := by
    simpa [prefixWord, tailWord_6130451, baseEnd_6130451] using wordTrace_append hprefix tailTrace_6130451
  have hstable : (prefixWord ++ tailWord_6130451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130451).length < 2 ^ (prefixWord ++ tailWord_6130451).sum := by decide
  have hdescent : baseEnd_6130451 < baseStart_6130451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130485 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_6130485 : Nat := 118140960795 + 6130485 * 2 ^ 59
def prefixEnd_6130485 : Nat := 4983230072969 + 3 ^ 40 * 6130485 * 2
def baseEnd_6130485 : Nat := 3147885450178552182943919

theorem tailTrace_6130485 : CollatzResearch.WordTrace tailWord_6130485 prefixEnd_6130485 3147885450178552182943919 := by
  unfold tailWord_6130485
  simp only [CollatzResearch.WordTrace]
  refine ⟨223597157195307323326904909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149064771463538215551269939 223597157195307323326904909)
  ·
    refine ⟨83848933948240246247589341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223597157195307323326904909 83848933948240246247589341)
    ·
      refine ⟨31443350230590092342846003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83848933948240246247589341 31443350230590092342846003)
      ·
        refine ⟨47165025345885138514269005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31443350230590092342846003 47165025345885138514269005)
        ·
          refine ⟨17686884504706926942850877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47165025345885138514269005 17686884504706926942850877)
          ·
            refine ⟨6632581689265097603569079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17686884504706926942850877 6632581689265097603569079)
            ·
              refine ⟨9948872533897646405353619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6632581689265097603569079 9948872533897646405353619)
              ·
                refine ⟨14923308800846469608030429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9948872533897646405353619 14923308800846469608030429)
                ·
                  refine ⟨5596240800317426103011411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14923308800846469608030429 5596240800317426103011411)
                  ·
                    refine ⟨8394361200476139154517117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5596240800317426103011411 8394361200476139154517117)
                    ·
                      refine ⟨3147885450178552182943919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8394361200476139154517117 3147885450178552182943919)
                      ·
                        rfl

theorem cell23_6130485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_6130485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130485 prefixEnd_6130485 := by exact prefixLift 6130485
  have htrace : WordTrace (prefixWord ++ tailWord_6130485) baseStart_6130485 baseEnd_6130485 := by
    simpa [prefixWord, tailWord_6130485, baseEnd_6130485] using wordTrace_append hprefix tailTrace_6130485
  have hstable : (prefixWord ++ tailWord_6130485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130485).length < 2 ^ (prefixWord ++ tailWord_6130485).sum := by decide
  have hdescent : baseEnd_6130485 < baseStart_6130485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130504 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_6130504 : Nat := 118140960795 + 6130504 * 2 ^ 59
def prefixEnd_6130504 : Nat := 4983230072969 + 3 ^ 40 * 6130504 * 2
def baseEnd_6130504 : Nat := 3147895206310987608606331

theorem tailTrace_6130504 : CollatzResearch.WordTrace tailWord_6130504 prefixEnd_6130504 3147895206310987608606331 := by
  unfold tailWord_6130504
  simp only [CollatzResearch.WordTrace]
  refine ⟨111798925091119244785923283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149065233454825659714564377 111798925091119244785923283)
  ·
    refine ⟨167698387636678867178884925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111798925091119244785923283 167698387636678867178884925)
    ·
      refine ⟨62886895363754575192081847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167698387636678867178884925 62886895363754575192081847)
      ·
        refine ⟨94330343045631862788122771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62886895363754575192081847 94330343045631862788122771)
        ·
          refine ⟨141495514568447794182184157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94330343045631862788122771 141495514568447794182184157)
          ·
            refine ⟨53060817963167922818319059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141495514568447794182184157 53060817963167922818319059)
            ·
              refine ⟨79591226944751884227478589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53060817963167922818319059 79591226944751884227478589)
              ·
                refine ⟨29846710104281956585304471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79591226944751884227478589 29846710104281956585304471)
                ·
                  refine ⟨44770065156422934877956707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29846710104281956585304471 44770065156422934877956707)
                  ·
                    refine ⟨67155097734634402316935061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44770065156422934877956707 67155097734634402316935061)
                    ·
                      refine ⟨3147895206310987608606331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67155097734634402316935061 3147895206310987608606331)
                      ·
                        rfl

theorem cell23_6130504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_6130504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130504 prefixEnd_6130504 := by exact prefixLift 6130504
  have htrace : WordTrace (prefixWord ++ tailWord_6130504) baseStart_6130504 baseEnd_6130504 := by
    simpa [prefixWord, tailWord_6130504, baseEnd_6130504] using wordTrace_append hprefix tailTrace_6130504
  have hstable : (prefixWord ++ tailWord_6130504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130504).length < 2 ^ (prefixWord ++ tailWord_6130504).sum := by decide
  have hdescent : baseEnd_6130504 < baseStart_6130504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130508 : List Nat := [2, 2, 1, 3, 3, 1, 3, 2, 1, 1, 4]
def baseStart_6130508 : Nat := 118140960795 + 6130508 * 2 ^ 59
def prefixEnd_6130508 : Nat := 4983230072969 + 3 ^ 40 * 6130508 * 2
def baseEnd_6130508 : Nat := 3147897260233605592956313

theorem tailTrace_6130508 : CollatzResearch.WordTrace tailWord_6130508 prefixEnd_6130508 3147897260233605592956313 := by
  unfold tailWord_6130508
  simp only [CollatzResearch.WordTrace]
  refine ⟨111798998037111999127496089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149065330716149332169994785 111798998037111999127496089)
  ·
    refine ⟨83849248527833999345622067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111798998037111999127496089 83849248527833999345622067)
    ·
      refine ⟨125773872791750999018433101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83849248527833999345622067 125773872791750999018433101)
      ·
        refine ⟨47165202296906624631912413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125773872791750999018433101 47165202296906624631912413)
        ·
          refine ⟨17686950861339984236967155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47165202296906624631912413 17686950861339984236967155)
          ·
            refine ⟨26530426292009976355450733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17686950861339984236967155 26530426292009976355450733)
            ·
              refine ⟨9948909859503741133294025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26530426292009976355450733 9948909859503741133294025)
              ·
                refine ⟨7461682394627805849970519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9948909859503741133294025 7461682394627805849970519)
                ·
                  refine ⟨11192523591941708774955779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7461682394627805849970519 11192523591941708774955779)
                  ·
                    refine ⟨16788785387912563162433669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11192523591941708774955779 16788785387912563162433669)
                    ·
                      refine ⟨3147897260233605592956313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16788785387912563162433669 3147897260233605592956313)
                      ·
                        rfl

theorem cell23_6130508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_6130508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130508 prefixEnd_6130508 := by exact prefixLift 6130508
  have htrace : WordTrace (prefixWord ++ tailWord_6130508) baseStart_6130508 baseEnd_6130508 := by
    simpa [prefixWord, tailWord_6130508, baseEnd_6130508] using wordTrace_append hprefix tailTrace_6130508
  have hstable : (prefixWord ++ tailWord_6130508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130508).length < 2 ^ (prefixWord ++ tailWord_6130508).sum := by decide
  have hdescent : baseEnd_6130508 < baseStart_6130508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130514 : List Nat := [3, 2, 2, 1, 1, 2, 1, 11]
def baseStart_6130514 : Nat := 118140960795 + 6130514 * 2 ^ 59
def prefixEnd_6130514 : Nat := 4983230072969 + 3 ^ 40 * 6130514 * 2
def baseEnd_6130514 : Nat := 116588901522871576647455

theorem tailTrace_6130514 : CollatzResearch.WordTrace tailWord_6130514 prefixEnd_6130514 116588901522871576647455 := by
  unfold tailWord_6130514
  simp only [CollatzResearch.WordTrace]
  refine ⟨55899553728050565319927649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149065476608134840853140397 55899553728050565319927649)
  ·
    refine ⟨41924665296037923989945737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55899553728050565319927649 41924665296037923989945737)
    ·
      refine ⟨31443498972028442992459303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41924665296037923989945737 31443498972028442992459303)
      ·
        refine ⟨47165248458042664488688955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31443498972028442992459303 47165248458042664488688955)
        ·
          refine ⟨70747872687063996733033433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47165248458042664488688955 70747872687063996733033433)
          ·
            refine ⟨53060904515297997549775075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70747872687063996733033433 53060904515297997549775075)
            ·
              refine ⟨79591356772946996324662613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53060904515297997549775075 79591356772946996324662613)
              ·
                refine ⟨116588901522871576647455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 79591356772946996324662613 116588901522871576647455)
                ·
                  rfl

theorem cell23_6130514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 11].length) (baseStart_6130514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130514 prefixEnd_6130514 := by exact prefixLift 6130514
  have htrace : WordTrace (prefixWord ++ tailWord_6130514) baseStart_6130514 baseEnd_6130514 := by
    simpa [prefixWord, tailWord_6130514, baseEnd_6130514] using wordTrace_append hprefix tailTrace_6130514
  have hstable : (prefixWord ++ tailWord_6130514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130514).length < 2 ^ (prefixWord ++ tailWord_6130514).sum := by decide
  have hdescent : baseEnd_6130514 < baseStart_6130514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130521 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 1, 2, 4]
def baseStart_6130521 : Nat := 118140960795 + 6130521 * 2 ^ 59
def prefixEnd_6130521 : Nat := 4983230072969 + 3 ^ 40 * 6130521 * 2
def baseEnd_6130521 : Nat := 3147903935482114042093753

theorem tailTrace_6130521 : CollatzResearch.WordTrace tailWord_6130521 prefixEnd_6130521 3147903935482114042093753 := by
  unfold tailWord_6130521
  simp only [CollatzResearch.WordTrace]
  refine ⟨223598470223176901475215417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149065646815451267650143611 223598470223176901475215417)
  ·
    refine ⟨167698852667382676106411563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223598470223176901475215417 167698852667382676106411563)
    ·
      refine ⟨251548279001074014159617345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167698852667382676106411563 251548279001074014159617345)
      ·
        refine ⟨188661209250805510619713009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251548279001074014159617345 188661209250805510619713009)
        ·
          refine ⟨141495906938104132964784757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188661209250805510619713009 141495906938104132964784757)
          ·
            refine ⟨13265241275447262465448571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141495906938104132964784757 13265241275447262465448571)
            ·
              refine ⟨19897861913170893698172857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13265241275447262465448571 19897861913170893698172857)
              ·
                refine ⟨14923396434878170273629643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19897861913170893698172857 14923396434878170273629643)
                ·
                  refine ⟨22385094652317255410444465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14923396434878170273629643 22385094652317255410444465)
                  ·
                    refine ⟨16788820989237941557833349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22385094652317255410444465 16788820989237941557833349)
                    ·
                      refine ⟨3147903935482114042093753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16788820989237941557833349 3147903935482114042093753)
                      ·
                        rfl

theorem cell23_6130521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_6130521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130521 prefixEnd_6130521 := by exact prefixLift 6130521
  have htrace : WordTrace (prefixWord ++ tailWord_6130521) baseStart_6130521 baseEnd_6130521 := by
    simpa [prefixWord, tailWord_6130521, baseEnd_6130521] using wordTrace_append hprefix tailTrace_6130521
  have hstable : (prefixWord ++ tailWord_6130521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130521).length < 2 ^ (prefixWord ++ tailWord_6130521).sum := by decide
  have hdescent : baseEnd_6130521 < baseStart_6130521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130541 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_6130541 : Nat := 118140960795 + 6130541 * 2 ^ 59
def prefixEnd_6130541 : Nat := 4983230072969 + 3 ^ 40 * 6130541 * 2
def baseEnd_6130541 : Nat := 3147914205095203963843661

theorem tailTrace_6130541 : CollatzResearch.WordTrace tailWord_6130541 prefixEnd_6130541 3147914205095203963843661 := by
  unfold tailWord_6130541
  simp only [CollatzResearch.WordTrace]
  refine ⟨223599199683104444890943477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149066133122069629927295651 223599199683104444890943477)
  ·
    refine ⟨20962424970291041708525951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223599199683104444890943477 20962424970291041708525951)
    ·
      refine ⟨31443637455436562562788927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20962424970291041708525951 31443637455436562562788927)
      ·
        refine ⟨47165456183154843844183391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31443637455436562562788927 47165456183154843844183391)
        ·
          refine ⟨70748184274732265766275087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47165456183154843844183391 70748184274732265766275087)
          ·
            refine ⟨106122276412098398649412631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70748184274732265766275087 106122276412098398649412631)
            ·
              refine ⟨159183414618147597974118947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106122276412098398649412631 159183414618147597974118947)
              ·
                refine ⟨238775121927221396961178421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159183414618147597974118947 238775121927221396961178421)
                ·
                  refine ⟨22385167680677005965110477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 238775121927221396961178421 22385167680677005965110477)
                  ·
                    refine ⟨8394437880253877236916429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22385167680677005965110477 8394437880253877236916429)
                    ·
                      refine ⟨3147914205095203963843661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8394437880253877236916429 3147914205095203963843661)
                      ·
                        rfl

theorem cell23_6130541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_6130541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130541 prefixEnd_6130541 := by exact prefixLift 6130541
  have htrace : WordTrace (prefixWord ++ tailWord_6130541) baseStart_6130541 baseEnd_6130541 := by
    simpa [prefixWord, tailWord_6130541, baseEnd_6130541] using wordTrace_append hprefix tailTrace_6130541
  have hstable : (prefixWord ++ tailWord_6130541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130541).length < 2 ^ (prefixWord ++ tailWord_6130541).sum := by decide
  have hdescent : baseEnd_6130541 < baseStart_6130541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130544 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 2, 7]
def baseStart_6130544 : Nat := 118140960795 + 6130544 * 2 ^ 59
def prefixEnd_6130544 : Nat := 4983230072969 + 3 ^ 40 * 6130544 * 2
def baseEnd_6130544 : Nat := 1049305248512389150702049

theorem tailTrace_6130544 : CollatzResearch.WordTrace tailWord_6130544 prefixEnd_6130544 1049305248512389150702049 := by
  unfold tailWord_6130544
  simp only [CollatzResearch.WordTrace]
  refine ⟨111799654551046788201651343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149066206068062384268868457 111799654551046788201651343)
  ·
    refine ⟨167699481826570182302477015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111799654551046788201651343 167699481826570182302477015)
    ·
      refine ⟨251549222739855273453715523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167699481826570182302477015 251549222739855273453715523)
      ·
        refine ⟨377323834109782910180573285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251549222739855273453715523 377323834109782910180573285)
        ·
          refine ⟨70748218895584295658857491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 377323834109782910180573285 70748218895584295658857491)
          ·
            refine ⟨106122328343376443488286237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70748218895584295658857491 106122328343376443488286237)
            ·
              refine ⟨39795873128766166308107339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106122328343376443488286237 39795873128766166308107339)
              ·
                refine ⟨59693809693149249462161009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39795873128766166308107339 59693809693149249462161009)
                ·
                  refine ⟨44770357269861937096620757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59693809693149249462161009 44770357269861937096620757)
                  ·
                    refine ⟨1049305248512389150702049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44770357269861937096620757 1049305248512389150702049)
                    ·
                      rfl

theorem cell23_6130544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 2, 7].length) (baseStart_6130544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130544 prefixEnd_6130544 := by exact prefixLift 6130544
  have htrace : WordTrace (prefixWord ++ tailWord_6130544) baseStart_6130544 baseEnd_6130544 := by
    simpa [prefixWord, tailWord_6130544, baseEnd_6130544] using wordTrace_append hprefix tailTrace_6130544
  have hstable : (prefixWord ++ tailWord_6130544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130544).length < 2 ^ (prefixWord ++ tailWord_6130544).sum := by decide
  have hdescent : baseEnd_6130544 < baseStart_6130544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130554 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5]
def baseStart_6130554 : Nat := 118140960795 + 6130554 * 2 ^ 59
def prefixEnd_6130554 : Nat := 4983230072969 + 3 ^ 40 * 6130554 * 2
def baseEnd_6130554 : Nat := 3147920880343712412981101

theorem tailTrace_6130554 : CollatzResearch.WordTrace tailWord_6130554 prefixEnd_6130554 3147920880343712412981101 := by
  unfold tailWord_6130554
  simp only [CollatzResearch.WordTrace]
  refine ⟨55899918458014337027791679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149066449221371565407444477 55899918458014337027791679)
  ·
    refine ⟨83849877687021505541687519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55899918458014337027791679 83849877687021505541687519)
    ·
      refine ⟨125774816530532258312531279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83849877687021505541687519 125774816530532258312531279)
      ·
        refine ⟨188662224795798387468796919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125774816530532258312531279 188662224795798387468796919)
        ·
          refine ⟨282993337193697581203195379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188662224795798387468796919 282993337193697581203195379)
          ·
            refine ⟨424490005790546371804793069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282993337193697581203195379 424490005790546371804793069)
            ·
              refine ⟨159183752171454889426797401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 424490005790546371804793069 159183752171454889426797401)
              ·
                refine ⟨119387814128591167070098051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159183752171454889426797401 119387814128591167070098051)
                ·
                  refine ⟨179081721192886750605147077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119387814128591167070098051 179081721192886750605147077)
                  ·
                    refine ⟨33577822723666265738465077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 179081721192886750605147077 33577822723666265738465077)
                    ·
                      refine ⟨3147920880343712412981101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33577822723666265738465077 3147920880343712412981101)
                      ·
                        rfl

theorem cell23_6130554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_6130554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130554 prefixEnd_6130554 := by exact prefixLift 6130554
  have htrace : WordTrace (prefixWord ++ tailWord_6130554) baseStart_6130554 baseEnd_6130554 := by
    simpa [prefixWord, tailWord_6130554, baseEnd_6130554] using wordTrace_append hprefix tailTrace_6130554
  have hstable : (prefixWord ++ tailWord_6130554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130554).length < 2 ^ (prefixWord ++ tailWord_6130554).sum := by decide
  have hdescent : baseEnd_6130554 < baseStart_6130554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130591 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 2, 6]
def baseStart_6130591 : Nat := 118140960795 + 6130591 * 2 ^ 59
def prefixEnd_6130591 : Nat := 4983230072969 + 3 ^ 40 * 6130591 * 2
def baseEnd_6130591 : Nat := 1049313293042642922739477

theorem tailTrace_6130591 : CollatzResearch.WordTrace tailWord_6130591 prefixEnd_6130591 1049313293042642922739477 := by
  unfold tailWord_6130591
  simp only [CollatzResearch.WordTrace]
  refine ⟨223601023332923303430263627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149067348888615535620175751 223601023332923303430263627)
  ·
    refine ⟨335401534999384955145395441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223601023332923303430263627 335401534999384955145395441)
    ·
      refine ⟨251551151249538716359046581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335401534999384955145395441 251551151249538716359046581)
      ·
        refine ⟨23582920429644254658660617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 251551151249538716359046581 23582920429644254658660617)
        ·
          refine ⟨17687190322233190993995463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23582920429644254658660617 17687190322233190993995463)
          ·
            refine ⟨26530785483349786490993195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17687190322233190993995463 26530785483349786490993195)
            ·
              refine ⟨39796178225024679736489793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26530785483349786490993195 39796178225024679736489793)
              ·
                refine ⟨29847133668768509802367345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39796178225024679736489793 29847133668768509802367345)
                ·
                  refine ⟨22385350251576382351775509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29847133668768509802367345 22385350251576382351775509)
                  ·
                    refine ⟨1049313293042642922739477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22385350251576382351775509 1049313293042642922739477)
                    ·
                      rfl

theorem cell23_6130591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 6].length) (baseStart_6130591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130591 prefixEnd_6130591 := by exact prefixLift 6130591
  have htrace : WordTrace (prefixWord ++ tailWord_6130591) baseStart_6130591 baseEnd_6130591 := by
    simpa [prefixWord, tailWord_6130591, baseEnd_6130591] using wordTrace_append hprefix tailTrace_6130591
  have hstable : (prefixWord ++ tailWord_6130591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130591).length < 2 ^ (prefixWord ++ tailWord_6130591).sum := by decide
  have hdescent : baseEnd_6130591 < baseStart_6130591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130604 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 11]
def baseStart_6130604 : Nat := 118140960795 + 6130604 * 2 ^ 59
def prefixEnd_6130604 : Nat := 4983230072969 + 3 ^ 40 * 6130604 * 2
def baseEnd_6130604 : Nat := 349771839375159690817319

theorem tailTrace_6130604 : CollatzResearch.WordTrace tailWord_6130604 prefixEnd_6130604 349771839375159690817319 := by
  unfold tailWord_6130604
  simp only [CollatzResearch.WordTrace]
  refine ⟨111800748740938103325243433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149067664987917471100324577 111800748740938103325243433)
  ·
    refine ⟨83850561555703577493932575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111800748740938103325243433 83850561555703577493932575)
    ·
      refine ⟨125775842333555366240898863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83850561555703577493932575 125775842333555366240898863)
      ·
        refine ⟨188663763500333049361348295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125775842333555366240898863 188663763500333049361348295)
        ·
          refine ⟨282995645250499574042022443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188663763500333049361348295 282995645250499574042022443)
          ·
            refine ⟨424493467875749361063033665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282995645250499574042022443 424493467875749361063033665)
            ·
              refine ⟨318370100906812020797275249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424493467875749361063033665 318370100906812020797275249)
              ·
                refine ⟨238777575680109015597956437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318370100906812020797275249 238777575680109015597956437)
                ·
                  refine ⟨349771839375159690817319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 238777575680109015597956437 349771839375159690817319)
                  ·
                    rfl

theorem cell23_6130604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 11].length) (baseStart_6130604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130604 prefixEnd_6130604 := by exact prefixLift 6130604
  have htrace : WordTrace (prefixWord ++ tailWord_6130604) baseStart_6130604 baseEnd_6130604 := by
    simpa [prefixWord, tailWord_6130604, baseEnd_6130604] using wordTrace_append hprefix tailTrace_6130604
  have hstable : (prefixWord ++ tailWord_6130604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130604).length < 2 ^ (prefixWord ++ tailWord_6130604).sum := by decide
  have hdescent : baseEnd_6130604 < baseStart_6130604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130615 : List Nat := [1, 1, 3, 1, 3, 1, 2, 5, 2, 2, 2]
def baseStart_6130615 : Nat := 118140960795 + 6130615 * 2 ^ 59
def prefixEnd_6130615 : Nat := 4983230072969 + 3 ^ 40 * 6130615 * 2
def baseEnd_6130615 : Nat := 3147952202663636674318321

theorem tailTrace_6130615 : CollatzResearch.WordTrace tailWord_6130615 prefixEnd_6130615 3147952202663636674318321 := by
  unfold tailWord_6130615
  simp only [CollatzResearch.WordTrace]
  refine ⟨223601898684836355529137299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149067932456557570352758199 223601898684836355529137299)
  ·
    refine ⟨335402848027254533293705949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223601898684836355529137299 335402848027254533293705949)
    ·
      refine ⟨125776068010220449985139731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335402848027254533293705949 125776068010220449985139731)
      ·
        refine ⟨188664102015330674977709597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125776068010220449985139731 188664102015330674977709597)
        ·
          refine ⟨70749038255749003116641099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188664102015330674977709597 70749038255749003116641099)
          ·
            refine ⟨106123557383623504674961649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70749038255749003116641099 106123557383623504674961649)
            ·
              refine ⟨79592668037717628506221237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106123557383623504674961649 79592668037717628506221237)
              ·
                refine ⟨7461812628536027672458241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79592668037717628506221237 7461812628536027672458241)
                ·
                  refine ⟨5596359471402020754343681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7461812628536027672458241 5596359471402020754343681)
                  ·
                    refine ⟨4197269603551515565757761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5596359471402020754343681 4197269603551515565757761)
                    ·
                      refine ⟨3147952202663636674318321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4197269603551515565757761 3147952202663636674318321)
                      ·
                        rfl

theorem cell23_6130615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 2, 2].length) (baseStart_6130615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130615 prefixEnd_6130615 := by exact prefixLift 6130615
  have htrace : WordTrace (prefixWord ++ tailWord_6130615) baseStart_6130615 baseEnd_6130615 := by
    simpa [prefixWord, tailWord_6130615, baseEnd_6130615] using wordTrace_append hprefix tailTrace_6130615
  have hstable : (prefixWord ++ tailWord_6130615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130615).length < 2 ^ (prefixWord ++ tailWord_6130615).sum := by decide
  have hdescent : baseEnd_6130615 < baseStart_6130615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130631 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 3]
def baseStart_6130631 : Nat := 118140960795 + 6130631 * 2 ^ 59
def prefixEnd_6130631 : Nat := 4983230072969 + 3 ^ 40 * 6130631 * 2
def baseEnd_6130631 : Nat := 3147960418354108611718247

theorem tailTrace_6130631 : CollatzResearch.WordTrace tailWord_6130631 prefixEnd_6130631 3147960418354108611718247 := by
  unfold tailWord_6130631
  simp only [CollatzResearch.WordTrace]
  refine ⟨223602482252778390261719747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149068321501852260174479831 223602482252778390261719747)
  ·
    refine ⟨335403723379167585392579621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223602482252778390261719747 335403723379167585392579621)
    ·
      refine ⟨62888198133593922261108679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335403723379167585392579621 62888198133593922261108679)
      ·
        refine ⟨94332297200390883391663019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62888198133593922261108679 94332297200390883391663019)
        ·
          refine ⟨141498445800586325087494529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94332297200390883391663019 141498445800586325087494529)
          ·
            refine ⟨106123834350439743815620897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141498445800586325087494529 106123834350439743815620897)
            ·
              refine ⟨79592875762829807861715673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106123834350439743815620897 79592875762829807861715673)
              ·
                refine ⟨59694656822122355896286755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79592875762829807861715673 59694656822122355896286755)
                ·
                  refine ⟨89541985233183533844430133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59694656822122355896286755 89541985233183533844430133)
                  ·
                    refine ⟨8394561115610956297915325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89541985233183533844430133 8394561115610956297915325)
                    ·
                      refine ⟨3147960418354108611718247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8394561115610956297915325 3147960418354108611718247)
                      ·
                        rfl

theorem cell23_6130631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_6130631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130631 prefixEnd_6130631 := by exact prefixLift 6130631
  have htrace : WordTrace (prefixWord ++ tailWord_6130631) baseStart_6130631 baseEnd_6130631 := by
    simpa [prefixWord, tailWord_6130631, baseEnd_6130631] using wordTrace_append hprefix tailTrace_6130631
  have hstable : (prefixWord ++ tailWord_6130631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130631).length < 2 ^ (prefixWord ++ tailWord_6130631).sum := by decide
  have hdescent : baseEnd_6130631 < baseStart_6130631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130655 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 7]
def baseStart_6130655 : Nat := 118140960795 + 6130655 * 2 ^ 59
def prefixEnd_6130655 : Nat := 4983230072969 + 3 ^ 40 * 6130655 * 2
def baseEnd_6130655 : Nat := 349774749098868501979793

theorem tailTrace_6130655 : CollatzResearch.WordTrace tailWord_6130655 prefixEnd_6130655 349774749098868501979793 := by
  unfold tailWord_6130655
  simp only [CollatzResearch.WordTrace]
  refine ⟨223603357604691442360593419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149068905069794294907062279 223603357604691442360593419)
  ·
    refine ⟨335405036407037163540890129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223603357604691442360593419 335405036407037163540890129)
    ·
      refine ⟨251553777305277872655667597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335405036407037163540890129 251553777305277872655667597)
      ·
        refine ⟨94332666489479202245875349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251553777305277872655667597 94332666489479202245875349)
        ·
          refine ⟨4421843741694337605275407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94332666489479202245875349 4421843741694337605275407)
          ·
            refine ⟨6632765612541506407913111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4421843741694337605275407 6632765612541506407913111)
            ·
              refine ⟨9949148418812259611869667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6632765612541506407913111 9949148418812259611869667)
              ·
                refine ⟨14923722628218389417804501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9949148418812259611869667 14923722628218389417804501)
                ·
                  refine ⟨349774749098868501979793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14923722628218389417804501 349774749098868501979793)
                  ·
                    rfl

theorem cell23_6130655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 7].length) (baseStart_6130655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130655 prefixEnd_6130655 := by exact prefixLift 6130655
  have htrace : WordTrace (prefixWord ++ tailWord_6130655) baseStart_6130655 baseEnd_6130655 := by
    simpa [prefixWord, tailWord_6130655, baseEnd_6130655] using wordTrace_append hprefix tailTrace_6130655
  have hstable : (prefixWord ++ tailWord_6130655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130655).length < 2 ^ (prefixWord ++ tailWord_6130655).sum := by decide
  have hdescent : baseEnd_6130655 < baseStart_6130655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130742 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_6130742 : Nat := 118140960795 + 6130742 * 2 ^ 59
def prefixEnd_6130742 : Nat := 4983230072969 + 3 ^ 40 * 6130742 * 2
def baseEnd_6130742 : Nat := 3148017414706757677430237

theorem tailTrace_6130742 : CollatzResearch.WordTrace tailWord_6130742 prefixEnd_6130742 3148017414706757677430237 := by
  unfold tailWord_6130742
  simp only [CollatzResearch.WordTrace]
  refine ⟨13975408172211016013688155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149071020503584170812673653 13975408172211016013688155)
  ·
    refine ⟨20963112258316524020532233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13975408172211016013688155 20963112258316524020532233)
    ·
      refine ⟨15722334193737393015399175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20963112258316524020532233 15722334193737393015399175)
      ·
        refine ⟨23583501290606089523098763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15722334193737393015399175 23583501290606089523098763)
        ·
          refine ⟨35375251935909134284648145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23583501290606089523098763 35375251935909134284648145)
          ·
            refine ⟨26531438951931850713486109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35375251935909134284648145 26531438951931850713486109)
            ·
              refine ⟨9949289606974444017557291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26531438951931850713486109 9949289606974444017557291)
              ·
                refine ⟨14923934410461666026335937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9949289606974444017557291 14923934410461666026335937)
                ·
                  refine ⟨11192950807846249519751953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14923934410461666026335937 11192950807846249519751953)
                  ·
                    refine ⟨8394713105884687139813965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11192950807846249519751953 8394713105884687139813965)
                    ·
                      refine ⟨3148017414706757677430237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8394713105884687139813965 3148017414706757677430237)
                      ·
                        rfl

theorem cell23_6130742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_6130742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130742 prefixEnd_6130742 := by exact prefixLift 6130742
  have htrace : WordTrace (prefixWord ++ tailWord_6130742) baseStart_6130742 baseEnd_6130742 := by
    simpa [prefixWord, tailWord_6130742, baseEnd_6130742] using wordTrace_append hprefix tailTrace_6130742
  have hstable : (prefixWord ++ tailWord_6130742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130742).length < 2 ^ (prefixWord ++ tailWord_6130742).sum := by decide
  have hdescent : baseEnd_6130742 < baseStart_6130742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130751 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 5]
def baseStart_6130751 : Nat := 118140960795 + 6130751 * 2 ^ 59
def prefixEnd_6130751 : Nat := 4983230072969 + 3 ^ 40 * 6130751 * 2
def baseEnd_6130751 : Nat := 3148022036032648142217695

theorem tailTrace_6130751 : CollatzResearch.WordTrace tailWord_6130751 prefixEnd_6130751 3148022036032648142217695 := by
  unfold tailWord_6130751
  simp only [CollatzResearch.WordTrace]
  refine ⟨223606859012343650756088107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149071239341562433837392071 223606859012343650756088107)
  ·
    refine ⟨335410288518515476134132161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223606859012343650756088107 335410288518515476134132161)
    ·
      refine ⟨251557716388886607100599121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335410288518515476134132161 251557716388886607100599121)
      ·
        refine ⟨188668287291664955325449341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251557716388886607100599121 188668287291664955325449341)
        ·
          refine ⟨70750607734374358247043503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188668287291664955325449341 70750607734374358247043503)
          ·
            refine ⟨106125911601561537370565255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70750607734374358247043503 106125911601561537370565255)
            ·
              refine ⟨159188867402342306055847883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106125911601561537370565255 159188867402342306055847883)
              ·
                refine ⟨238783301103513459083771825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159188867402342306055847883 238783301103513459083771825)
                ·
                  refine ⟨179087475827635094312828869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238783301103513459083771825 179087475827635094312828869)
                  ·
                    refine ⟨33578901717681580183655413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 179087475827635094312828869 33578901717681580183655413)
                    ·
                      refine ⟨3148022036032648142217695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33578901717681580183655413 3148022036032648142217695)
                      ·
                        rfl

theorem cell23_6130751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_6130751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130751 prefixEnd_6130751 := by exact prefixLift 6130751
  have htrace : WordTrace (prefixWord ++ tailWord_6130751) baseStart_6130751 baseEnd_6130751 := by
    simpa [prefixWord, tailWord_6130751, baseEnd_6130751] using wordTrace_append hprefix tailTrace_6130751
  have hstable : (prefixWord ++ tailWord_6130751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130751).length < 2 ^ (prefixWord ++ tailWord_6130751).sum := by decide
  have hdescent : baseEnd_6130751 < baseStart_6130751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130771 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 5, 6]
def baseStart_6130771 : Nat := 118140960795 + 6130771 * 2 ^ 59
def prefixEnd_6130771 : Nat := 4983230072969 + 3 ^ 40 * 6130771 * 2
def baseEnd_6130771 : Nat := 1049344101881912687989201

theorem tailTrace_6130771 : CollatzResearch.WordTrace tailWord_6130771 prefixEnd_6130771 1049344101881912687989201 := by
  unfold tailWord_6130771
  simp only [CollatzResearch.WordTrace]
  refine ⟨223607588472271194171816167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149071725648180796114544111 223607588472271194171816167)
  ·
    refine ⟨335411382708406791257724251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223607588472271194171816167 335411382708406791257724251)
    ·
      refine ⟨503117074062610186886586377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335411382708406791257724251 503117074062610186886586377)
      ·
        refine ⟨377337805546957640164939783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503117074062610186886586377 377337805546957640164939783)
        ·
          refine ⟨566006708320436460247409675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377337805546957640164939783 566006708320436460247409675)
          ·
            refine ⟨849010062480654690371114513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566006708320436460247409675 849010062480654690371114513)
            ·
              refine ⟨636757546860491017778335885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849010062480654690371114513 636757546860491017778335885)
              ·
                refine ⟨238784080072684131666875957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 636757546860491017778335885 238784080072684131666875957)
                ·
                  refine ⟨22386007506814137343769621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 238784080072684131666875957 22386007506814137343769621)
                  ·
                    refine ⟨1049344101881912687989201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22386007506814137343769621 1049344101881912687989201)
                    ·
                      rfl

theorem cell23_6130771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 6].length) (baseStart_6130771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130771 prefixEnd_6130771 := by exact prefixLift 6130771
  have htrace : WordTrace (prefixWord ++ tailWord_6130771) baseStart_6130771 baseEnd_6130771 := by
    simpa [prefixWord, tailWord_6130771, baseEnd_6130771] using wordTrace_append hprefix tailTrace_6130771
  have hstable : (prefixWord ++ tailWord_6130771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130771).length < 2 ^ (prefixWord ++ tailWord_6130771).sum := by decide
  have hdescent : baseEnd_6130771 < baseStart_6130771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130778 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4]
def baseStart_6130778 : Nat := 118140960795 + 6130778 * 2 ^ 59
def prefixEnd_6130778 : Nat := 4983230072969 + 3 ^ 40 * 6130778 * 2
def baseEnd_6130778 : Nat := 3148035900010319536580071

theorem tailTrace_6130778 : CollatzResearch.WordTrace tailWord_6130778 prefixEnd_6130778 3148035900010319536580071 := by
  unfold tailWord_6130778
  simp only [CollatzResearch.WordTrace]
  refine ⟨55901960945811458591830247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149071895855497222911547325 55901960945811458591830247)
  ·
    refine ⟨83852941418717187887745371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55901960945811458591830247 83852941418717187887745371)
    ·
      refine ⟨125779412128075781831618057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83852941418717187887745371 125779412128075781831618057)
      ·
        refine ⟨94334559096056836373713543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125779412128075781831618057 94334559096056836373713543)
        ·
          refine ⟨141501838644085254560570315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94334559096056836373713543 141501838644085254560570315)
          ·
            refine ⟨212252757966127881840855473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141501838644085254560570315 212252757966127881840855473)
            ·
              refine ⟨159189568474595911380641605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212252757966127881840855473 159189568474595911380641605)
              ·
                refine ⟨29848044088986733383870301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159189568474595911380641605 29848044088986733383870301)
                ·
                  refine ⟨11193016533370025018951363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29848044088986733383870301 11193016533370025018951363)
                  ·
                    refine ⟨16789524800055037528427045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11193016533370025018951363 16789524800055037528427045)
                    ·
                      refine ⟨3148035900010319536580071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16789524800055037528427045 3148035900010319536580071)
                      ·
                        rfl

theorem cell23_6130778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_6130778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130778 prefixEnd_6130778 := by exact prefixLift 6130778
  have htrace : WordTrace (prefixWord ++ tailWord_6130778) baseStart_6130778 baseEnd_6130778 := by
    simpa [prefixWord, tailWord_6130778, baseEnd_6130778] using wordTrace_append hprefix tailTrace_6130778
  have hstable : (prefixWord ++ tailWord_6130778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130778).length < 2 ^ (prefixWord ++ tailWord_6130778).sum := by decide
  have hdescent : baseEnd_6130778 < baseStart_6130778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130808 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 1, 2, 4]
def baseStart_6130808 : Nat := 118140960795 + 6130808 * 2 ^ 59
def prefixEnd_6130808 : Nat := 4983230072969 + 3 ^ 40 * 6130808 * 2
def baseEnd_6130808 : Nat := 3148051304429954419204933

theorem tailTrace_6130808 : CollatzResearch.WordTrace tailWord_6130808 prefixEnd_6130808 3148051304429954419204933 := by
  unfold tailWord_6130808
  simp only [CollatzResearch.WordTrace]
  refine ⟨111804468986568574745456539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149072625315424766327275385 111804468986568574745456539)
  ·
    refine ⟨167706703479852862118184809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111804468986568574745456539 167706703479852862118184809)
    ·
      refine ⟨125780027609889646588638607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167706703479852862118184809 125780027609889646588638607)
      ·
        refine ⟨188670041414834469882957911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125780027609889646588638607 188670041414834469882957911)
        ·
          refine ⟨283005062122251704824436867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188670041414834469882957911 283005062122251704824436867)
          ·
            refine ⟨424507593183377557236655301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283005062122251704824436867 424507593183377557236655301)
            ·
              refine ⟨79595173721883291981872869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 424507593183377557236655301 79595173721883291981872869)
              ·
                refine ⟨14924095072853117246601163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79595173721883291981872869 14924095072853117246601163)
                ·
                  refine ⟨22386142609279675869901745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14924095072853117246601163 22386142609279675869901745)
                  ·
                    refine ⟨16789606956959756902426309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22386142609279675869901745 16789606956959756902426309)
                    ·
                      refine ⟨3148051304429954419204933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16789606956959756902426309 3148051304429954419204933)
                      ·
                        rfl

theorem cell23_6130808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_6130808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130808 prefixEnd_6130808 := by exact prefixLift 6130808
  have htrace : WordTrace (prefixWord ++ tailWord_6130808) baseStart_6130808 baseEnd_6130808 := by
    simpa [prefixWord, tailWord_6130808, baseEnd_6130808] using wordTrace_append hprefix tailTrace_6130808
  have hstable : (prefixWord ++ tailWord_6130808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130808).length < 2 ^ (prefixWord ++ tailWord_6130808).sum := by decide
  have hdescent : baseEnd_6130808 < baseStart_6130808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130839 : List Nat := [1, 1, 3, 3, 3, 3, 2, 1, 2, 4]
def baseStart_6130839 : Nat := 118140960795 + 6130839 * 2 ^ 59
def prefixEnd_6130839 : Nat := 4983230072969 + 3 ^ 40 * 6130839 * 2
def baseEnd_6130839 : Nat := 1049355740776747932639097

theorem tailTrace_6130839 : CollatzResearch.WordTrace tailWord_6130839 prefixEnd_6130839 1049355740776747932639097 := by
  unfold tailWord_6130839
  simp only [CollatzResearch.WordTrace]
  refine ⟨223610068636024841785291571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149073379090683227856861047 223610068636024841785291571)
  ·
    refine ⟨335415102954037262677937357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223610068636024841785291571 335415102954037262677937357)
    ·
      refine ⟨125780663607763973504226509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335415102954037262677937357 125780663607763973504226509)
      ·
        refine ⟨47167748852911490064084941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125780663607763973504226509 47167748852911490064084941)
        ·
          refine ⟨17687905819841808774031853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47167748852911490064084941 17687905819841808774031853)
          ·
            refine ⟨6632964682440678290261945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17687905819841808774031853 6632964682440678290261945)
            ·
              refine ⟨4974723511830508717696459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6632964682440678290261945 4974723511830508717696459)
              ·
                refine ⟨7462085267745763076544689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4974723511830508717696459 7462085267745763076544689)
                ·
                  refine ⟨5596563950809322307408517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7462085267745763076544689 5596563950809322307408517)
                  ·
                    refine ⟨1049355740776747932639097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5596563950809322307408517 1049355740776747932639097)
                    ·
                      rfl

theorem cell23_6130839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_6130839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130839 prefixEnd_6130839 := by exact prefixLift 6130839
  have htrace : WordTrace (prefixWord ++ tailWord_6130839) baseStart_6130839 baseEnd_6130839 := by
    simpa [prefixWord, tailWord_6130839, baseEnd_6130839] using wordTrace_append hprefix tailTrace_6130839
  have hstable : (prefixWord ++ tailWord_6130839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130839).length < 2 ^ (prefixWord ++ tailWord_6130839).sum := by decide
  have hdescent : baseEnd_6130839 < baseStart_6130839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130845 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_6130845 : Nat := 118140960795 + 6130845 * 2 ^ 59
def prefixEnd_6130845 : Nat := 4983230072969 + 3 ^ 40 * 6130845 * 2
def baseEnd_6130845 : Nat := 3148070303214170774442263

theorem tailTrace_6130845 : CollatzResearch.WordTrace tailWord_6130845 prefixEnd_6130845 3148070303214170774442263 := by
  unfold tailWord_6130845
  simp only [CollatzResearch.WordTrace]
  refine ⟨223610287474003104810009989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149073524982668736540006659 223610287474003104810009989)
  ·
    refine ⟨41926928901375582151876873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223610287474003104810009989 41926928901375582151876873)
    ·
      refine ⟨31445196676031686613907655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41926928901375582151876873 31445196676031686613907655)
      ·
        refine ⟨47167795014047529920861483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31445196676031686613907655 47167795014047529920861483)
        ·
          refine ⟨70751692521071294881292225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47167795014047529920861483 70751692521071294881292225)
          ·
            refine ⟨53063769390803471160969169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70751692521071294881292225 53063769390803471160969169)
            ·
              refine ⟨39797827043102603370726877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53063769390803471160969169 39797827043102603370726877)
              ·
                refine ⟨14924185141163476264022579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39797827043102603370726877 14924185141163476264022579)
                ·
                  refine ⟨22386277711745214396033869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14924185141163476264022579 22386277711745214396033869)
                  ·
                    refine ⟨8394854141904455398512701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22386277711745214396033869 8394854141904455398512701)
                    ·
                      refine ⟨3148070303214170774442263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8394854141904455398512701 3148070303214170774442263)
                      ·
                        rfl

theorem cell23_6130845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_6130845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130845 prefixEnd_6130845 := by exact prefixLift 6130845
  have htrace : WordTrace (prefixWord ++ tailWord_6130845) baseStart_6130845 baseEnd_6130845 := by
    simpa [prefixWord, tailWord_6130845, baseEnd_6130845] using wordTrace_append hprefix tailTrace_6130845
  have hstable : (prefixWord ++ tailWord_6130845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130845).length < 2 ^ (prefixWord ++ tailWord_6130845).sum := by decide
  have hdescent : baseEnd_6130845 < baseStart_6130845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130880 : List Nat := [2, 1, 1, 2, 7, 1, 2, 2, 1, 2, 2]
def baseStart_6130880 : Nat := 118140960795 + 6130880 * 2 ^ 59
def prefixEnd_6130880 : Nat := 4983230072969 + 3 ^ 40 * 6130880 * 2
def baseEnd_6130880 : Nat := 3148088275037078137504603

theorem tailTrace_6130880 : CollatzResearch.WordTrace tailWord_6130880 prefixEnd_6130880 3148088275037078137504603 := by
  unfold tailWord_6130880
  simp only [CollatzResearch.WordTrace]
  refine ⟨111805782014438152893767047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149074376019250870525022729 111805782014438152893767047)
  ·
    refine ⟨167708673021657229340650571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111805782014438152893767047 167708673021657229340650571)
    ·
      refine ⟨251563009532485844010975857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167708673021657229340650571 251563009532485844010975857)
      ·
        refine ⟨188672257149364383008231893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251563009532485844010975857 188672257149364383008231893)
        ·
          refine ⟨4422006026938227726755435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 188672257149364383008231893 4422006026938227726755435)
          ·
            refine ⟨6633009040407341590133153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4422006026938227726755435 6633009040407341590133153)
            ·
              refine ⟨4974756780305506192599865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6633009040407341590133153 4974756780305506192599865)
              ·
                refine ⟨3731067585229129644449899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4974756780305506192599865 3731067585229129644449899)
                ·
                  refine ⟨5596601377843694466674849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3731067585229129644449899 5596601377843694466674849)
                  ·
                    refine ⟨4197451033382770850006137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5596601377843694466674849 4197451033382770850006137)
                    ·
                      refine ⟨3148088275037078137504603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4197451033382770850006137 3148088275037078137504603)
                      ·
                        rfl

theorem cell23_6130880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 1, 2, 2].length) (baseStart_6130880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130880 prefixEnd_6130880 := by exact prefixLift 6130880
  have htrace : WordTrace (prefixWord ++ tailWord_6130880) baseStart_6130880 baseEnd_6130880 := by
    simpa [prefixWord, tailWord_6130880, baseEnd_6130880] using wordTrace_append hprefix tailTrace_6130880
  have hstable : (prefixWord ++ tailWord_6130880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130880).length < 2 ^ (prefixWord ++ tailWord_6130880).sum := by decide
  have hdescent : baseEnd_6130880 < baseStart_6130880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130885 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 5, 4, 2]
def baseStart_6130885 : Nat := 118140960795 + 6130885 * 2 ^ 59
def prefixEnd_6130885 : Nat := 4983230072969 + 3 ^ 40 * 6130885 * 2
def baseEnd_6130885 : Nat := 3148090842440350617942079

theorem tailTrace_6130885 : CollatzResearch.WordTrace tailWord_6130885 prefixEnd_6130885 3148090842440350617942079 := by
  unfold tailWord_6130885
  simp only [CollatzResearch.WordTrace]
  refine ⟨223611746393858191641466109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149074497595905461094310739 223611746393858191641466109)
  ·
    refine ⟨83854404897696821865549791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223611746393858191641466109 83854404897696821865549791)
    ·
      refine ⟨125781607346545232798324687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83854404897696821865549791 125781607346545232798324687)
      ·
        refine ⟨188672411019817849197487031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125781607346545232798324687 188672411019817849197487031)
        ·
          refine ⟨283008616529726773796230547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188672411019817849197487031 283008616529726773796230547)
          ·
            refine ⟨424512924794590160694345821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283008616529726773796230547 424512924794590160694345821)
            ·
              refine ⟨159192346797971310260379683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 424512924794590160694345821 159192346797971310260379683)
              ·
                refine ⟨238788520196956965390569525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159192346797971310260379683 238788520196956965390569525)
                ·
                  refine ⟨22386423768464715505365893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 238788520196956965390569525 22386423768464715505365893)
                  ·
                    refine ⟨4197454456587134157256105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22386423768464715505365893 4197454456587134157256105)
                    ·
                      refine ⟨3148090842440350617942079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4197454456587134157256105 3148090842440350617942079)
                      ·
                        rfl

theorem cell23_6130885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 4, 2].length) (baseStart_6130885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130885 prefixEnd_6130885 := by exact prefixLift 6130885
  have htrace : WordTrace (prefixWord ++ tailWord_6130885) baseStart_6130885 baseEnd_6130885 := by
    simpa [prefixWord, tailWord_6130885, baseEnd_6130885] using wordTrace_append hprefix tailTrace_6130885
  have hstable : (prefixWord ++ tailWord_6130885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130885).length < 2 ^ (prefixWord ++ tailWord_6130885).sum := by decide
  have hdescent : baseEnd_6130885 < baseStart_6130885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130886 : List Nat := [6, 1, 2, 2, 1, 2, 1, 8]
def baseStart_6130886 : Nat := 118140960795 + 6130886 * 2 ^ 59
def prefixEnd_6130886 : Nat := 4983230072969 + 3 ^ 40 * 6130886 * 2
def baseEnd_6130886 : Nat := 116595976145222411630725

theorem tailTrace_6130886 : CollatzResearch.WordTrace tailWord_6130886 prefixEnd_6130886 116595976145222411630725 := by
  unfold tailWord_6130886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6987868214589205275382891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 149074521911236379208168341 6987868214589205275382891)
  ·
    refine ⟨10481802321883807913074337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6987868214589205275382891 10481802321883807913074337)
    ·
      refine ⟨7861351741412855934805753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10481802321883807913074337 7861351741412855934805753)
      ·
        refine ⟨5896013806059641951104315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7861351741412855934805753 5896013806059641951104315)
        ·
          refine ⟨8844020709089462926656473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5896013806059641951104315 8844020709089462926656473)
          ·
            refine ⟨6633015531817097194992355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8844020709089462926656473 6633015531817097194992355)
            ·
              refine ⟨9949523297725645792488533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6633015531817097194992355 9949523297725645792488533)
              ·
                refine ⟨116595976145222411630725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9949523297725645792488533 116595976145222411630725)
                ·
                  rfl

theorem cell23_6130886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_6130886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130886 prefixEnd_6130886 := by exact prefixLift 6130886
  have htrace : WordTrace (prefixWord ++ tailWord_6130886) baseStart_6130886 baseEnd_6130886 := by
    simpa [prefixWord, tailWord_6130886, baseEnd_6130886] using wordTrace_append hprefix tailTrace_6130886
  have hstable : (prefixWord ++ tailWord_6130886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130886).length < 2 ^ (prefixWord ++ tailWord_6130886).sum := by decide
  have hdescent : baseEnd_6130886 < baseStart_6130886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130888 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_6130888 : Nat := 118140960795 + 6130888 * 2 ^ 59
def prefixEnd_6130888 : Nat := 4983230072969 + 3 ^ 40 * 6130888 * 2
def baseEnd_6130888 : Nat := 3148092382882314106204565

theorem tailTrace_6130888 : CollatzResearch.WordTrace tailWord_6130888 prefixEnd_6130888 3148092382882314106204565 := by
  unfold tailWord_6130888
  simp only [CollatzResearch.WordTrace]
  refine ⟨111805927906423661576912659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149074570541898215435883545 111805927906423661576912659)
  ·
    refine ⟨167708891859635492365368989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111805927906423661576912659 167708891859635492365368989)
    ·
      refine ⟨62890834447363309637013371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167708891859635492365368989 62890834447363309637013371)
      ·
        refine ⟨94336251671044964455520057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62890834447363309637013371 94336251671044964455520057)
        ·
          refine ⟨70752188753283723341640043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94336251671044964455520057 70752188753283723341640043)
          ·
            refine ⟨106128283129925585012460065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70752188753283723341640043 106128283129925585012460065)
            ·
              refine ⟨79596212347444188759345049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106128283129925585012460065 79596212347444188759345049)
              ·
                refine ⟨59697159260583141569508787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79596212347444188759345049 59697159260583141569508787)
                ·
                  refine ⟨89545738890874712354263181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59697159260583141569508787 89545738890874712354263181)
                  ·
                    refine ⟨33579652084078017132848693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89545738890874712354263181 33579652084078017132848693)
                    ·
                      refine ⟨3148092382882314106204565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33579652084078017132848693 3148092382882314106204565)
                      ·
                        rfl

theorem cell23_6130888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_6130888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130888 prefixEnd_6130888 := by exact prefixLift 6130888
  have htrace : WordTrace (prefixWord ++ tailWord_6130888) baseStart_6130888 baseEnd_6130888 := by
    simpa [prefixWord, tailWord_6130888, baseEnd_6130888] using wordTrace_append hprefix tailTrace_6130888
  have hstable : (prefixWord ++ tailWord_6130888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130888).length < 2 ^ (prefixWord ++ tailWord_6130888).sum := by decide
  have hdescent : baseEnd_6130888 < baseStart_6130888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130942 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 7]
def baseStart_6130942 : Nat := 118140960795 + 6130942 * 2 ^ 59
def prefixEnd_6130942 : Nat := 4983230072969 + 3 ^ 40 * 6130942 * 2
def baseEnd_6130942 : Nat := 349791123426406321658813

theorem tailTrace_6130942 : CollatzResearch.WordTrace tailWord_6130942 prefixEnd_6130942 349791123426406321658813 := by
  unfold tailWord_6130942
  simp only [CollatzResearch.WordTrace]
  refine ⟨27951728169331461297036385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149075883569767793584194053 27951728169331461297036385)
  ·
    refine ⟨20963796126998595972777289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27951728169331461297036385 20963796126998595972777289)
    ·
      refine ⟨15722847095248946979582967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20963796126998595972777289 15722847095248946979582967)
      ·
        refine ⟨23584270642873420469374451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15722847095248946979582967 23584270642873420469374451)
        ·
          refine ⟨35376405964310130704061677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23584270642873420469374451 35376405964310130704061677)
          ·
            refine ⟨13266152236616299014023129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35376405964310130704061677 13266152236616299014023129)
            ·
              refine ⟨9949614177462224260517347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13266152236616299014023129 9949614177462224260517347)
              ·
                refine ⟨14924421266193336390776021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9949614177462224260517347 14924421266193336390776021)
                ·
                  refine ⟨349791123426406321658813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14924421266193336390776021 349791123426406321658813)
                  ·
                    rfl

theorem cell23_6130942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_6130942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130942 prefixEnd_6130942 := by exact prefixLift 6130942
  have htrace : WordTrace (prefixWord ++ tailWord_6130942) baseStart_6130942 baseEnd_6130942 := by
    simpa [prefixWord, tailWord_6130942, baseEnd_6130942] using wordTrace_append hprefix tailTrace_6130942
  have hstable : (prefixWord ++ tailWord_6130942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130942).length < 2 ^ (prefixWord ++ tailWord_6130942).sum := by decide
  have hdescent : baseEnd_6130942 < baseStart_6130942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130976 : List Nat := [2, 1, 1, 5, 4, 1, 1, 3, 5]
def baseStart_6130976 : Nat := 118140960795 + 6130976 * 2 ^ 59
def prefixEnd_6130976 : Nat := 4983230072969 + 3 ^ 40 * 6130976 * 2
def baseEnd_6130976 : Nat := 349793063242212195767129

theorem tailTrace_6130976 : CollatzResearch.WordTrace tailWord_6130976 prefixEnd_6130976 349793063242212195767129 := by
  unfold tailWord_6130976
  simp only [CollatzResearch.WordTrace]
  refine ⟨111807532718264257091514391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149076710291019009455352521 111807532718264257091514391)
  ·
    refine ⟨167711299077396385637271587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111807532718264257091514391 167711299077396385637271587)
    ·
      refine ⟨251566948616094578455907381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167711299077396385637271587 251566948616094578455907381)
      ·
        refine ⟨23584401432758866730241317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 251566948616094578455907381 23584401432758866730241317)
        ·
          refine ⟨4422075268642287511920247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23584401432758866730241317 4422075268642287511920247)
          ·
            refine ⟨6633112902963431267880371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4422075268642287511920247 6633112902963431267880371)
            ·
              refine ⟨9949669354445146901820557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6633112902963431267880371 9949669354445146901820557)
              ·
                refine ⟨3731126007916930088182709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9949669354445146901820557 3731126007916930088182709)
                ·
                  refine ⟨349793063242212195767129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3731126007916930088182709 349793063242212195767129)
                  ·
                    rfl

theorem cell23_6130976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 5].length) (baseStart_6130976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130976 prefixEnd_6130976 := by exact prefixLift 6130976
  have htrace : WordTrace (prefixWord ++ tailWord_6130976) baseStart_6130976 baseEnd_6130976 := by
    simpa [prefixWord, tailWord_6130976, baseEnd_6130976] using wordTrace_append hprefix tailTrace_6130976
  have hstable : (prefixWord ++ tailWord_6130976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130976).length < 2 ^ (prefixWord ++ tailWord_6130976).sum := by decide
  have hdescent : baseEnd_6130976 < baseStart_6130976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6130989 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_6130989 : Nat := 118140960795 + 6130989 * 2 ^ 59
def prefixEnd_6130989 : Nat := 4983230072969 + 3 ^ 40 * 6130989 * 2
def baseEnd_6130989 : Nat := 1049381414809472737013867

theorem tailTrace_6130989 : CollatzResearch.WordTrace tailWord_6130989 prefixEnd_6130989 1049381414809472737013867 := by
  unfold tailWord_6130989
  simp only [CollatzResearch.WordTrace]
  refine ⟨223615539585481417403252021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149077026390320944935501347 223615539585481417403252021)
  ·
    refine ⟨20963956836138882881554877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223615539585481417403252021 20963956836138882881554877)
    ·
      refine ⟨7861483813552081080583079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20963956836138882881554877 7861483813552081080583079)
      ·
        refine ⟨11792225720328121620874619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7861483813552081080583079 11792225720328121620874619)
        ·
          refine ⟨17688338580492182431311929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11792225720328121620874619 17688338580492182431311929)
          ·
            refine ⟨13266253935369136823483947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17688338580492182431311929 13266253935369136823483947)
            ·
              refine ⟨19899380903053705235225921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13266253935369136823483947 19899380903053705235225921)
              ·
                refine ⟨14924535677290278926419441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19899380903053705235225921 14924535677290278926419441)
                ·
                  refine ⟨11193401757967709194814581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14924535677290278926419441 11193401757967709194814581)
                  ·
                    refine ⟨1049381414809472737013867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11193401757967709194814581 1049381414809472737013867)
                    ·
                      rfl

theorem cell23_6130989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_6130989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6130989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6130989 prefixEnd_6130989 := by exact prefixLift 6130989
  have htrace : WordTrace (prefixWord ++ tailWord_6130989) baseStart_6130989 baseEnd_6130989 := by
    simpa [prefixWord, tailWord_6130989, baseEnd_6130989] using wordTrace_append hprefix tailTrace_6130989
  have hstable : (prefixWord ++ tailWord_6130989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6130989).length < 2 ^ (prefixWord ++ tailWord_6130989).sum := by decide
  have hdescent : baseEnd_6130989 < baseStart_6130989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6130989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131029 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 2, 2, 3]
def baseStart_6131029 : Nat := 118140960795 + 6131029 * 2 ^ 59
def prefixEnd_6131029 : Nat := 4983230072969 + 3 ^ 40 * 6131029 * 2
def baseEnd_6131029 : Nat := 3148164783654598054541417

theorem tailTrace_6131029 : CollatzResearch.WordTrace tailWord_6131029 prefixEnd_6131029 3148164783654598054541417 := by
  unfold tailWord_6131029
  simp only [CollatzResearch.WordTrace]
  refine ⟨223616998505336504234708141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149077999003557669489805427 223616998505336504234708141)
  ·
    refine ⟨83856374439501189088015553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223616998505336504234708141 83856374439501189088015553)
    ·
      refine ⟨62892280829625891816011665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83856374439501189088015553 62892280829625891816011665)
      ·
        refine ⟨47169210622219418862008749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62892280829625891816011665 47169210622219418862008749)
        ·
          refine ⟨17688453983332282073253281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47169210622219418862008749 17688453983332282073253281)
          ·
            refine ⟨13266340487499211554939961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17688453983332282073253281 13266340487499211554939961)
            ·
              refine ⟨9949755365624408666204971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13266340487499211554939961 9949755365624408666204971)
              ·
                refine ⟨14924633048436612999307457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9949755365624408666204971 14924633048436612999307457)
                ·
                  refine ⟨11193474786327459749480593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14924633048436612999307457 11193474786327459749480593)
                  ·
                    refine ⟨8395106089745594812110445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11193474786327459749480593 8395106089745594812110445)
                    ·
                      refine ⟨3148164783654598054541417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8395106089745594812110445 3148164783654598054541417)
                      ·
                        rfl

theorem cell23_6131029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_6131029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131029 prefixEnd_6131029 := by exact prefixLift 6131029
  have htrace : WordTrace (prefixWord ++ tailWord_6131029) baseStart_6131029 baseEnd_6131029 := by
    simpa [prefixWord, tailWord_6131029, baseEnd_6131029] using wordTrace_append hprefix tailTrace_6131029
  have hstable : (prefixWord ++ tailWord_6131029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131029).length < 2 ^ (prefixWord ++ tailWord_6131029).sum := by decide
  have hdescent : baseEnd_6131029 < baseStart_6131029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131053 : List Nat := [1, 5, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_6131053 : Nat := 118140960795 + 6131053 * 2 ^ 59
def prefixEnd_6131053 : Nat := 4983230072969 + 3 ^ 40 * 6131053 * 2
def baseEnd_6131053 : Nat := 1049392369063435320213769

theorem tailTrace_6131053 : CollatzResearch.WordTrace tailWord_6131053 prefixEnd_6131053 1049392369063435320213769 := by
  unfold tailWord_6131053
  simp only [CollatzResearch.WordTrace]
  refine ⟨223617873857249556333581813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149078582571499704222387875 223617873857249556333581813)
  ·
    refine ⟨20964175674117145906273295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223617873857249556333581813 20964175674117145906273295)
    ·
      refine ⟨31446263511175718859409943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20964175674117145906273295 31446263511175718859409943)
      ·
        refine ⟨47169395266763578289114915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31446263511175718859409943 47169395266763578289114915)
        ·
          refine ⟨70754092900145367433672373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47169395266763578289114915 70754092900145367433672373)
          ·
            refine ⟨6633196209388628196906785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70754092900145367433672373 6633196209388628196906785)
            ·
              refine ⟨4974897157041471147680089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6633196209388628196906785 4974897157041471147680089)
              ·
                refine ⟨3731172867781103360760067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4974897157041471147680089 3731172867781103360760067)
                ·
                  refine ⟨5596759301671655041140101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3731172867781103360760067 5596759301671655041140101)
                  ·
                    refine ⟨1049392369063435320213769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5596759301671655041140101 1049392369063435320213769)
                    ·
                      rfl

theorem cell23_6131053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_6131053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131053 prefixEnd_6131053 := by exact prefixLift 6131053
  have htrace : WordTrace (prefixWord ++ tailWord_6131053) baseStart_6131053 baseEnd_6131053 := by
    simpa [prefixWord, tailWord_6131053, baseEnd_6131053] using wordTrace_append hprefix tailTrace_6131053
  have hstable : (prefixWord ++ tailWord_6131053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131053).length < 2 ^ (prefixWord ++ tailWord_6131053).sum := by decide
  have hdescent : baseEnd_6131053 < baseStart_6131053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131086 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2]
def baseStart_6131086 : Nat := 118140960795 + 6131086 * 2 ^ 59
def prefixEnd_6131086 : Nat := 4983230072969 + 3 ^ 40 * 6131086 * 2
def baseEnd_6131086 : Nat := 3148194052051904331528655

theorem tailTrace_6131086 : CollatzResearch.WordTrace tailWord_6131086 prefixEnd_6131086 3148194052051904331528655 := by
  unfold tailWord_6131086
  simp only [CollatzResearch.WordTrace]
  refine ⟨27952384683266250371191639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149079384977420001979688741 27952384683266250371191639)
  ·
    refine ⟨41928577024899375556787459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27952384683266250371191639 41928577024899375556787459)
    ·
      refine ⟨62892865537349063335181189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41928577024899375556787459 62892865537349063335181189)
      ·
        refine ⟨11792412288252949375346473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62892865537349063335181189 11792412288252949375346473)
        ·
          refine ⟨8844309216189712031509855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11792412288252949375346473 8844309216189712031509855)
          ·
            refine ⟨13266463824284568047264783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8844309216189712031509855 13266463824284568047264783)
            ·
              refine ⟨19899695736426852070897175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13266463824284568047264783 19899695736426852070897175)
              ·
                refine ⟨29849543604640278106345763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19899695736426852070897175 29849543604640278106345763)
                ·
                  refine ⟨44774315406960417159518645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29849543604640278106345763 44774315406960417159518645)
                  ·
                    refine ⟨4197592069402539108704873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44774315406960417159518645 4197592069402539108704873)
                    ·
                      refine ⟨3148194052051904331528655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4197592069402539108704873 3148194052051904331528655)
                      ·
                        rfl

theorem cell23_6131086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_6131086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131086 prefixEnd_6131086 := by exact prefixLift 6131086
  have htrace : WordTrace (prefixWord ++ tailWord_6131086) baseStart_6131086 baseEnd_6131086 := by
    simpa [prefixWord, tailWord_6131086, baseEnd_6131086] using wordTrace_append hprefix tailTrace_6131086
  have hstable : (prefixWord ++ tailWord_6131086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131086).length < 2 ^ (prefixWord ++ tailWord_6131086).sum := by decide
  have hdescent : baseEnd_6131086 < baseStart_6131086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131095 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 6]
def baseStart_6131095 : Nat := 118140960795 + 6131095 * 2 ^ 59
def prefixEnd_6131095 : Nat := 4983230072969 + 3 ^ 40 * 6131095 * 2
def baseEnd_6131095 : Nat := 3148198673377794796316113

theorem tailTrace_6131095 : CollatzResearch.WordTrace tailWord_6131095 prefixEnd_6131095 3148198673377794796316113 := by
  unfold tailWord_6131095
  simp only [CollatzResearch.WordTrace]
  refine ⟨223619405723097397506610739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149079603815398265004407159 223619405723097397506610739)
  ·
    refine ⟨335429108584646096259916109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223619405723097397506610739 335429108584646096259916109)
    ·
      refine ⟨125785915719242286097468541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335429108584646096259916109 125785915719242286097468541)
      ·
        refine ⟨47169718394715857286550703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125785915719242286097468541 47169718394715857286550703)
        ·
          refine ⟨70754577592073785929826055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47169718394715857286550703 70754577592073785929826055)
          ·
            refine ⟨106131866388110678894739083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70754577592073785929826055 106131866388110678894739083)
            ·
              refine ⟨159197799582166018342108625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106131866388110678894739083 159197799582166018342108625)
              ·
                refine ⟨119398349686624513756581469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159197799582166018342108625 119398349686624513756581469)
                ·
                  refine ⟨44774381132484192658718051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119398349686624513756581469 44774381132484192658718051)
                  ·
                    refine ⟨67161571698726288988077077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44774381132484192658718051 67161571698726288988077077)
                    ·
                      refine ⟨3148198673377794796316113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67161571698726288988077077 3148198673377794796316113)
                      ·
                        rfl

theorem cell23_6131095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_6131095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131095 prefixEnd_6131095 := by exact prefixLift 6131095
  have htrace : WordTrace (prefixWord ++ tailWord_6131095) baseStart_6131095 baseEnd_6131095 := by
    simpa [prefixWord, tailWord_6131095, baseEnd_6131095] using wordTrace_append hprefix tailTrace_6131095
  have hstable : (prefixWord ++ tailWord_6131095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131095).length < 2 ^ (prefixWord ++ tailWord_6131095).sum := by decide
  have hdescent : baseEnd_6131095 < baseStart_6131095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131135 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 2, 7]
def baseStart_6131135 : Nat := 118140960795 + 6131135 * 2 ^ 59
def prefixEnd_6131135 : Nat := 4983230072969 + 3 ^ 40 * 6131135 * 2
def baseEnd_6131135 : Nat := 1049406404201324879938643

theorem tailTrace_6131135 : CollatzResearch.WordTrace tailWord_6131135 prefixEnd_6131135 1049406404201324879938643 := by
  unfold tailWord_6131135
  simp only [CollatzResearch.WordTrace]
  refine ⟨223620864642952484338066859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149080576428634989558711239 223620864642952484338066859)
  ·
    refine ⟨335431296964428726507100289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223620864642952484338066859 335431296964428726507100289)
    ·
      refine ⟨251573472723321544880325217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335431296964428726507100289 251573472723321544880325217)
      ·
        refine ⟨188680104542491158660243913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251573472723321544880325217 188680104542491158660243913)
        ·
          refine ⟨141510078406868368995182935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188680104542491158660243913 141510078406868368995182935)
          ·
            refine ⟨212265117610302553492774403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141510078406868368995182935 212265117610302553492774403)
            ·
              refine ⟨318397676415453830239161605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212265117610302553492774403 318397676415453830239161605)
              ·
                refine ⟨59699564327897593169842801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 318397676415453830239161605 59699564327897593169842801)
                ·
                  refine ⟨44774673245923194877382101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59699564327897593169842801 44774673245923194877382101)
                  ·
                    refine ⟨1049406404201324879938643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44774673245923194877382101 1049406404201324879938643)
                    ·
                      rfl

theorem cell23_6131135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 7].length) (baseStart_6131135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131135 prefixEnd_6131135 := by exact prefixLift 6131135
  have htrace : WordTrace (prefixWord ++ tailWord_6131135) baseStart_6131135 baseEnd_6131135 := by
    simpa [prefixWord, tailWord_6131135, baseEnd_6131135] using wordTrace_append hprefix tailTrace_6131135
  have hstable : (prefixWord ++ tailWord_6131135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131135).length < 2 ^ (prefixWord ++ tailWord_6131135).sum := by decide
  have hdescent : baseEnd_6131135 < baseStart_6131135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131182 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 1, 8]
def baseStart_6131182 : Nat := 118140960795 + 6131182 * 2 ^ 59
def prefixEnd_6131182 : Nat := 4983230072969 + 3 ^ 40 * 6131182 * 2
def baseEnd_6131182 : Nat := 1049414448731578651976071

theorem tailTrace_6131182 : CollatzResearch.WordTrace tailWord_6131182 prefixEnd_6131182 1049414448731578651976071 := by
  unfold tailWord_6131182
  simp only [CollatzResearch.WordTrace]
  refine ⟨27952822359222776420628475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149081719249188140910018533 27952822359222776420628475)
  ·
    refine ⟨41929233538834164630942713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27952822359222776420628475 41929233538834164630942713)
    ·
      refine ⟨31446925154125623473207035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41929233538834164630942713 31446925154125623473207035)
      ·
        refine ⟨47170387731188435209810553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31446925154125623473207035 47170387731188435209810553)
        ·
          refine ⟨35377790798391326407357915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47170387731188435209810553 35377790798391326407357915)
          ·
            refine ⟨53066686197586989611036873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35377790798391326407357915 53066686197586989611036873)
            ·
              refine ⟨39800014648190242208277655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53066686197586989611036873 39800014648190242208277655)
              ·
                refine ⟨59700021972285363312416483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39800014648190242208277655 59700021972285363312416483)
                ·
                  refine ⟨89550032958428044968624725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59700021972285363312416483 89550032958428044968624725)
                  ·
                    refine ⟨1049414448731578651976071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89550032958428044968624725 1049414448731578651976071)
                    ·
                      rfl

theorem cell23_6131182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_6131182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131182 prefixEnd_6131182 := by exact prefixLift 6131182
  have htrace : WordTrace (prefixWord ++ tailWord_6131182) baseStart_6131182 baseEnd_6131182 := by
    simpa [prefixWord, tailWord_6131182, baseEnd_6131182] using wordTrace_append hprefix tailTrace_6131182
  have hstable : (prefixWord ++ tailWord_6131182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131182).length < 2 ^ (prefixWord ++ tailWord_6131182).sum := by decide
  have hdescent : baseEnd_6131182 < baseStart_6131182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131192 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 2, 1, 5]
def baseStart_6131192 : Nat := 118140960795 + 6131192 * 2 ^ 59
def prefixEnd_6131192 : Nat := 4983230072969 + 3 ^ 40 * 6131192 * 2
def baseEnd_6131192 : Nat := 3148248481001280916803167

theorem tailTrace_6131192 : CollatzResearch.WordTrace tailWord_6131192 prefixEnd_6131192 3148248481001280916803167 := by
  unfold tailWord_6131192
  simp only [CollatzResearch.WordTrace]
  refine ⟨111811471801872991536445915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149081962402497322048594553 111811471801872991536445915)
  ·
    refine ⟨167717207702809487304668873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111811471801872991536445915 167717207702809487304668873)
    ·
      refine ⟨125787905777107115478501655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167717207702809487304668873 125787905777107115478501655)
      ·
        refine ⟨188681858665660673217752483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125787905777107115478501655 188681858665660673217752483)
        ·
          refine ⟨283022787998491009826628725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188681858665660673217752483 283022787998491009826628725)
          ·
            refine ⟨26533386374858532171246443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 283022787998491009826628725 26533386374858532171246443)
            ·
              refine ⟨39800079562287798256869665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26533386374858532171246443 39800079562287798256869665)
              ·
                refine ⟨29850059671715848692652249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39800079562287798256869665 29850059671715848692652249)
                ·
                  refine ⟨22387544753786886519489187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29850059671715848692652249 22387544753786886519489187)
                  ·
                    refine ⟨33581317130680329779233781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22387544753786886519489187 33581317130680329779233781)
                    ·
                      refine ⟨3148248481001280916803167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33581317130680329779233781 3148248481001280916803167)
                      ·
                        rfl

theorem cell23_6131192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_6131192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131192 prefixEnd_6131192 := by exact prefixLift 6131192
  have htrace : WordTrace (prefixWord ++ tailWord_6131192) baseStart_6131192 baseEnd_6131192 := by
    simpa [prefixWord, tailWord_6131192, baseEnd_6131192] using wordTrace_append hprefix tailTrace_6131192
  have hstable : (prefixWord ++ tailWord_6131192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131192).length < 2 ^ (prefixWord ++ tailWord_6131192).sum := by decide
  have hdescent : baseEnd_6131192 < baseStart_6131192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131249 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 4, 5, 2]
def baseStart_6131249 : Nat := 118140960795 + 6131249 * 2 ^ 59
def prefixEnd_6131249 : Nat := 4983230072969 + 3 ^ 40 * 6131249 * 2
def baseEnd_6131249 : Nat := 3148277749398587193790405

theorem tailTrace_6131249 : CollatzResearch.WordTrace tailWord_6131249 prefixEnd_6131249 3148277749398587193790405 := by
  unfold tailWord_6131249
  simp only [CollatzResearch.WordTrace]
  refine ⟨223625022564539481807716801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149083348376359654538477867 223625022564539481807716801)
  ·
    refine ⟨167718766923404611355787601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223625022564539481807716801 167718766923404611355787601)
    ·
      refine ⟨125789075192553458516840701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167718766923404611355787601 125789075192553458516840701)
      ·
        refine ⟨47170903197207546943815263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125789075192553458516840701 47170903197207546943815263)
        ·
          refine ⟨70756354795811320415722895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47170903197207546943815263 70756354795811320415722895)
          ·
            refine ⟨106134532193716980623584343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70756354795811320415722895 106134532193716980623584343)
            ·
              refine ⟨159201798290575470935376515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106134532193716980623584343 159201798290575470935376515)
              ·
                refine ⟨238802697435863206403064773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159201798290575470935376515 238802697435863206403064773)
                ·
                  refine ⟨44775505769224351200574645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 238802697435863206403064773 44775505769224351200574645)
                  ·
                    refine ⟨4197703665864782925053873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44775505769224351200574645 4197703665864782925053873)
                    ·
                      refine ⟨3148277749398587193790405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4197703665864782925053873 3148277749398587193790405)
                      ·
                        rfl

theorem cell23_6131249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_6131249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131249 prefixEnd_6131249 := by exact prefixLift 6131249
  have htrace : WordTrace (prefixWord ++ tailWord_6131249) baseStart_6131249 baseEnd_6131249 := by
    simpa [prefixWord, tailWord_6131249, baseEnd_6131249] using wordTrace_append hprefix tailTrace_6131249
  have hstable : (prefixWord ++ tailWord_6131249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131249).length < 2 ^ (prefixWord ++ tailWord_6131249).sum := by decide
  have hdescent : baseEnd_6131249 < baseStart_6131249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131299 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 3]
def baseStart_6131299 : Nat := 118140960795 + 6131299 * 2 ^ 59
def prefixEnd_6131299 : Nat := 4983230072969 + 3 ^ 40 * 6131299 * 2
def baseEnd_6131299 : Nat := 3148303423431311998165175

theorem tailTrace_6131299 : CollatzResearch.WordTrace tailWord_6131299 prefixEnd_6131299 3148303423431311998165175 := by
  unfold tailWord_6131299
  simp only [CollatzResearch.WordTrace]
  refine ⟨223626846214358340347036951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149084564142905560231357967 223626846214358340347036951)
  ·
    refine ⟨335440269321537510520555427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223626846214358340347036951 335440269321537510520555427)
    ·
      refine ⟨503160403982306265780833141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335440269321537510520555427 503160403982306265780833141)
      ·
        refine ⟨47171287873341212416953107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 503160403982306265780833141 47171287873341212416953107)
        ·
          refine ⟨70756931810011818625429661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47171287873341212416953107 70756931810011818625429661)
          ·
            refine ⟨26533849428754431984536123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70756931810011818625429661 26533849428754431984536123)
            ·
              refine ⟨39800774143131647976804185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26533849428754431984536123 39800774143131647976804185)
              ·
                refine ⟨29850580607348735982603139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39800774143131647976804185 29850580607348735982603139)
                ·
                  refine ⟨44775870911023103973904709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29850580607348735982603139 44775870911023103973904709)
                  ·
                    refine ⟨8395475795816831995107133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44775870911023103973904709 8395475795816831995107133)
                    ·
                      refine ⟨3148303423431311998165175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8395475795816831995107133 3148303423431311998165175)
                      ·
                        rfl

theorem cell23_6131299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_6131299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131299 prefixEnd_6131299 := by exact prefixLift 6131299
  have htrace : WordTrace (prefixWord ++ tailWord_6131299) baseStart_6131299 baseEnd_6131299 := by
    simpa [prefixWord, tailWord_6131299, baseEnd_6131299] using wordTrace_append hprefix tailTrace_6131299
  have hstable : (prefixWord ++ tailWord_6131299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131299).length < 2 ^ (prefixWord ++ tailWord_6131299).sum := by decide
  have hdescent : baseEnd_6131299 < baseStart_6131299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131306 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 3, 4]
def baseStart_6131306 : Nat := 118140960795 + 6131306 * 2 ^ 59
def prefixEnd_6131306 : Nat := 4983230072969 + 3 ^ 40 * 6131306 * 2
def baseEnd_6131306 : Nat := 1049435672598631156925881

theorem tailTrace_6131306 : CollatzResearch.WordTrace tailWord_6131306 prefixEnd_6131306 1049435672598631156925881 := by
  unfold tailWord_6131306
  simp only [CollatzResearch.WordTrace]
  refine ⟨55906775381333245135635443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149084734350221987028361181 55906775381333245135635443)
  ·
    refine ⟨83860163071999867703453165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55906775381333245135635443 83860163071999867703453165)
    ·
      refine ⟨31447561151999950388794937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83860163071999867703453165 31447561151999950388794937)
      ·
        refine ⟨23585670863999962791596203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31447561151999950388794937 23585670863999962791596203)
        ·
          refine ⟨35378506295999944187394305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23585670863999962791596203 35378506295999944187394305)
          ·
            refine ⟨26533879721999958140545729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35378506295999944187394305 26533879721999958140545729)
            ·
              refine ⟨19900409791499968605409297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26533879721999958140545729 19900409791499968605409297)
              ·
                refine ⟨14925307343624976454056973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19900409791499968605409297 14925307343624976454056973)
                ·
                  refine ⟨5596990253859366170271365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14925307343624976454056973 5596990253859366170271365)
                  ·
                    refine ⟨1049435672598631156925881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5596990253859366170271365 1049435672598631156925881)
                    ·
                      rfl

theorem cell23_6131306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_6131306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131306 prefixEnd_6131306 := by exact prefixLift 6131306
  have htrace : WordTrace (prefixWord ++ tailWord_6131306) baseStart_6131306 baseEnd_6131306 := by
    simpa [prefixWord, tailWord_6131306, baseEnd_6131306] using wordTrace_append hprefix tailTrace_6131306
  have hstable : (prefixWord ++ tailWord_6131306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131306).length < 2 ^ (prefixWord ++ tailWord_6131306).sum := by decide
  have hdescent : baseEnd_6131306 < baseStart_6131306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131322 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8]
def baseStart_6131322 : Nat := 118140960795 + 6131322 * 2 ^ 59
def prefixEnd_6131322 : Nat := 4983230072969 + 3 ^ 40 * 6131322 * 2
def baseEnd_6131322 : Nat := 3148315233486365408177569

theorem tailTrace_6131322 : CollatzResearch.WordTrace tailWord_6131322 prefixEnd_6131322 3148315233486365408177569 := by
  unfold tailWord_6131322
  simp only [CollatzResearch.WordTrace]
  refine ⟨55906921273318753818781055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149085123395516676850082813 55906921273318753818781055)
  ·
    refine ⟨83860381909978130728171583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55906921273318753818781055 83860381909978130728171583)
    ·
      refine ⟨125790572864967196092257375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83860381909978130728171583 125790572864967196092257375)
      ·
        refine ⟨188685859297450794138386063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125790572864967196092257375 188685859297450794138386063)
        ·
          refine ⟨283028788946176191207579095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188685859297450794138386063 283028788946176191207579095)
          ·
            refine ⟨424543183419264286811368643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283028788946176191207579095 424543183419264286811368643)
            ·
              refine ⟨636814775128896430217052965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424543183419264286811368643 636814775128896430217052965)
              ·
                refine ⟨119402770336668080665697431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 636814775128896430217052965 119402770336668080665697431)
                ·
                  refine ⟨179104155505002120998546147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119402770336668080665697431 179104155505002120998546147)
                  ·
                    refine ⟨268656233257503181497819221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 179104155505002120998546147 268656233257503181497819221)
                    ·
                      refine ⟨3148315233486365408177569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 268656233257503181497819221 3148315233486365408177569)
                      ·
                        rfl

theorem cell23_6131322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_6131322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131322 prefixEnd_6131322 := by exact prefixLift 6131322
  have htrace : WordTrace (prefixWord ++ tailWord_6131322) baseStart_6131322 baseEnd_6131322 := by
    simpa [prefixWord, tailWord_6131322, baseEnd_6131322] using wordTrace_append hprefix tailTrace_6131322
  have hstable : (prefixWord ++ tailWord_6131322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131322).length < 2 ^ (prefixWord ++ tailWord_6131322).sum := by decide
  have hdescent : baseEnd_6131322 < baseStart_6131322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131379 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 1, 6]
def baseStart_6131379 : Nat := 118140960795 + 6131379 * 2 ^ 59
def prefixEnd_6131379 : Nat := 4983230072969 + 3 ^ 40 * 6131379 * 2
def baseEnd_6131379 : Nat := 1049448167294557228388269

theorem tailTrace_6131379 : CollatzResearch.WordTrace tailWord_6131379 prefixEnd_6131379 1049448167294557228388269 := by
  unfold tailWord_6131379
  simp only [CollatzResearch.WordTrace]
  refine ⟨223629764054068514009949191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149086509369379009339966127 223629764054068514009949191)
  ·
    refine ⟨335444646081102771014923787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223629764054068514009949191 335444646081102771014923787)
    ·
      refine ⟨503166969121654156522385681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335444646081102771014923787 503166969121654156522385681)
      ·
        refine ⟨377375226841240617391789261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503166969121654156522385681 377375226841240617391789261)
        ·
          refine ⟨141515710065465231521920973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 377375226841240617391789261 141515710065465231521920973)
          ·
            refine ⟨53068391274549461820720365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141515710065465231521920973 53068391274549461820720365)
            ·
              refine ⟨19900646727956048182770137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53068391274549461820720365 19900646727956048182770137)
              ·
                refine ⟨14925485045967036137077603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19900646727956048182770137 14925485045967036137077603)
                ·
                  refine ⟨22388227568950554205616405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14925485045967036137077603 22388227568950554205616405)
                  ·
                    refine ⟨1049448167294557228388269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22388227568950554205616405 1049448167294557228388269)
                    ·
                      rfl

theorem cell23_6131379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 6].length) (baseStart_6131379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131379 prefixEnd_6131379 := by exact prefixLift 6131379
  have htrace : WordTrace (prefixWord ++ tailWord_6131379) baseStart_6131379 baseEnd_6131379 := by
    simpa [prefixWord, tailWord_6131379, baseEnd_6131379] using wordTrace_append hprefix tailTrace_6131379
  have hstable : (prefixWord ++ tailWord_6131379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131379).length < 2 ^ (prefixWord ++ tailWord_6131379).sum := by decide
  have hdescent : baseEnd_6131379 < baseStart_6131379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131383 : List Nat := [1, 1, 3, 1, 5, 2, 3, 1, 1, 5]
def baseStart_6131383 : Nat := 118140960795 + 6131383 * 2 ^ 59
def prefixEnd_6131383 : Nat := 4983230072969 + 3 ^ 40 * 6131383 * 2
def baseEnd_6131383 : Nat := 1049448851935429889838263

theorem tailTrace_6131383 : CollatzResearch.WordTrace tailWord_6131383 prefixEnd_6131383 1049448851935429889838263 := by
  unfold tailWord_6131383
  simp only [CollatzResearch.WordTrace]
  refine ⟨223629909946054022693094803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149086606630702681795396535 223629909946054022693094803)
  ·
    refine ⟨335444864919081034039642205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223629909946054022693094803 335444864919081034039642205)
    ·
      refine ⟨125791824344655387764865827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335444864919081034039642205 125791824344655387764865827)
      ·
        refine ⟨188687736516983081647298741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125791824344655387764865827 188687736516983081647298741)
        ·
          refine ⟨17689475298467163904434257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188687736516983081647298741 17689475298467163904434257)
          ·
            refine ⟨13267106473850372928325693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17689475298467163904434257 13267106473850372928325693)
            ·
              refine ⟨4975164927693889848122135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13267106473850372928325693 4975164927693889848122135)
              ·
                refine ⟨7462747391540834772183203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4975164927693889848122135 7462747391540834772183203)
                ·
                  refine ⟨11194121087311252158274805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7462747391540834772183203 11194121087311252158274805)
                  ·
                    refine ⟨1049448851935429889838263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11194121087311252158274805 1049448851935429889838263)
                    ·
                      rfl

theorem cell23_6131383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_6131383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131383 prefixEnd_6131383 := by exact prefixLift 6131383
  have htrace : WordTrace (prefixWord ++ tailWord_6131383) baseStart_6131383 baseEnd_6131383 := by
    simpa [prefixWord, tailWord_6131383, baseEnd_6131383] using wordTrace_append hprefix tailTrace_6131383
  have hstable : (prefixWord ++ tailWord_6131383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131383).length < 2 ^ (prefixWord ++ tailWord_6131383).sum := by decide
  have hdescent : baseEnd_6131383 < baseStart_6131383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131399 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_6131399 : Nat := 118140960795 + 6131399 * 2 ^ 59
def prefixEnd_6131399 : Nat := 4983230072969 + 3 ^ 40 * 6131399 * 2
def baseEnd_6131399 : Nat := 3148354771496761606914715

theorem tailTrace_6131399 : CollatzResearch.WordTrace tailWord_6131399 prefixEnd_6131399 3148354771496761606914715 := by
  unfold tailWord_6131399
  simp only [CollatzResearch.WordTrace]
  refine ⟨223630493513996057425677251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149086995675997371617118167 223630493513996057425677251)
  ·
    refine ⟨335445740270994086138515877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223630493513996057425677251 335445740270994086138515877)
    ·
      refine ⟨62896076300811391150971727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335445740270994086138515877 62896076300811391150971727)
      ·
        refine ⟨94344114451217086726457591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62896076300811391150971727 94344114451217086726457591)
        ·
          refine ⟨141516171676825630089686387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94344114451217086726457591 141516171676825630089686387)
          ·
            refine ⟨212274257515238445134529581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141516171676825630089686387 212274257515238445134529581)
            ·
              refine ⟨79602846568214416925448593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212274257515238445134529581 79602846568214416925448593)
              ·
                refine ⟨59702134926160812694086445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79602846568214416925448593 59702134926160812694086445)
                ·
                  refine ⟨22388300597310304760282417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59702134926160812694086445 22388300597310304760282417)
                  ·
                    refine ⟨16791225447982728570211813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22388300597310304760282417 16791225447982728570211813)
                    ·
                      refine ⟨3148354771496761606914715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16791225447982728570211813 3148354771496761606914715)
                      ·
                        rfl

theorem cell23_6131399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_6131399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131399 prefixEnd_6131399 := by exact prefixLift 6131399
  have htrace : WordTrace (prefixWord ++ tailWord_6131399) baseStart_6131399 baseEnd_6131399 := by
    simpa [prefixWord, tailWord_6131399, baseEnd_6131399] using wordTrace_append hprefix tailTrace_6131399
  have hstable : (prefixWord ++ tailWord_6131399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131399).length < 2 ^ (prefixWord ++ tailWord_6131399).sum := by decide
  have hdescent : baseEnd_6131399 < baseStart_6131399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131406 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3]
def baseStart_6131406 : Nat := 118140960795 + 6131406 * 2 ^ 59
def prefixEnd_6131406 : Nat := 4983230072969 + 3 ^ 40 * 6131406 * 2
def baseEnd_6131406 : Nat := 3148358365861343079527183

theorem tailTrace_6131406 : CollatzResearch.WordTrace tailWord_6131406 prefixEnd_6131406 3148358365861343079527183 := by
  unfold tailWord_6131406
  simp only [CollatzResearch.WordTrace]
  refine ⟨27953843603121337202647759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149087165883313798414121381 27953843603121337202647759)
  ·
    refine ⟨41930765404682005803971639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27953843603121337202647759 41930765404682005803971639)
    ·
      refine ⟨62896148107023008705957459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41930765404682005803971639 62896148107023008705957459)
      ·
        refine ⟨94344222160534513058936189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62896148107023008705957459 94344222160534513058936189)
        ·
          refine ⟨35379083310200442397101071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94344222160534513058936189 35379083310200442397101071)
          ·
            refine ⟨53068624965300663595651607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35379083310200442397101071 53068624965300663595651607)
            ·
              refine ⟨79602937447950995393477411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53068624965300663595651607 79602937447950995393477411)
              ·
                refine ⟨119404406171926493090216117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79602937447950995393477411 119404406171926493090216117)
                ·
                  refine ⟨11194163078618108727207761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119404406171926493090216117 11194163078618108727207761)
                  ·
                    refine ⟨8395622308963581545405821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11194163078618108727207761 8395622308963581545405821)
                    ·
                      refine ⟨3148358365861343079527183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8395622308963581545405821 3148358365861343079527183)
                      ·
                        rfl

theorem cell23_6131406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_6131406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131406 prefixEnd_6131406 := by exact prefixLift 6131406
  have htrace : WordTrace (prefixWord ++ tailWord_6131406) baseStart_6131406 baseEnd_6131406 := by
    simpa [prefixWord, tailWord_6131406, baseEnd_6131406] using wordTrace_append hprefix tailTrace_6131406
  have hstable : (prefixWord ++ tailWord_6131406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131406).length < 2 ^ (prefixWord ++ tailWord_6131406).sum := by decide
  have hdescent : baseEnd_6131406 < baseStart_6131406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131409 : List Nat := [1, 2, 2, 1, 2, 4, 3, 8]
def baseStart_6131409 : Nat := 118140960795 + 6131409 * 2 ^ 59
def prefixEnd_6131409 : Nat := 4983230072969 + 3 ^ 40 * 6131409 * 2
def baseEnd_6131409 : Nat := 116605922455678021029247

theorem tailTrace_6131409 : CollatzResearch.WordTrace tailWord_6131409 prefixEnd_6131409 116605922455678021029247 := by
  unfold tailWord_6131409
  simp only [CollatzResearch.WordTrace]
  refine ⟨223630858243959829133541281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149087238829306552755694187 223630858243959829133541281)
  ·
    refine ⟨167723143682969871850155961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223630858243959829133541281 167723143682969871850155961)
    ·
      refine ⟨125792357762227403887616971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167723143682969871850155961 125792357762227403887616971)
      ·
        refine ⟨188688536643341105831425457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125792357762227403887616971 188688536643341105831425457)
        ·
          refine ⟨141516402482505829373569093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188688536643341105831425457 141516402482505829373569093)
          ·
            refine ⟨26534325465469843007544205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141516402482505829373569093 26534325465469843007544205)
            ·
              refine ⟨9950372049551191127829077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26534325465469843007544205 9950372049551191127829077)
              ·
                refine ⟨116605922455678021029247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9950372049551191127829077 116605922455678021029247)
                ·
                  rfl

theorem cell23_6131409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 8].length) (baseStart_6131409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131409 prefixEnd_6131409 := by exact prefixLift 6131409
  have htrace : WordTrace (prefixWord ++ tailWord_6131409) baseStart_6131409 baseEnd_6131409 := by
    simpa [prefixWord, tailWord_6131409, baseEnd_6131409] using wordTrace_append hprefix tailTrace_6131409
  have hstable : (prefixWord ++ tailWord_6131409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131409).length < 2 ^ (prefixWord ++ tailWord_6131409).sum := by decide
  have hdescent : baseEnd_6131409 < baseStart_6131409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131416 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 1, 2, 4]
def baseStart_6131416 : Nat := 118140960795 + 6131416 * 2 ^ 59
def prefixEnd_6131416 : Nat := 4983230072969 + 3 ^ 40 * 6131416 * 2
def baseEnd_6131416 : Nat := 3148363500667888040402137

theorem tailTrace_6131416 : CollatzResearch.WordTrace tailWord_6131416 prefixEnd_6131416 3148363500667888040402137 := by
  unfold tailWord_6131416
  simp only [CollatzResearch.WordTrace]
  refine ⟨111815556777467234664523051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149087409036622979552697401 111815556777467234664523051)
  ·
    refine ⟨167723335166200851996784577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111815556777467234664523051 167723335166200851996784577)
    ·
      refine ⟨125792501374650638997588433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167723335166200851996784577 125792501374650638997588433)
      ·
        refine ⟨94344376030987979248191325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125792501374650638997588433 94344376030987979248191325)
        ·
          refine ⟨35379141011620492218071747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94344376030987979248191325 35379141011620492218071747)
          ·
            refine ⟨53068711517430738327107621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35379141011620492218071747 53068711517430738327107621)
            ·
              refine ⟨9950383409518263436332679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53068711517430738327107621 9950383409518263436332679)
              ·
                refine ⟨14925575114277395154499019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9950383409518263436332679 14925575114277395154499019)
                ·
                  refine ⟨22388362671416092731748529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14925575114277395154499019 22388362671416092731748529)
                  ·
                    refine ⟨16791272003562069548811397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22388362671416092731748529 16791272003562069548811397)
                    ·
                      refine ⟨3148363500667888040402137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16791272003562069548811397 3148363500667888040402137)
                      ·
                        rfl

theorem cell23_6131416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_6131416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131416 prefixEnd_6131416 := by exact prefixLift 6131416
  have htrace : WordTrace (prefixWord ++ tailWord_6131416) baseStart_6131416 baseEnd_6131416 := by
    simpa [prefixWord, tailWord_6131416, baseEnd_6131416] using wordTrace_append hprefix tailTrace_6131416
  have hstable : (prefixWord ++ tailWord_6131416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131416).length < 2 ^ (prefixWord ++ tailWord_6131416).sum := by decide
  have hdescent : baseEnd_6131416 < baseStart_6131416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131436 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 3]
def baseStart_6131436 : Nat := 118140960795 + 6131436 * 2 ^ 59
def prefixEnd_6131436 : Nat := 4983230072969 + 3 ^ 40 * 6131436 * 2
def baseEnd_6131436 : Nat := 3148373770280977962152045

theorem tailTrace_6131436 : CollatzResearch.WordTrace tailWord_6131436 prefixEnd_6131436 3148373770280977962152045 := by
  unfold tailWord_6131436
  simp only [CollatzResearch.WordTrace]
  refine ⟨111815921507431006372387081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149087895343241341829849441 111815921507431006372387081)
  ·
    refine ⟨83861941130573254779290311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111815921507431006372387081 83861941130573254779290311)
    ·
      refine ⟨125792911695859882168935467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83861941130573254779290311 125792911695859882168935467)
      ·
        refine ⟨188689367543789823253403201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125792911695859882168935467 188689367543789823253403201)
        ·
          refine ⟨141517025657842367440052401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188689367543789823253403201 141517025657842367440052401)
          ·
            refine ⟨106137769243381775580039301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141517025657842367440052401 106137769243381775580039301)
            ·
              refine ⟨19900831733134082921257369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106137769243381775580039301 19900831733134082921257369)
              ·
                refine ⟨14925623799850562190943027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19900831733134082921257369 14925623799850562190943027)
                ·
                  refine ⟨22388435699775843286414541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14925623799850562190943027 22388435699775843286414541)
                  ·
                    refine ⟨8395663387415941232405453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22388435699775843286414541 8395663387415941232405453)
                    ·
                      refine ⟨3148373770280977962152045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8395663387415941232405453 3148373770280977962152045)
                      ·
                        rfl

theorem cell23_6131436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_6131436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131436 prefixEnd_6131436 := by exact prefixLift 6131436
  have htrace : WordTrace (prefixWord ++ tailWord_6131436) baseStart_6131436 baseEnd_6131436 := by
    simpa [prefixWord, tailWord_6131436, baseEnd_6131436] using wordTrace_append hprefix tailTrace_6131436
  have hstable : (prefixWord ++ tailWord_6131436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131436).length < 2 ^ (prefixWord ++ tailWord_6131436).sum := by decide
  have hdescent : baseEnd_6131436 < baseStart_6131436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131437 : List Nat := [1, 5, 1, 2, 1, 2, 1, 5, 1, 2, 2]
def baseStart_6131437 : Nat := 118140960795 + 6131437 * 2 ^ 59
def prefixEnd_6131437 : Nat := 4983230072969 + 3 ^ 40 * 6131437 * 2
def baseEnd_6131437 : Nat := 3148374283761632458239541

theorem tailTrace_6131437 : CollatzResearch.WordTrace tailWord_6131437 prefixEnd_6131437 3148374283761632458239541 := by
  unfold tailWord_6131437
  simp only [CollatzResearch.WordTrace]
  refine ⟨223631879487858389915560565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149087919658572259943707043 223631879487858389915560565)
  ·
    refine ⟨20965488701986724054583803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223631879487858389915560565 20965488701986724054583803)
    ·
      refine ⟨31448233052980086081875705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20965488701986724054583803 31448233052980086081875705)
      ·
        refine ⟨23586174789735064561406779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31448233052980086081875705 23586174789735064561406779)
        ·
          refine ⟨35379262184602596842110169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23586174789735064561406779 35379262184602596842110169)
          ·
            refine ⟨26534446638451947631582627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35379262184602596842110169 26534446638451947631582627)
            ·
              refine ⟨39801669957677921447373941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26534446638451947631582627 39801669957677921447373941)
              ·
                refine ⟨3731406558532305135691307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39801669957677921447373941 3731406558532305135691307)
                ·
                  refine ⟨5597109837798457703536961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3731406558532305135691307 5597109837798457703536961)
                  ·
                    refine ⟨4197832378348843277652721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5597109837798457703536961 4197832378348843277652721)
                    ·
                      refine ⟨3148374283761632458239541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4197832378348843277652721 3148374283761632458239541)
                      ·
                        rfl

theorem cell23_6131437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_6131437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131437 prefixEnd_6131437 := by exact prefixLift 6131437
  have htrace : WordTrace (prefixWord ++ tailWord_6131437) baseStart_6131437 baseEnd_6131437 := by
    simpa [prefixWord, tailWord_6131437, baseEnd_6131437] using wordTrace_append hprefix tailTrace_6131437
  have hstable : (prefixWord ++ tailWord_6131437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131437).length < 2 ^ (prefixWord ++ tailWord_6131437).sum := by decide
  have hdescent : baseEnd_6131437 < baseStart_6131437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131453 : List Nat := [1, 4, 1, 1, 1, 1, 2, 6, 2, 1, 3]
def baseStart_6131453 : Nat := 118140960795 + 6131453 * 2 ^ 59
def prefixEnd_6131453 : Nat := 4983230072969 + 3 ^ 40 * 6131453 * 2
def baseEnd_6131453 : Nat := 3148382499452104395639467

theorem tailTrace_6131453 : CollatzResearch.WordTrace tailWord_6131453 prefixEnd_6131453 3148382499452104395639467 := by
  unfold tailWord_6131453
  simp only [CollatzResearch.WordTrace]
  refine ⟨223632463055800424648143013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149088308703866949765428675 223632463055800424648143013)
  ·
    refine ⟨41931086822962579621526815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223632463055800424648143013 41931086822962579621526815)
    ·
      refine ⟨62896630234443869432290223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41931086822962579621526815 62896630234443869432290223)
      ·
        refine ⟨94344945351665804148435335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62896630234443869432290223 94344945351665804148435335)
        ·
          refine ⟨141517418027498706222653003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94344945351665804148435335 141517418027498706222653003)
          ·
            refine ⟨212276127041248059333979505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141517418027498706222653003 212276127041248059333979505)
            ·
              refine ⟨159207095280936044500484629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212276127041248059333979505 159207095280936044500484629)
              ·
                refine ⟨7462832591293877085960217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 159207095280936044500484629 7462832591293877085960217)
                ·
                  refine ⟨5597124443470407814470163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7462832591293877085960217 5597124443470407814470163)
                  ·
                    refine ⟨8395686665205611721705245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5597124443470407814470163 8395686665205611721705245)
                    ·
                      refine ⟨3148382499452104395639467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8395686665205611721705245 3148382499452104395639467)
                      ·
                        rfl

theorem cell23_6131453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_6131453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131453 prefixEnd_6131453 := by exact prefixLift 6131453
  have htrace : WordTrace (prefixWord ++ tailWord_6131453) baseStart_6131453 baseEnd_6131453 := by
    simpa [prefixWord, tailWord_6131453, baseEnd_6131453] using wordTrace_append hprefix tailTrace_6131453
  have hstable : (prefixWord ++ tailWord_6131453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131453).length < 2 ^ (prefixWord ++ tailWord_6131453).sum := by decide
  have hdescent : baseEnd_6131453 < baseStart_6131453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131459 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 4]
def baseStart_6131459 : Nat := 118140960795 + 6131459 * 2 ^ 59
def prefixEnd_6131459 : Nat := 4983230072969 + 3 ^ 40 * 6131459 * 2
def baseEnd_6131459 : Nat := 3148385580336031372164439

theorem tailTrace_6131459 : CollatzResearch.WordTrace tailWord_6131459 prefixEnd_6131459 3148385580336031372164439 := by
  unfold tailWord_6131459
  simp only [CollatzResearch.WordTrace]
  refine ⟨223632681893778687672861431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149088454595852458448574287 223632681893778687672861431)
  ·
    refine ⟨335449022840668031509292147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223632681893778687672861431 335449022840668031509292147)
    ·
      refine ⟨503173534261002047263938221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335449022840668031509292147 503173534261002047263938221)
      ·
        refine ⟨188690075347875767723976833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 503173534261002047263938221 188690075347875767723976833)
        ·
          refine ⟨141517556510906825792982625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188690075347875767723976833 141517556510906825792982625)
          ·
            refine ⟨106138167383180119344736969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141517556510906825792982625 106138167383180119344736969)
            ·
              refine ⟨79603625537385089508552727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106138167383180119344736969 79603625537385089508552727)
              ·
                refine ⟨119405438306077634262829091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79603625537385089508552727 119405438306077634262829091)
                ·
                  refine ⟨179108157459116451394243637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119405438306077634262829091 179108157459116451394243637)
                  ·
                    refine ⟨16791389761792167318210341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 179108157459116451394243637 16791389761792167318210341)
                    ·
                      refine ⟨3148385580336031372164439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16791389761792167318210341 3148385580336031372164439)
                      ·
                        rfl

theorem cell23_6131459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_6131459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131459 prefixEnd_6131459 := by exact prefixLift 6131459
  have htrace : WordTrace (prefixWord ++ tailWord_6131459) baseStart_6131459 baseEnd_6131459 := by
    simpa [prefixWord, tailWord_6131459, baseEnd_6131459] using wordTrace_append hprefix tailTrace_6131459
  have hstable : (prefixWord ++ tailWord_6131459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131459).length < 2 ^ (prefixWord ++ tailWord_6131459).sum := by decide
  have hdescent : baseEnd_6131459 < baseStart_6131459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131496 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_6131496 : Nat := 118140960795 + 6131496 * 2 ^ 59
def prefixEnd_6131496 : Nat := 4983230072969 + 3 ^ 40 * 6131496 * 2
def baseEnd_6131496 : Nat := 3148404579120247727401769

theorem tailTrace_6131496 : CollatzResearch.WordTrace tailWord_6131496 prefixEnd_6131496 3148404579120247727401769 := by
  unfold tailWord_6131496
  simp only [CollatzResearch.WordTrace]
  refine ⟨111817015697322321495979171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149089354263096428661305561 111817015697322321495979171)
  ·
    refine ⟨167725523545983482243968757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111817015697322321495979171 167725523545983482243968757)
    ·
      refine ⟨15724267832435951460372071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167725523545983482243968757 15724267832435951460372071)
      ·
        refine ⟨23586401748653927190558107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15724267832435951460372071 23586401748653927190558107)
        ·
          refine ⟨35379602622980890785837161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23586401748653927190558107 35379602622980890785837161)
          ·
            refine ⟨26534701967235668089377871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35379602622980890785837161 26534701967235668089377871)
            ·
              refine ⟨39802052950853502134066807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26534701967235668089377871 39802052950853502134066807)
              ·
                refine ⟨59703079426280253201100211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39802052950853502134066807 59703079426280253201100211)
                ·
                  refine ⟨89554619139420379801650317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59703079426280253201100211 89554619139420379801650317)
                  ·
                    refine ⟨33582982177282642425618869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89554619139420379801650317 33582982177282642425618869)
                    ·
                      refine ⟨3148404579120247727401769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33582982177282642425618869 3148404579120247727401769)
                      ·
                        rfl

theorem cell23_6131496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_6131496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131496 prefixEnd_6131496 := by exact prefixLift 6131496
  have htrace : WordTrace (prefixWord ++ tailWord_6131496) baseStart_6131496 baseEnd_6131496 := by
    simpa [prefixWord, tailWord_6131496, baseEnd_6131496] using wordTrace_append hprefix tailTrace_6131496
  have hstable : (prefixWord ++ tailWord_6131496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131496).length < 2 ^ (prefixWord ++ tailWord_6131496).sum := by decide
  have hdescent : baseEnd_6131496 < baseStart_6131496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131516 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 7]
def baseStart_6131516 : Nat := 118140960795 + 6131516 * 2 ^ 59
def prefixEnd_6131516 : Nat := 4983230072969 + 3 ^ 40 * 6131516 * 2
def baseEnd_6131516 : Nat := 349823872081481961016853

theorem tailTrace_6131516 : CollatzResearch.WordTrace tailWord_6131516 prefixEnd_6131516 349823872081481961016853 := by
  unfold tailWord_6131516
  simp only [CollatzResearch.WordTrace]
  refine ⟨111817380427286093203843201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149089840569714790938457601 111817380427286093203843201)
  ·
    refine ⟨83863035320464569902882401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111817380427286093203843201 83863035320464569902882401)
    ·
      refine ⟨62897276490348427427161801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83863035320464569902882401 62897276490348427427161801)
      ·
        refine ⟨47172957367761320570371351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62897276490348427427161801 47172957367761320570371351)
        ·
          refine ⟨70759436051641980855557027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47172957367761320570371351 70759436051641980855557027)
          ·
            refine ⟨106139154077462971283335541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70759436051641980855557027 106139154077462971283335541)
            ·
              refine ⟨9950545694762153557812707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106139154077462971283335541 9950545694762153557812707)
              ·
                refine ⟨14925818542143230336719061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9950545694762153557812707 14925818542143230336719061)
                ·
                  refine ⟨349823872081481961016853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14925818542143230336719061 349823872081481961016853)
                  ·
                    rfl

theorem cell23_6131516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 7].length) (baseStart_6131516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131516 prefixEnd_6131516 := by exact prefixLift 6131516
  have htrace : WordTrace (prefixWord ++ tailWord_6131516) baseStart_6131516 baseEnd_6131516 := by
    simpa [prefixWord, tailWord_6131516, baseEnd_6131516] using wordTrace_append hprefix tailTrace_6131516
  have hstable : (prefixWord ++ tailWord_6131516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131516).length < 2 ^ (prefixWord ++ tailWord_6131516).sum := by decide
  have hdescent : baseEnd_6131516 < baseStart_6131516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131527 : List Nat := [1, 1, 4, 1, 2, 1, 6, 1, 2, 2, 2]
def baseStart_6131527 : Nat := 118140960795 + 6131527 * 2 ^ 59
def prefixEnd_6131527 : Nat := 4983230072969 + 3 ^ 40 * 6131527 * 2
def baseEnd_6131527 : Nat := 3148420497020537106114127

theorem tailTrace_6131527 : CollatzResearch.WordTrace tailWord_6131527 prefixEnd_6131527 3148420497020537106114127 := by
  unfold tailWord_6131527
  simp only [CollatzResearch.WordTrace]
  refine ⟨223635162057532335286336835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149090108038354890190891223 223635162057532335286336835)
  ·
    refine ⟨335452743086298502929505253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223635162057532335286336835 335452743086298502929505253)
    ·
      refine ⟨62897389328680969299282235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335452743086298502929505253 62897389328680969299282235)
      ·
        refine ⟨94346083993021453948923353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62897389328680969299282235 94346083993021453948923353)
        ·
          refine ⟨70759562994766090461692515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94346083993021453948923353 70759562994766090461692515)
          ·
            refine ⟨106139344492149135692538773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70759562994766090461692515 106139344492149135692538773)
            ·
              refine ⟨4975281773069490735587755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106139344492149135692538773 4975281773069490735587755)
              ·
                refine ⟨7462922659604236103381633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4975281773069490735587755 7462922659604236103381633)
                ·
                  refine ⟨5597191994703177077536225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7462922659604236103381633 5597191994703177077536225)
                  ·
                    refine ⟨4197893996027382808152169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5597191994703177077536225 4197893996027382808152169)
                    ·
                      refine ⟨3148420497020537106114127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4197893996027382808152169 3148420497020537106114127)
                      ·
                        rfl

theorem cell23_6131527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_6131527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131527 prefixEnd_6131527 := by exact prefixLift 6131527
  have htrace : WordTrace (prefixWord ++ tailWord_6131527) baseStart_6131527 baseEnd_6131527 := by
    simpa [prefixWord, tailWord_6131527, baseEnd_6131527] using wordTrace_append hprefix tailTrace_6131527
  have hstable : (prefixWord ++ tailWord_6131527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131527).length < 2 ^ (prefixWord ++ tailWord_6131527).sum := by decide
  have hdescent : baseEnd_6131527 < baseStart_6131527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131593 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 3, 4]
def baseStart_6131593 : Nat := 118140960795 + 6131593 * 2 ^ 59
def prefixEnd_6131593 : Nat := 4983230072969 + 3 ^ 40 * 6131593 * 2
def baseEnd_6131593 : Nat := 1049484795581244615962941

theorem tailTrace_6131593 : CollatzResearch.WordTrace tailWord_6131593 prefixEnd_6131593 1049484795581244615962941 := by
  unfold tailWord_6131593
  simp only [CollatzResearch.WordTrace]
  refine ⟨223637569275293228558239433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149091712850195485705492955 223637569275293228558239433)
  ·
    refine ⟨167728176956469921418679575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223637569275293228558239433 167728176956469921418679575)
    ·
      refine ⟨251592265434704882128019363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167728176956469921418679575 251592265434704882128019363)
      ·
        refine ⟨377388398152057323192029045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251592265434704882128019363 377388398152057323192029045)
        ·
          refine ⟨35380162326755374049252723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 377388398152057323192029045 35380162326755374049252723)
          ·
            refine ⟨53070243490133061073879085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35380162326755374049252723 53070243490133061073879085)
            ·
              refine ⟨19901341308799897902704657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53070243490133061073879085 19901341308799897902704657)
              ·
                refine ⟨14926005981599923427028493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19901341308799897902704657 14926005981599923427028493)
                ·
                  refine ⟨5597252243099971285135685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14926005981599923427028493 5597252243099971285135685)
                  ·
                    refine ⟨1049484795581244615962941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5597252243099971285135685 1049484795581244615962941)
                    ·
                      rfl

theorem cell23_6131593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 4].length) (baseStart_6131593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131593 prefixEnd_6131593 := by exact prefixLift 6131593
  have htrace : WordTrace (prefixWord ++ tailWord_6131593) baseStart_6131593 baseEnd_6131593 := by
    simpa [prefixWord, tailWord_6131593, baseEnd_6131593] using wordTrace_append hprefix tailTrace_6131593
  have hstable : (prefixWord ++ tailWord_6131593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131593).length < 2 ^ (prefixWord ++ tailWord_6131593).sum := by decide
  have hdescent : baseEnd_6131593 < baseStart_6131593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131623 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 8]
def baseStart_6131623 : Nat := 118140960795 + 6131623 * 2 ^ 59
def prefixEnd_6131623 : Nat := 4983230072969 + 3 ^ 40 * 6131623 * 2
def baseEnd_6131623 : Nat := 349829976795929858945965

theorem tailTrace_6131623 : CollatzResearch.WordTrace tailWord_6131623 prefixEnd_6131623 349829976795929858945965 := by
  unfold tailWord_6131623
  simp only [CollatzResearch.WordTrace]
  refine ⟨223638663465184543681831523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149092442310123029121221015 223638663465184543681831523)
  ·
    refine ⟨335457995197776815522747285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223638663465184543681831523 335457995197776815522747285)
    ·
      refine ⟨15724593524895788227628779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 335457995197776815522747285 15724593524895788227628779)
      ·
        refine ⟨23586890287343682341443169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15724593524895788227628779 23586890287343682341443169)
        ·
          refine ⟨17690167715507761756082377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23586890287343682341443169 17690167715507761756082377)
          ·
            refine ⟨13267625786630821317061783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17690167715507761756082377 13267625786630821317061783)
            ·
              refine ⟨19901438679946231975592675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13267625786630821317061783 19901438679946231975592675)
              ·
                refine ⟨29852158019919347963389013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19901438679946231975592675 29852158019919347963389013)
                ·
                  refine ⟨349829976795929858945965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29852158019919347963389013 349829976795929858945965)
                  ·
                    rfl

theorem cell23_6131623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 8].length) (baseStart_6131623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131623 prefixEnd_6131623 := by exact prefixLift 6131623
  have htrace : WordTrace (prefixWord ++ tailWord_6131623) baseStart_6131623 baseEnd_6131623 := by
    simpa [prefixWord, tailWord_6131623, baseEnd_6131623] using wordTrace_append hprefix tailTrace_6131623
  have hstable : (prefixWord ++ tailWord_6131623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131623).length < 2 ^ (prefixWord ++ tailWord_6131623).sum := by decide
  have hdescent : baseEnd_6131623 < baseStart_6131623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131643 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 1, 5, 2]
def baseStart_6131643 : Nat := 118140960795 + 6131643 * 2 ^ 59
def prefixEnd_6131643 : Nat := 4983230072969 + 3 ^ 40 * 6131643 * 2
def baseEnd_6131643 : Nat := 3148480060776458652263593

theorem tailTrace_6131643 : CollatzResearch.WordTrace tailWord_6131643 prefixEnd_6131643 3148480060776458652263593 := by
  unfold tailWord_6131643
  simp only [CollatzResearch.WordTrace]
  refine ⟨223639392925112087097559583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149092928616741391398373055 223639392925112087097559583)
  ·
    refine ⟨335459089387668130646339375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223639392925112087097559583 335459089387668130646339375)
    ·
      refine ⟨503188634081502195969509063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335459089387668130646339375 503188634081502195969509063)
      ·
        refine ⟨754782951122253293954263595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503188634081502195969509063 754782951122253293954263595)
        ·
          refine ⟨1132174426683379940931395393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754782951122253293954263595 1132174426683379940931395393)
          ·
            refine ⟨849130820012534955698546545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1132174426683379940931395393 849130820012534955698546545)
            ·
              refine ⟨636848115009401216773909909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849130820012534955698546545 636848115009401216773909909)
              ·
                refine ⟨29852255391065682036277027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 636848115009401216773909909 29852255391065682036277027)
                ·
                  refine ⟨44778383086598523054415541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29852255391065682036277027 44778383086598523054415541)
                  ·
                    refine ⟨4197973414368611536351457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44778383086598523054415541 4197973414368611536351457)
                    ·
                      refine ⟨3148480060776458652263593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4197973414368611536351457 3148480060776458652263593)
                      ·
                        rfl

theorem cell23_6131643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 5, 2].length) (baseStart_6131643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131643 prefixEnd_6131643 := by exact prefixLift 6131643
  have htrace : WordTrace (prefixWord ++ tailWord_6131643) baseStart_6131643 baseEnd_6131643 := by
    simpa [prefixWord, tailWord_6131643, baseEnd_6131643] using wordTrace_append hprefix tailTrace_6131643
  have hstable : (prefixWord ++ tailWord_6131643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131643).length < 2 ^ (prefixWord ++ tailWord_6131643).sum := by decide
  have hdescent : baseEnd_6131643 < baseStart_6131643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131660 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 1, 5, 2]
def baseStart_6131660 : Nat := 118140960795 + 6131660 * 2 ^ 59
def prefixEnd_6131660 : Nat := 4983230072969 + 3 ^ 40 * 6131660 * 2
def baseEnd_6131660 : Nat := 3148488789947585085751015

theorem tailTrace_6131660 : CollatzResearch.WordTrace tailWord_6131660 prefixEnd_6131660 3148488789947585085751015 := by
  unfold tailWord_6131660
  simp only [CollatzResearch.WordTrace]
  refine ⟨111820006483025249500464217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149093341977366999333952289 111820006483025249500464217)
  ·
    refine ⟨83865004862268937125348163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111820006483025249500464217 83865004862268937125348163)
    ·
      refine ⟨125797507293403405688022245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83865004862268937125348163 125797507293403405688022245)
      ·
        refine ⟨23587032617513138566504171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125797507293403405688022245 23587032617513138566504171)
        ·
          refine ⟨35380548926269707849756257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23587032617513138566504171 35380548926269707849756257)
          ·
            refine ⟨26535411694702280887317193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35380548926269707849756257 26535411694702280887317193)
            ·
              refine ⟨19901558771026710665487895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26535411694702280887317193 19901558771026710665487895)
              ·
                refine ⟨29852338156540065998231843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19901558771026710665487895 29852338156540065998231843)
                ·
                  refine ⟨44778507234810098997347765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29852338156540065998231843 44778507234810098997347765)
                  ·
                    refine ⟨4197985053263446781001353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44778507234810098997347765 4197985053263446781001353)
                    ·
                      refine ⟨3148488789947585085751015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4197985053263446781001353 3148488789947585085751015)
                      ·
                        rfl

theorem cell23_6131660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_6131660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131660 prefixEnd_6131660 := by exact prefixLift 6131660
  have htrace : WordTrace (prefixWord ++ tailWord_6131660) baseStart_6131660 baseEnd_6131660 := by
    simpa [prefixWord, tailWord_6131660, baseEnd_6131660] using wordTrace_append hprefix tailTrace_6131660
  have hstable : (prefixWord ++ tailWord_6131660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131660).length < 2 ^ (prefixWord ++ tailWord_6131660).sum := by decide
  have hdescent : baseEnd_6131660 < baseStart_6131660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131684 : List Nat := [2, 3, 1, 1, 1, 1, 7, 2, 1, 1, 3]
def baseStart_6131684 : Nat := 118140960795 + 6131684 * 2 ^ 59
def prefixEnd_6131684 : Nat := 4983230072969 + 3 ^ 40 * 6131684 * 2
def baseEnd_6131684 : Nat := 3148501113483292991850905

theorem tailTrace_6131684 : CollatzResearch.WordTrace tailWord_6131684 prefixEnd_6131684 3148501113483292991850905 := by
  unfold tailWord_6131684
  simp only [CollatzResearch.WordTrace]
  refine ⟨111820444158981775549901053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149093925545309034066534737 111820444158981775549901053)
  ·
    refine ⟨41932666559618165831212895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111820444158981775549901053 41932666559618165831212895)
    ·
      refine ⟨62898999839427248746819343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41932666559618165831212895 62898999839427248746819343)
      ·
        refine ⟨94348499759140873120229015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62898999839427248746819343 94348499759140873120229015)
        ·
          refine ⟨141522749638711309680343523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94348499759140873120229015 141522749638711309680343523)
          ·
            refine ⟨212284124458066964520515285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141522749638711309680343523 212284124458066964520515285)
            ·
              refine ⟨4975409166985944480949577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 212284124458066964520515285 4975409166985944480949577)
              ·
                refine ⟨3731556875239458360712183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4975409166985944480949577 3731556875239458360712183)
                ·
                  refine ⟨5597335312859187541068275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3731556875239458360712183 5597335312859187541068275)
                  ·
                    refine ⟨8396002969288781311602413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5597335312859187541068275 8396002969288781311602413)
                    ·
                      refine ⟨3148501113483292991850905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8396002969288781311602413 3148501113483292991850905)
                      ·
                        rfl

theorem cell23_6131684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_6131684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131684 prefixEnd_6131684 := by exact prefixLift 6131684
  have htrace : WordTrace (prefixWord ++ tailWord_6131684) baseStart_6131684 baseEnd_6131684 := by
    simpa [prefixWord, tailWord_6131684, baseEnd_6131684] using wordTrace_append hprefix tailTrace_6131684
  have hstable : (prefixWord ++ tailWord_6131684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131684).length < 2 ^ (prefixWord ++ tailWord_6131684).sum := by decide
  have hdescent : baseEnd_6131684 < baseStart_6131684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131696 : List Nat := [2, 1, 1, 1, 3, 2, 3, 10]
def baseStart_6131696 : Nat := 118140960795 + 6131696 * 2 ^ 59
def prefixEnd_6131696 : Nat := 4983230072969 + 3 ^ 40 * 6131696 * 2
def baseEnd_6131696 : Nat := 116611380564857294255587

theorem tailTrace_6131696 : CollatzResearch.WordTrace tailWord_6131696 prefixEnd_6131696 116611380564857294255587 := by
  unfold tailWord_6131696
  simp only [CollatzResearch.WordTrace]
  refine ⟨111820662996960038574619471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149094217329280051432825961 111820662996960038574619471)
  ·
    refine ⟨167730994495440057861929207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111820662996960038574619471 167730994495440057861929207)
    ·
      refine ⟨251596491743160086792893811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167730994495440057861929207 251596491743160086792893811)
      ·
        refine ⟨377394737614740130189340717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251596491743160086792893811 377394737614740130189340717)
        ·
          refine ⟨141523026605527548821002769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 377394737614740130189340717 141523026605527548821002769)
          ·
            refine ⟨106142269954145661615752077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141523026605527548821002769 106142269954145661615752077)
            ·
              refine ⟨39803351232804623105907029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106142269954145661615752077 39803351232804623105907029)
              ·
                refine ⟨116611380564857294255587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39803351232804623105907029 116611380564857294255587)
                ·
                  rfl

theorem cell23_6131696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 10].length) (baseStart_6131696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131696 prefixEnd_6131696 := by exact prefixLift 6131696
  have htrace : WordTrace (prefixWord ++ tailWord_6131696) baseStart_6131696 baseEnd_6131696 := by
    simpa [prefixWord, tailWord_6131696, baseEnd_6131696] using wordTrace_append hprefix tailTrace_6131696
  have hstable : (prefixWord ++ tailWord_6131696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131696).length < 2 ^ (prefixWord ++ tailWord_6131696).sum := by decide
  have hdescent : baseEnd_6131696 < baseStart_6131696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131724 : List Nat := [2, 2, 1, 2, 3, 1, 2, 5, 1, 2, 2]
def baseStart_6131724 : Nat := 118140960795 + 6131724 * 2 ^ 59
def prefixEnd_6131724 : Nat := 4983230072969 + 3 ^ 40 * 6131724 * 2
def baseEnd_6131724 : Nat := 3148521652709472835350721

theorem tailTrace_6131724 : CollatzResearch.WordTrace tailWord_6131724 prefixEnd_6131724 3148521652709472835350721 := by
  unfold tailWord_6131724
  simp only [CollatzResearch.WordTrace]
  refine ⟨111821173618909318965629113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149094898158545758620838817 111821173618909318965629113)
  ·
    refine ⟨83865880214181989224221835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111821173618909318965629113 83865880214181989224221835)
    ·
      refine ⟨125798820321272983836332753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83865880214181989224221835 125798820321272983836332753)
      ·
        refine ⟨94349115240954737877249565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125798820321272983836332753 94349115240954737877249565)
        ·
          refine ⟨35380918215358026703968587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94349115240954737877249565 35380918215358026703968587)
          ·
            refine ⟨53071377323037040055952881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35380918215358026703968587 53071377323037040055952881)
            ·
              refine ⟨39803532992277780041964661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53071377323037040055952881 39803532992277780041964661)
              ·
                refine ⟨3731581218026041878934187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39803532992277780041964661 3731581218026041878934187)
                ·
                  refine ⟨5597371827039062818401281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3731581218026041878934187 5597371827039062818401281)
                  ·
                    refine ⟨4198028870279297113800961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5597371827039062818401281 4198028870279297113800961)
                    ·
                      refine ⟨3148521652709472835350721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4198028870279297113800961 3148521652709472835350721)
                      ·
                        rfl

theorem cell23_6131724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_6131724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131724 prefixEnd_6131724 := by exact prefixLift 6131724
  have htrace : WordTrace (prefixWord ++ tailWord_6131724) baseStart_6131724 baseEnd_6131724 := by
    simpa [prefixWord, tailWord_6131724, baseEnd_6131724] using wordTrace_append hprefix tailTrace_6131724
  have hstable : (prefixWord ++ tailWord_6131724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131724).length < 2 ^ (prefixWord ++ tailWord_6131724).sum := by decide
  have hdescent : baseEnd_6131724 < baseStart_6131724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131741 : List Nat := [1, 4, 2, 2, 2, 2, 1, 4, 1, 2, 2]
def baseStart_6131741 : Nat := 118140960795 + 6131741 * 2 ^ 59
def prefixEnd_6131741 : Nat := 4983230072969 + 3 ^ 40 * 6131741 * 2
def baseEnd_6131741 : Nat := 3148530381880599268838143

theorem tailTrace_6131741 : CollatzResearch.WordTrace tailWord_6131741 prefixEnd_6131741 3148530381880599268838143 := by
  unfold tailWord_6131741
  simp only [CollatzResearch.WordTrace]
  refine ⟨223642967278757049834627077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149095311519171366556418051 223642967278757049834627077)
  ·
    refine ⟨41933056364766946843992577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223642967278757049834627077 41933056364766946843992577)
    ·
      refine ⟨31449792273575210132994433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41933056364766946843992577 31449792273575210132994433)
      ·
        refine ⟨23587344205181407599745825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31449792273575210132994433 23587344205181407599745825)
        ·
          refine ⟨17690508153886055699809369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23587344205181407599745825 17690508153886055699809369)
          ·
            refine ⟨13267881115414541774857027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17690508153886055699809369 13267881115414541774857027)
            ·
              refine ⟨19901821673121812662285541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13267881115414541774857027 19901821673121812662285541)
              ·
                refine ⟨3731591563710339874178539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19901821673121812662285541 3731591563710339874178539)
                ·
                  refine ⟨5597387345565509811267809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3731591563710339874178539 5597387345565509811267809)
                  ·
                    refine ⟨4198040509174132358450857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5597387345565509811267809 4198040509174132358450857)
                    ·
                      refine ⟨3148530381880599268838143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4198040509174132358450857 3148530381880599268838143)
                      ·
                        rfl

theorem cell23_6131741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_6131741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131741 prefixEnd_6131741 := by exact prefixLift 6131741
  have htrace : WordTrace (prefixWord ++ tailWord_6131741) baseStart_6131741 baseEnd_6131741 := by
    simpa [prefixWord, tailWord_6131741, baseEnd_6131741] using wordTrace_append hprefix tailTrace_6131741
  have hstable : (prefixWord ++ tailWord_6131741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131741).length < 2 ^ (prefixWord ++ tailWord_6131741).sum := by decide
  have hdescent : baseEnd_6131741 < baseStart_6131741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131773 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 1, 8]
def baseStart_6131773 : Nat := 118140960795 + 6131773 * 2 ^ 59
def prefixEnd_6131773 : Nat := 4983230072969 + 3 ^ 40 * 6131773 * 2
def baseEnd_6131773 : Nat := 1049515604420514381212665

theorem tailTrace_6131773 : CollatzResearch.WordTrace tailWord_6131773 prefixEnd_6131773 1049515604420514381212665 := by
  unfold tailWord_6131773
  simp only [CollatzResearch.WordTrace]
  refine ⟨223644134414641119299791973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149096089609760746199861315 223644134414641119299791973)
  ·
    refine ⟨41933275202745209868710995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223644134414641119299791973 41933275202745209868710995)
    ·
      refine ⟨62899912804117814803066493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41933275202745209868710995 62899912804117814803066493)
      ·
        refine ⟨23587467301544180551149935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62899912804117814803066493 23587467301544180551149935)
        ·
          refine ⟨35381200952316270826724903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23587467301544180551149935 35381200952316270826724903)
          ·
            refine ⟨53071801428474406240087355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35381200952316270826724903 53071801428474406240087355)
            ·
              refine ⟨79607702142711609360131033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53071801428474406240087355 79607702142711609360131033)
              ·
                refine ⟨59705776607033707020098275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79607702142711609360131033 59705776607033707020098275)
                ·
                  refine ⟨89558664910550560530147413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59705776607033707020098275 89558664910550560530147413)
                  ·
                    refine ⟨1049515604420514381212665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89558664910550560530147413 1049515604420514381212665)
                    ·
                      rfl

theorem cell23_6131773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_6131773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131773 prefixEnd_6131773 := by exact prefixLift 6131773
  have htrace : WordTrace (prefixWord ++ tailWord_6131773) baseStart_6131773 baseEnd_6131773 := by
    simpa [prefixWord, tailWord_6131773, baseEnd_6131773] using wordTrace_append hprefix tailTrace_6131773
  have hstable : (prefixWord ++ tailWord_6131773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131773).length < 2 ^ (prefixWord ++ tailWord_6131773).sum := by decide
  have hdescent : baseEnd_6131773 < baseStart_6131773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131783 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_6131783 : Nat := 118140960795 + 6131783 * 2 ^ 59
def prefixEnd_6131783 : Nat := 4983230072969 + 3 ^ 40 * 6131783 * 2
def baseEnd_6131783 : Nat := 3148551948068088104512949

theorem tailTrace_6131783 : CollatzResearch.WordTrace tailWord_6131783 prefixEnd_6131783 3148551948068088104512949 := by
  unfold tailWord_6131783
  simp only [CollatzResearch.WordTrace]
  refine ⟨223644499144604891007656003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149096332763069927338437335 223644499144604891007656003)
  ·
    refine ⟨335466748716907336511484005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223644499144604891007656003 335466748716907336511484005)
    ·
      refine ⟨62900015384420125595903251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335466748716907336511484005 62900015384420125595903251)
      ·
        refine ⟨94350023076630188393854877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62900015384420125595903251 94350023076630188393854877)
        ·
          refine ⟨35381258653736320647695579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94350023076630188393854877 35381258653736320647695579)
          ·
            refine ⟨53071887980604480971543369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35381258653736320647695579 53071887980604480971543369)
            ·
              refine ⟨39803915985453360728657527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53071887980604480971543369 39803915985453360728657527)
              ·
                refine ⟨59705873978180041092986291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39803915985453360728657527 59705873978180041092986291)
                ·
                  refine ⟨89558810967270061639479437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59705873978180041092986291 89558810967270061639479437)
                  ·
                    refine ⟨33584554112726273114804789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89558810967270061639479437 33584554112726273114804789)
                    ·
                      refine ⟨3148551948068088104512949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33584554112726273114804789 3148551948068088104512949)
                      ·
                        rfl

theorem cell23_6131783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_6131783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131783 prefixEnd_6131783 := by exact prefixLift 6131783
  have htrace : WordTrace (prefixWord ++ tailWord_6131783) baseStart_6131783 baseEnd_6131783 := by
    simpa [prefixWord, tailWord_6131783, baseEnd_6131783] using wordTrace_append hprefix tailTrace_6131783
  have hstable : (prefixWord ++ tailWord_6131783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131783).length < 2 ^ (prefixWord ++ tailWord_6131783).sum := by decide
  have hdescent : baseEnd_6131783 < baseStart_6131783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131837 : List Nat := [1, 4, 1, 1, 3, 2, 3, 3, 5]
def baseStart_6131837 : Nat := 118140960795 + 6131837 * 2 ^ 59
def prefixEnd_6131837 : Nat := 4983230072969 + 3 ^ 40 * 6131837 * 2
def baseEnd_6131837 : Nat := 349842186224825654804189

theorem tailTrace_6131837 : CollatzResearch.WordTrace tailWord_6131837 prefixEnd_6131837 349842186224825654804189 := by
  unfold tailWord_6131837
  simp only [CollatzResearch.WordTrace]
  refine ⟨223646468686409258230121765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149097645790939505486747843 223646468686409258230121765)
  ·
    refine ⟨41933712878701735918147831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223646468686409258230121765 41933712878701735918147831)
    ·
      refine ⟨62900569318052603877221747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41933712878701735918147831 62900569318052603877221747)
      ·
        refine ⟨94350853977078905815832621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62900569318052603877221747 94350853977078905815832621)
        ·
          refine ⟨35381570241404589680937233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94350853977078905815832621 35381570241404589680937233)
          ·
            refine ⟨26536177681053442260702925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35381570241404589680937233 26536177681053442260702925)
            ·
              refine ⟨9951066630395040847763597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26536177681053442260702925 9951066630395040847763597)
              ·
                refine ⟨3731649986398140317911349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9951066630395040847763597 3731649986398140317911349)
                ·
                  refine ⟨349842186224825654804189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3731649986398140317911349 349842186224825654804189)
                  ·
                    rfl

theorem cell23_6131837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_6131837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131837 prefixEnd_6131837 := by exact prefixLift 6131837
  have htrace : WordTrace (prefixWord ++ tailWord_6131837) baseStart_6131837 baseEnd_6131837 := by
    simpa [prefixWord, tailWord_6131837, baseEnd_6131837] using wordTrace_append hprefix tailTrace_6131837
  have hstable : (prefixWord ++ tailWord_6131837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131837).length < 2 ^ (prefixWord ++ tailWord_6131837).sum := by decide
  have hdescent : baseEnd_6131837 < baseStart_6131837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131840 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 1, 7, 2]
def baseStart_6131840 : Nat := 118140960795 + 6131840 * 2 ^ 59
def prefixEnd_6131840 : Nat := 4983230072969 + 3 ^ 40 * 6131840 * 2
def baseEnd_6131840 : Nat := 3148581216465394381500187

theorem tailTrace_6131840 : CollatzResearch.WordTrace tailWord_6131840 prefixEnd_6131840 3148581216465394381500187 := by
  unfold tailWord_6131840
  simp only [CollatzResearch.WordTrace]
  refine ⟨111823289052699194871240487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149097718736932259828320649 111823289052699194871240487)
  ·
    refine ⟨167734933579048792306860731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111823289052699194871240487 167734933579048792306860731)
    ·
      refine ⟨251602400368573188460291097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167734933579048792306860731 251602400368573188460291097)
      ·
        refine ⟨188701800276429891345218323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251602400368573188460291097 188701800276429891345218323)
        ·
          refine ⟨283052700414644837017827485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188701800276429891345218323 283052700414644837017827485)
          ·
            refine ⟨106144762655491813881685307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283052700414644837017827485 106144762655491813881685307)
            ·
              refine ⟨159217143983237720822527961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106144762655491813881685307 159217143983237720822527961)
              ·
                refine ⟨119412857987428290616895971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159217143983237720822527961 119412857987428290616895971)
                ·
                  refine ⟨179119286981142435925343957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119412857987428290616895971 179119286981142435925343957)
                  ·
                    refine ⟨4198108288620525842000249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 179119286981142435925343957 4198108288620525842000249)
                    ·
                      refine ⟨3148581216465394381500187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4198108288620525842000249 3148581216465394381500187)
                      ·
                        rfl

theorem cell23_6131840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 7, 2].length) (baseStart_6131840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131840 prefixEnd_6131840 := by exact prefixLift 6131840
  have htrace : WordTrace (prefixWord ++ tailWord_6131840) baseStart_6131840 baseEnd_6131840 := by
    simpa [prefixWord, tailWord_6131840, baseEnd_6131840] using wordTrace_append hprefix tailTrace_6131840
  have hstable : (prefixWord ++ tailWord_6131840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131840).length < 2 ^ (prefixWord ++ tailWord_6131840).sum := by decide
  have hdescent : baseEnd_6131840 < baseStart_6131840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131850 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 4, 5]
def baseStart_6131850 : Nat := 118140960795 + 6131850 * 2 ^ 59
def prefixEnd_6131850 : Nat := 4983230072969 + 3 ^ 40 * 6131850 * 2
def baseEnd_6131850 : Nat := 1049528783757313114125047

theorem tailTrace_6131850 : CollatzResearch.WordTrace tailWord_6131850 prefixEnd_6131850 1049528783757313114125047 := by
  unfold tailWord_6131850
  simp only [CollatzResearch.WordTrace]
  refine ⟨55911735708840540362586251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149097961890241440966896669 55911735708840540362586251)
  ·
    refine ⟨83867603563260810543879377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55911735708840540362586251 83867603563260810543879377)
    ·
      refine ⟨62900702672445607907909533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83867603563260810543879377 62900702672445607907909533)
      ·
        refine ⟨23587763502167102965466075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62900702672445607907909533 23587763502167102965466075)
        ·
          refine ⟨35381645253250654448199113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23587763502167102965466075 35381645253250654448199113)
          ·
            refine ⟨26536233939937990836149335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35381645253250654448199113 26536233939937990836149335)
            ·
              refine ⟨39804350909906986254224003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26536233939937990836149335 39804350909906986254224003)
              ·
                refine ⟨59706526364860479381336005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39804350909906986254224003 59706526364860479381336005)
                ·
                  refine ⟨11194973693411339884000501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59706526364860479381336005 11194973693411339884000501)
                  ·
                    refine ⟨1049528783757313114125047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11194973693411339884000501 1049528783757313114125047)
                    ·
                      rfl

theorem cell23_6131850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_6131850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131850 prefixEnd_6131850 := by exact prefixLift 6131850
  have htrace : WordTrace (prefixWord ++ tailWord_6131850) baseStart_6131850 baseEnd_6131850 := by
    simpa [prefixWord, tailWord_6131850, baseEnd_6131850] using wordTrace_append hprefix tailTrace_6131850
  have hstable : (prefixWord ++ tailWord_6131850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131850).length < 2 ^ (prefixWord ++ tailWord_6131850).sum := by decide
  have hdescent : baseEnd_6131850 < baseStart_6131850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131854 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 7]
def baseStart_6131854 : Nat := 118140960795 + 6131854 * 2 ^ 59
def prefixEnd_6131854 : Nat := 4983230072969 + 3 ^ 40 * 6131854 * 2
def baseEnd_6131854 : Nat := 349843156132728591858347

theorem tailTrace_6131854 : CollatzResearch.WordTrace tailWord_6131854 prefixEnd_6131854 349843156132728591858347 := by
  unfold tailWord_6131854
  simp only [CollatzResearch.WordTrace]
  refine ⟨27955886090918458766686327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149098059151565113422327077 27955886090918458766686327)
  ·
    refine ⟨41933829136377688150029491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27955886090918458766686327 41933829136377688150029491)
    ·
      refine ⟨62900743704566532225044237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41933829136377688150029491 62900743704566532225044237)
      ·
        refine ⟨23587778889212449584391589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62900743704566532225044237 23587778889212449584391589)
        ·
          refine ⟨4422708541727334297073423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23587778889212449584391589 4422708541727334297073423)
          ·
            refine ⟨6634062812591001445610135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4422708541727334297073423 6634062812591001445610135)
            ·
              refine ⟨9951094218886502168415203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6634062812591001445610135 9951094218886502168415203)
              ·
                refine ⟨14926641328329753252622805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9951094218886502168415203 14926641328329753252622805)
                ·
                  refine ⟨349843156132728591858347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14926641328329753252622805 349843156132728591858347)
                  ·
                    rfl

theorem cell23_6131854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_6131854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131854 prefixEnd_6131854 := by exact prefixLift 6131854
  have htrace : WordTrace (prefixWord ++ tailWord_6131854) baseStart_6131854 baseEnd_6131854 := by
    simpa [prefixWord, tailWord_6131854, baseEnd_6131854] using wordTrace_append hprefix tailTrace_6131854
  have hstable : (prefixWord ++ tailWord_6131854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131854).length < 2 ^ (prefixWord ++ tailWord_6131854).sum := by decide
  have hdescent : baseEnd_6131854 < baseStart_6131854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131914 : List Nat := [3, 1, 2, 1, 3, 1, 3, 4, 1, 4]
def baseStart_6131914 : Nat := 118140960795 + 6131914 * 2 ^ 59
def prefixEnd_6131914 : Nat := 4983230072969 + 3 ^ 40 * 6131914 * 2
def baseEnd_6131914 : Nat := 1049539738011275697324949

theorem tailTrace_6131914 : CollatzResearch.WordTrace tailWord_6131914 prefixEnd_6131914 1049539738011275697324949 := by
  unfold tailWord_6131914
  simp only [CollatzResearch.WordTrace]
  refine ⟨55912319276782575095168699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149099518071420200253783197 55912319276782575095168699)
  ·
    refine ⟨83868478915173862642753049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55912319276782575095168699 83868478915173862642753049)
    ·
      refine ⟨62901359186380396982064787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83868478915173862642753049 62901359186380396982064787)
      ·
        refine ⟨94352038779570595473097181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62901359186380396982064787 94352038779570595473097181)
        ·
          refine ⟨35382014542338973302411443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94352038779570595473097181 35382014542338973302411443)
          ·
            refine ⟨53073021813508459953617165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35382014542338973302411443 53073021813508459953617165)
            ·
              refine ⟨19902383180065672482606437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53073021813508459953617165 19902383180065672482606437)
              ·
                refine ⟨3731696846262313590488707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19902383180065672482606437 3731696846262313590488707)
                ·
                  refine ⟨5597545269393470385733061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3731696846262313590488707 5597545269393470385733061)
                  ·
                    refine ⟨1049539738011275697324949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5597545269393470385733061 1049539738011275697324949)
                    ·
                      rfl

theorem cell23_6131914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_6131914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131914 prefixEnd_6131914 := by exact prefixLift 6131914
  have htrace : WordTrace (prefixWord ++ tailWord_6131914) baseStart_6131914 baseEnd_6131914 := by
    simpa [prefixWord, tailWord_6131914, baseEnd_6131914] using wordTrace_append hprefix tailTrace_6131914
  have hstable : (prefixWord ++ tailWord_6131914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131914).length < 2 ^ (prefixWord ++ tailWord_6131914).sum := by decide
  have hdescent : baseEnd_6131914 < baseStart_6131914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131923 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 1, 11]
def baseStart_6131923 : Nat := 118140960795 + 6131923 * 2 ^ 59
def prefixEnd_6131923 : Nat := 4983230072969 + 3 ^ 40 * 6131923 * 2
def baseEnd_6131923 : Nat := 1049541278453239185587435

theorem tailTrace_6131923 : CollatzResearch.WordTrace tailWord_6131923 prefixEnd_6131923 1049541278453239185587435 := by
  unfold tailWord_6131923
  simp only [CollatzResearch.WordTrace]
  refine ⟨223649605364097694917752423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149099736909398463278501615 223649605364097694917752423)
  ·
    refine ⟨335474408046146542376628635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223649605364097694917752423 335474408046146542376628635)
    ·
      refine ⟨503211612069219813564942953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335474408046146542376628635 503211612069219813564942953)
      ·
        refine ⟨377408709051914860173707215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503211612069219813564942953 377408709051914860173707215)
        ·
          refine ⟨566113063577872290260560823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377408709051914860173707215 566113063577872290260560823)
          ·
            refine ⟨849169595366808435390841235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566113063577872290260560823 849169595366808435390841235)
            ·
              refine ⟨1273754393050212653086261853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849169595366808435390841235 1273754393050212653086261853)
              ·
                refine ⟨477657897393829744907348195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1273754393050212653086261853 477657897393829744907348195)
                ·
                  refine ⟨716486846090744617361022293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477657897393829744907348195 716486846090744617361022293)
                  ·
                    refine ⟨1049541278453239185587435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 716486846090744617361022293 1049541278453239185587435)
                    ·
                      rfl

theorem cell23_6131923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 11].length) (baseStart_6131923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131923 prefixEnd_6131923 := by exact prefixLift 6131923
  have htrace : WordTrace (prefixWord ++ tailWord_6131923) baseStart_6131923 baseEnd_6131923 := by
    simpa [prefixWord, tailWord_6131923, baseEnd_6131923] using wordTrace_append hprefix tailTrace_6131923
  have hstable : (prefixWord ++ tailWord_6131923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131923).length < 2 ^ (prefixWord ++ tailWord_6131923).sum := by decide
  have hdescent : baseEnd_6131923 < baseStart_6131923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131947 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 1, 5, 2]
def baseStart_6131947 : Nat := 118140960795 + 6131947 * 2 ^ 59
def prefixEnd_6131947 : Nat := 4983230072969 + 3 ^ 40 * 6131947 * 2
def baseEnd_6131947 : Nat := 3148636158895425462862195

theorem tailTrace_6131947 : CollatzResearch.WordTrace tailWord_6131947 prefixEnd_6131947 3148636158895425462862195 := by
  unfold tailWord_6131947
  simp only [CollatzResearch.WordTrace]
  refine ⟨223650480716010747016626095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149100320477340498011084063 223650480716010747016626095)
  ·
    refine ⟨335475721074016120524939143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223650480716010747016626095 335475721074016120524939143)
    ·
      refine ⟨503213581611024180787408715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335475721074016120524939143 503213581611024180787408715)
      ·
        refine ⟨754820372416536271181113073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503213581611024180787408715 754820372416536271181113073)
        ·
          refine ⟨566115279312402203385834805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 754820372416536271181113073 566115279312402203385834805)
          ·
            refine ⟨53073307435537706567422013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 566115279312402203385834805 53073307435537706567422013)
            ·
              refine ⟨19902490288326639962783255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53073307435537706567422013 19902490288326639962783255)
              ·
                refine ⟨29853735432489959944174883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19902490288326639962783255 29853735432489959944174883)
                ·
                  refine ⟨44780603148734939916262325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29853735432489959944174883 44780603148734939916262325)
                  ·
                    refine ⟨4198181545193900617149593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44780603148734939916262325 4198181545193900617149593)
                    ·
                      refine ⟨3148636158895425462862195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4198181545193900617149593 3148636158895425462862195)
                      ·
                        rfl

theorem cell23_6131947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 5, 2].length) (baseStart_6131947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131947 prefixEnd_6131947 := by exact prefixLift 6131947
  have htrace : WordTrace (prefixWord ++ tailWord_6131947) baseStart_6131947 baseEnd_6131947 := by
    simpa [prefixWord, tailWord_6131947, baseEnd_6131947] using wordTrace_append hprefix tailTrace_6131947
  have hstable : (prefixWord ++ tailWord_6131947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131947).length < 2 ^ (prefixWord ++ tailWord_6131947).sum := by decide
  have hdescent : baseEnd_6131947 < baseStart_6131947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131950 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_6131950 : Nat := 118140960795 + 6131950 * 2 ^ 59
def prefixEnd_6131950 : Nat := 4983230072969 + 3 ^ 40 * 6131950 * 2
def baseEnd_6131950 : Nat := 3148637699337388951124681

theorem tailTrace_6131950 : CollatzResearch.WordTrace tailWord_6131950 prefixEnd_6131950 3148637699337388951124681 := by
  unfold tailWord_6131950
  simp only [CollatzResearch.WordTrace]
  refine ⟨27956323766874984816123163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149100393423333252352656869 27956323766874984816123163)
  ·
    refine ⟨41934485650312477224184745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27956323766874984816123163 41934485650312477224184745)
    ·
      refine ⟨31450864237734357918138559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41934485650312477224184745 31450864237734357918138559)
      ·
        refine ⟨47176296356601536877207839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31450864237734357918138559 47176296356601536877207839)
        ·
          refine ⟨70764444534902305315811759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47176296356601536877207839 70764444534902305315811759)
          ·
            refine ⟨106146666802353457973717639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70764444534902305315811759 106146666802353457973717639)
            ·
              refine ⟨159220000203530186960576459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106146666802353457973717639 159220000203530186960576459)
              ·
                refine ⟨238830000305295280440864689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159220000203530186960576459 238830000305295280440864689)
                ·
                  refine ⟨179122500228971460330648517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238830000305295280440864689 179122500228971460330648517)
                  ·
                    refine ⟨33585468792932148811996597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 179122500228971460330648517 33585468792932148811996597)
                    ·
                      refine ⟨3148637699337388951124681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33585468792932148811996597 3148637699337388951124681)
                      ·
                        rfl

theorem cell23_6131950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_6131950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131950 prefixEnd_6131950 := by exact prefixLift 6131950
  have htrace : WordTrace (prefixWord ++ tailWord_6131950) baseStart_6131950 baseEnd_6131950 := by
    simpa [prefixWord, tailWord_6131950, baseEnd_6131950] using wordTrace_append hprefix tailTrace_6131950
  have hstable : (prefixWord ++ tailWord_6131950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131950).length < 2 ^ (prefixWord ++ tailWord_6131950).sum := by decide
  have hdescent : baseEnd_6131950 < baseStart_6131950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6131987 : List Nat := [1, 1, 1, 2, 1, 3, 1, 7, 2, 4]
def baseStart_6131987 : Nat := 118140960795 + 6131987 * 2 ^ 59
def prefixEnd_6131987 : Nat := 4983230072969 + 3 ^ 40 * 6131987 * 2
def baseEnd_6131987 : Nat := 1049552232707201768787337

theorem tailTrace_6131987 : CollatzResearch.WordTrace tailWord_6131987 prefixEnd_6131987 1049552232707201768787337 := by
  unfold tailWord_6131987
  simp only [CollatzResearch.WordTrace]
  refine ⟨223651939635865833848082215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149101293090577222565388143 223651939635865833848082215)
  ·
    refine ⟨335477909453798750772123323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223651939635865833848082215 335477909453798750772123323)
    ·
      refine ⟨503216864180698126158184985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335477909453798750772123323 503216864180698126158184985)
      ·
        refine ⟨377412648135523594618638739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503216864180698126158184985 377412648135523594618638739)
        ·
          refine ⟨566118972203285391927958109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377412648135523594618638739 566118972203285391927958109)
          ·
            refine ⟨212294614576232021972984291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 566118972203285391927958109 212294614576232021972984291)
            ·
              refine ⟨318441921864348032959476437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212294614576232021972984291 318441921864348032959476437)
              ·
                refine ⟨7463482543695657022487729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 318441921864348032959476437 7463482543695657022487729)
                ·
                  refine ⟨5597611907771742766865797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7463482543695657022487729 5597611907771742766865797)
                  ·
                    refine ⟨1049552232707201768787337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5597611907771742766865797 1049552232707201768787337)
                    ·
                      rfl

theorem cell23_6131987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 4].length) (baseStart_6131987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6131987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6131987 prefixEnd_6131987 := by exact prefixLift 6131987
  have htrace : WordTrace (prefixWord ++ tailWord_6131987) baseStart_6131987 baseEnd_6131987 := by
    simpa [prefixWord, tailWord_6131987, baseEnd_6131987] using wordTrace_append hprefix tailTrace_6131987
  have hstable : (prefixWord ++ tailWord_6131987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6131987).length < 2 ^ (prefixWord ++ tailWord_6131987).sum := by decide
  have hdescent : baseEnd_6131987 < baseStart_6131987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6131987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132005 : List Nat := [1, 3, 1, 2, 6, 1, 1, 3, 1, 1, 3]
def baseStart_6132005 : Nat := 118140960795 + 6132005 * 2 ^ 59
def prefixEnd_6132005 : Nat := 4983230072969 + 3 ^ 40 * 6132005 * 2
def baseEnd_6132005 : Nat := 3148665940773386235936929

theorem tailTrace_6132005 : CollatzResearch.WordTrace tailWord_6132005 prefixEnd_6132005 3148665940773386235936929 := by
  unfold tailWord_6132005
  simp only [CollatzResearch.WordTrace]
  refine ⟨223652596149800622922237469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149101730766533748614824979 223652596149800622922237469)
  ·
    refine ⟨83869723556175233595839051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223652596149800622922237469 83869723556175233595839051)
    ·
      refine ⟨125804585334262850393758577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83869723556175233595839051 125804585334262850393758577)
      ·
        refine ⟨94353439000697137795318933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125804585334262850393758577 94353439000697137795318933)
        ·
          refine ⟨4422817453157678334155575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94353439000697137795318933 4422817453157678334155575)
          ·
            refine ⟨6634226179736517501233363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4422817453157678334155575 6634226179736517501233363)
            ·
              refine ⟨9951339269604776251850045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6634226179736517501233363 9951339269604776251850045)
              ·
                refine ⟨3731752226101791094443767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9951339269604776251850045 3731752226101791094443767)
                ·
                  refine ⟨5597628339152686641665651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3731752226101791094443767 5597628339152686641665651)
                  ·
                    refine ⟨8396442508729029962498477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5597628339152686641665651 8396442508729029962498477)
                    ·
                      refine ⟨3148665940773386235936929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8396442508729029962498477 3148665940773386235936929)
                      ·
                        rfl

theorem cell23_6132005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_6132005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132005 prefixEnd_6132005 := by exact prefixLift 6132005
  have htrace : WordTrace (prefixWord ++ tailWord_6132005) baseStart_6132005 baseEnd_6132005 := by
    simpa [prefixWord, tailWord_6132005, baseEnd_6132005] using wordTrace_append hprefix tailTrace_6132005
  have hstable : (prefixWord ++ tailWord_6132005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132005).length < 2 ^ (prefixWord ++ tailWord_6132005).sum := by decide
  have hdescent : baseEnd_6132005 < baseStart_6132005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132017 : List Nat := [1, 2, 2, 3, 4, 2, 9]
def baseStart_6132017 : Nat := 118140960795 + 6132017 * 2 ^ 59
def prefixEnd_6132017 : Nat := 4983230072969 + 3 ^ 40 * 6132017 * 2
def baseEnd_6132017 : Nat := 38872495093101730728233

theorem tailTrace_6132017 : CollatzResearch.WordTrace tailWord_6132017 prefixEnd_6132017 38872495093101730728233 := by
  unfold tailWord_6132017
  simp only [CollatzResearch.WordTrace]
  refine ⟨223653033825757148971674305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149102022550504765981116203 223653033825757148971674305)
  ·
    refine ⟨167739775369317861728755729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223653033825757148971674305 167739775369317861728755729)
    ·
      refine ⟨125804831526988396296566797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167739775369317861728755729 125804831526988396296566797)
      ·
        refine ⟨47176811822620648611212549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125804831526988396296566797 47176811822620648611212549)
        ·
          refine ⟨8845652216741371614602353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47176811822620648611212549 8845652216741371614602353)
          ·
            refine ⟨6634239162556028710951765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8845652216741371614602353 6634239162556028710951765)
            ·
              refine ⟨38872495093101730728233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6634239162556028710951765 38872495093101730728233)
              ·
                rfl

theorem cell23_6132017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 9].length) (baseStart_6132017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132017 prefixEnd_6132017 := by exact prefixLift 6132017
  have htrace : WordTrace (prefixWord ++ tailWord_6132017) baseStart_6132017 baseEnd_6132017 := by
    simpa [prefixWord, tailWord_6132017, baseEnd_6132017] using wordTrace_append hprefix tailTrace_6132017
  have hstable : (prefixWord ++ tailWord_6132017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132017).length < 2 ^ (prefixWord ++ tailWord_6132017).sum := by decide
  have hdescent : baseEnd_6132017 < baseStart_6132017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132037 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 1, 9, 2]
def baseStart_6132037 : Nat := 118140960795 + 6132037 * 2 ^ 59
def prefixEnd_6132037 : Nat := 4983230072969 + 3 ^ 40 * 6132037 * 2
def baseEnd_6132037 : Nat := 3148682372154330110736781

theorem tailTrace_6132037 : CollatzResearch.WordTrace tailWord_6132037 prefixEnd_6132037 3148682372154330110736781 := by
  unfold tailWord_6132037
  simp only [CollatzResearch.WordTrace]
  refine ⟨223653763285684692387402365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149102508857123128258268243 223653763285684692387402365)
  ·
    refine ⟨83870161232131759645275887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223653763285684692387402365 83870161232131759645275887)
    ·
      refine ⟨125805241848197639467913831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83870161232131759645275887 125805241848197639467913831)
      ·
        refine ⟨188707862772296459201870747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125805241848197639467913831 188707862772296459201870747)
        ·
          refine ⟨283061794158444688802806121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188707862772296459201870747 283061794158444688802806121)
          ·
            refine ⟨212296345618833516602104591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283061794158444688802806121 212296345618833516602104591)
            ·
              refine ⟨318444518428250274903156887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212296345618833516602104591 318444518428250274903156887)
              ·
                refine ⟨477666777642375412354735331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318444518428250274903156887 477666777642375412354735331)
                ·
                  refine ⟨716500166463563118532102997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477666777642375412354735331 716500166463563118532102997)
                  ·
                    refine ⟨4198243162872440147649041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 716500166463563118532102997 4198243162872440147649041)
                    ·
                      refine ⟨3148682372154330110736781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4198243162872440147649041 3148682372154330110736781)
                      ·
                        rfl

theorem cell23_6132037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 9, 2].length) (baseStart_6132037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132037 prefixEnd_6132037 := by exact prefixLift 6132037
  have htrace : WordTrace (prefixWord ++ tailWord_6132037) baseStart_6132037 baseEnd_6132037 := by
    simpa [prefixWord, tailWord_6132037, baseEnd_6132037] using wordTrace_append hprefix tailTrace_6132037
  have hstable : (prefixWord ++ tailWord_6132037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132037).length < 2 ^ (prefixWord ++ tailWord_6132037).sum := by decide
  have hdescent : baseEnd_6132037 < baseStart_6132037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132077 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_6132077 : Nat := 118140960795 + 6132077 * 2 ^ 59
def prefixEnd_6132077 : Nat := 4983230072969 + 3 ^ 40 * 6132077 * 2
def baseEnd_6132077 : Nat := 1049567637126836651412199

theorem tailTrace_6132077 : CollatzResearch.WordTrace tailWord_6132077 prefixEnd_6132077 1049567637126836651412199 := by
  unfold tailWord_6132077
  simp only [CollatzResearch.WordTrace]
  refine ⟨223655222205539779218858485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149103481470359852812572323 223655222205539779218858485)
  ·
    refine ⟨20967677081769354301767983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223655222205539779218858485 20967677081769354301767983)
    ·
      refine ⟨31451515622654031452651975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20967677081769354301767983 31451515622654031452651975)
      ·
        refine ⟨47177273433981047178977963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31451515622654031452651975 47177273433981047178977963)
        ·
          refine ⟨70765910150971570768466945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47177273433981047178977963 70765910150971570768466945)
          ·
            refine ⟨53074432613228678076350209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70765910150971570768466945 53074432613228678076350209)
            ·
              refine ⟨39805824459921508557262657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53074432613228678076350209 39805824459921508557262657)
              ·
                refine ⟨29854368344941131417946993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39805824459921508557262657 29854368344941131417946993)
                ·
                  refine ⟨22390776258705848563460245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29854368344941131417946993 22390776258705848563460245)
                  ·
                    refine ⟨1049567637126836651412199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22390776258705848563460245 1049567637126836651412199)
                    ·
                      rfl

theorem cell23_6132077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_6132077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132077 prefixEnd_6132077 := by exact prefixLift 6132077
  have htrace : WordTrace (prefixWord ++ tailWord_6132077) baseStart_6132077 baseEnd_6132077 := by
    simpa [prefixWord, tailWord_6132077, baseEnd_6132077] using wordTrace_append hprefix tailTrace_6132077
  have hstable : (prefixWord ++ tailWord_6132077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132077).length < 2 ^ (prefixWord ++ tailWord_6132077).sum := by decide
  have hdescent : baseEnd_6132077 < baseStart_6132077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132107 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 7]
def baseStart_6132107 : Nat := 118140960795 + 6132107 * 2 ^ 59
def prefixEnd_6132107 : Nat := 4983230072969 + 3 ^ 40 * 6132107 * 2
def baseEnd_6132107 : Nat := 349857590644460537429051

theorem tailTrace_6132107 : CollatzResearch.WordTrace tailWord_6132107 prefixEnd_6132107 349857590644460537429051 := by
  unfold tailWord_6132107
  simp only [CollatzResearch.WordTrace]
  refine ⟨223656316395431094342450575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149104210930287396228300383 223656316395431094342450575)
  ·
    refine ⟨335484474593146641513675863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223656316395431094342450575 335484474593146641513675863)
    ·
      refine ⟨503226711889719962270513795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335484474593146641513675863 503226711889719962270513795)
      ·
        refine ⟨754840067834579943405770693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503226711889719962270513795 754840067834579943405770693)
        ·
          refine ⟨141532512718983739388582005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 754840067834579943405770693 141532512718983739388582005)
          ·
            refine ⟨13268673067404725567679563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141532512718983739388582005 13268673067404725567679563)
            ·
              refine ⟨19903009601107088351519345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13268673067404725567679563 19903009601107088351519345)
              ·
                refine ⟨14927257200830316263639509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19903009601107088351519345 14927257200830316263639509)
                ·
                  refine ⟨349857590644460537429051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14927257200830316263639509 349857590644460537429051)
                  ·
                    rfl

theorem cell23_6132107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 7].length) (baseStart_6132107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132107 prefixEnd_6132107 := by exact prefixLift 6132107
  have htrace : WordTrace (prefixWord ++ tailWord_6132107) baseStart_6132107 baseEnd_6132107 := by
    simpa [prefixWord, tailWord_6132107, baseEnd_6132107] using wordTrace_append hprefix tailTrace_6132107
  have hstable : (prefixWord ++ tailWord_6132107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132107).length < 2 ^ (prefixWord ++ tailWord_6132107).sum := by decide
  have hdescent : baseEnd_6132107 < baseStart_6132107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132117 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 3, 5, 3]
def baseStart_6132117 : Nat := 118140960795 + 6132117 * 2 ^ 59
def prefixEnd_6132117 : Nat := 4983230072969 + 3 ^ 40 * 6132117 * 2
def baseEnd_6132117 : Nat := 3148723450606689797736413

theorem tailTrace_6132117 : CollatzResearch.WordTrace tailWord_6132117 prefixEnd_6132117 3148723450606689797736413 := by
  unfold tailWord_6132117
  simp only [CollatzResearch.WordTrace]
  refine ⟨223656681125394866050314605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149104454083596577366876403 223656681125394866050314605)
  ·
    refine ⟨83871255422023074768867977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223656681125394866050314605 83871255422023074768867977)
    ·
      refine ⟨62903441566517306076650983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83871255422023074768867977 62903441566517306076650983)
      ·
        refine ⟨94355162349775959114976475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62903441566517306076650983 94355162349775959114976475)
        ·
          refine ⟨141532743524663938672464713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94355162349775959114976475 141532743524663938672464713)
          ·
            refine ⟨106149557643497954004348535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141532743524663938672464713 106149557643497954004348535)
            ·
              refine ⟨159224336465246931006522803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106149557643497954004348535 159224336465246931006522803)
              ·
                refine ⟨238836504697870396509784205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159224336465246931006522803 238836504697870396509784205)
                ·
                  refine ⟨89563689261701398691169077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238836504697870396509784205 89563689261701398691169077)
                  ·
                    refine ⟨8396595868284506127297101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89563689261701398691169077 8396595868284506127297101)
                    ·
                      refine ⟨3148723450606689797736413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8396595868284506127297101 3148723450606689797736413)
                      ·
                        rfl

theorem cell23_6132117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_6132117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132117 prefixEnd_6132117 := by exact prefixLift 6132117
  have htrace : WordTrace (prefixWord ++ tailWord_6132117) baseStart_6132117 baseEnd_6132117 := by
    simpa [prefixWord, tailWord_6132117, baseEnd_6132117] using wordTrace_append hprefix tailTrace_6132117
  have hstable : (prefixWord ++ tailWord_6132117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132117).length < 2 ^ (prefixWord ++ tailWord_6132117).sum := by decide
  have hdescent : baseEnd_6132117 < baseStart_6132117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132135 : List Nat := [1, 1, 6, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_6132135 : Nat := 118140960795 + 6132135 * 2 ^ 59
def prefixEnd_6132135 : Nat := 4983230072969 + 3 ^ 40 * 6132135 * 2
def baseEnd_6132135 : Nat := 3148732693258470727311331

theorem tailTrace_6132135 : CollatzResearch.WordTrace tailWord_6132135 prefixEnd_6132135 3148732693258470727311331 := by
  unfold tailWord_6132135
  simp only [CollatzResearch.WordTrace]
  refine ⟨223657337639329655124469859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149104891759553103416313239 223657337639329655124469859)
  ·
    refine ⟨335486006458994482686704789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223657337639329655124469859 335486006458994482686704789)
    ·
      refine ⟨15725906552765366375939287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 335486006458994482686704789 15725906552765366375939287)
      ·
        refine ⟨23588859829148049563908931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15725906552765366375939287 23588859829148049563908931)
        ·
          refine ⟨35383289743722074345863397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23588859829148049563908931 35383289743722074345863397)
          ·
            refine ⟨6634366826947888939849387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35383289743722074345863397 6634366826947888939849387)
            ·
              refine ⟨9951550240421833409774081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6634366826947888939849387 9951550240421833409774081)
              ·
                refine ⟨7463662680316375057330561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9951550240421833409774081 7463662680316375057330561)
                ·
                  refine ⟨5597747010237281292997921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7463662680316375057330561 5597747010237281292997921)
                  ·
                    refine ⟨4198310257677960969748441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5597747010237281292997921 4198310257677960969748441)
                    ·
                      refine ⟨3148732693258470727311331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4198310257677960969748441 3148732693258470727311331)
                      ·
                        rfl

theorem cell23_6132135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_6132135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132135 prefixEnd_6132135 := by exact prefixLift 6132135
  have htrace : WordTrace (prefixWord ++ tailWord_6132135) baseStart_6132135 baseEnd_6132135 := by
    simpa [prefixWord, tailWord_6132135, baseEnd_6132135] using wordTrace_append hprefix tailTrace_6132135
  have hstable : (prefixWord ++ tailWord_6132135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132135).length < 2 ^ (prefixWord ++ tailWord_6132135).sum := by decide
  have hdescent : baseEnd_6132135 < baseStart_6132135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132137 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 2, 5]
def baseStart_6132137 : Nat := 118140960795 + 6132137 * 2 ^ 59
def prefixEnd_6132137 : Nat := 4983230072969 + 3 ^ 40 * 6132137 * 2
def baseEnd_6132137 : Nat := 1049577906739926573162107

theorem tailTrace_6132137 : CollatzResearch.WordTrace tailWord_6132137 prefixEnd_6132137 1049577906739926573162107 := by
  unfold tailWord_6132137
  simp only [CollatzResearch.WordTrace]
  refine ⟨223657410585322409466042665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149104940390214939644028443 223657410585322409466042665)
  ·
    refine ⟨167743057938991807099531999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223657410585322409466042665 167743057938991807099531999)
    ·
      refine ⟨251614586908487710649297999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167743057938991807099531999 251614586908487710649297999)
      ·
        refine ⟨377421880362731565973946999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251614586908487710649297999 377421880362731565973946999)
        ·
          refine ⟨566132820544097348960920499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377421880362731565973946999 566132820544097348960920499)
          ·
            refine ⟨849199230816146023441380749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566132820544097348960920499 849199230816146023441380749)
            ·
              refine ⟨318449711556054758790517781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 849199230816146023441380749 318449711556054758790517781)
              ·
                refine ⟨14927330229190066818305521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 318449711556054758790517781 14927330229190066818305521)
                ·
                  refine ⟨11195497671892550113729141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14927330229190066818305521 11195497671892550113729141)
                  ·
                    refine ⟨1049577906739926573162107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11195497671892550113729141 1049577906739926573162107)
                    ·
                      rfl

theorem cell23_6132137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 5].length) (baseStart_6132137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132137 prefixEnd_6132137 := by exact prefixLift 6132137
  have htrace : WordTrace (prefixWord ++ tailWord_6132137) baseStart_6132137 baseEnd_6132137 := by
    simpa [prefixWord, tailWord_6132137, baseEnd_6132137] using wordTrace_append hprefix tailTrace_6132137
  have hstable : (prefixWord ++ tailWord_6132137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132137).length < 2 ^ (prefixWord ++ tailWord_6132137).sum := by decide
  have hdescent : baseEnd_6132137 < baseStart_6132137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132141 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 7]
def baseStart_6132141 : Nat := 118140960795 + 6132141 * 2 ^ 59
def prefixEnd_6132141 : Nat := 4983230072969 + 3 ^ 40 * 6132141 * 2
def baseEnd_6132141 : Nat := 349859530460266411537367

theorem tailTrace_6132141 : CollatzResearch.WordTrace tailWord_6132141 prefixEnd_6132141 349859530460266411537367 := by
  unfold tailWord_6132141
  simp only [CollatzResearch.WordTrace]
  refine ⟨223657556477307918149188277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149105037651538612099458851 223657556477307918149188277)
  ·
    refine ⟨20967895919747617326486401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223657556477307918149188277 20967895919747617326486401)
    ·
      refine ⟨15725921939810712994864801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20967895919747617326486401 15725921939810712994864801)
      ·
        refine ⟨11794441454858034746148601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15725921939810712994864801 11794441454858034746148601)
        ·
          refine ⟨8845831091143526059611451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11794441454858034746148601 8845831091143526059611451)
          ·
            refine ⟨13268746636715289089417177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8845831091143526059611451 13268746636715289089417177)
            ·
              refine ⟨9951559977536466817062883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13268746636715289089417177 9951559977536466817062883)
              ·
                refine ⟨14927339966304700225594325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9951559977536466817062883 14927339966304700225594325)
                ·
                  refine ⟨349859530460266411537367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14927339966304700225594325 349859530460266411537367)
                  ·
                    rfl

theorem cell23_6132141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_6132141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132141 prefixEnd_6132141 := by exact prefixLift 6132141
  have htrace : WordTrace (prefixWord ++ tailWord_6132141) baseStart_6132141 baseEnd_6132141 := by
    simpa [prefixWord, tailWord_6132141, baseEnd_6132141] using wordTrace_append hprefix tailTrace_6132141
  have hstable : (prefixWord ++ tailWord_6132141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132141).length < 2 ^ (prefixWord ++ tailWord_6132141).sum := by decide
  have hdescent : baseEnd_6132141 < baseStart_6132141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132174 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_6132174 : Nat := 118140960795 + 6132174 * 2 ^ 59
def prefixEnd_6132174 : Nat := 4983230072969 + 3 ^ 40 * 6132174 * 2
def baseEnd_6132174 : Nat := 3148752719003996074723651

theorem tailTrace_6132174 : CollatzResearch.WordTrace tailWord_6132174 prefixEnd_6132174 3148752719003996074723651 := by
  unfold tailWord_6132174
  simp only [CollatzResearch.WordTrace]
  refine ⟨27957345010773545598142447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149105840057458909856759717 27957345010773545598142447)
  ·
    refine ⟨41936017516160318397213671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27957345010773545598142447 41936017516160318397213671)
    ·
      refine ⟨62904026274240477595820507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41936017516160318397213671 62904026274240477595820507)
      ·
        refine ⟨94356039411360716393730761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62904026274240477595820507 94356039411360716393730761)
        ·
          refine ⟨70767029558520537295298071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94356039411360716393730761 70767029558520537295298071)
          ·
            refine ⟨106150544337780805942947107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70767029558520537295298071 106150544337780805942947107)
            ·
              refine ⟨159225816506671208914420661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106150544337780805942947107 159225816506671208914420661)
              ·
                refine ⟨14927420297500425835726937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159225816506671208914420661 14927420297500425835726937)
                ·
                  refine ⟨11195565223125319376795203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14927420297500425835726937 11195565223125319376795203)
                  ·
                    refine ⟨16793347834687979065192805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11195565223125319376795203 16793347834687979065192805)
                    ·
                      refine ⟨3148752719003996074723651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16793347834687979065192805 3148752719003996074723651)
                      ·
                        rfl

theorem cell23_6132174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_6132174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132174 prefixEnd_6132174 := by exact prefixLift 6132174
  have htrace : WordTrace (prefixWord ++ tailWord_6132174) baseStart_6132174 baseEnd_6132174 := by
    simpa [prefixWord, tailWord_6132174, baseEnd_6132174] using wordTrace_append hprefix tailTrace_6132174
  have hstable : (prefixWord ++ tailWord_6132174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132174).length < 2 ^ (prefixWord ++ tailWord_6132174).sum := by decide
  have hdescent : baseEnd_6132174 < baseStart_6132174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132217 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 6]
def baseStart_6132217 : Nat := 118140960795 + 6132217 * 2 ^ 59
def prefixEnd_6132217 : Nat := 4983230072969 + 3 ^ 40 * 6132217 * 2
def baseEnd_6132217 : Nat := 3148774798672139406485953

theorem tailTrace_6132217 : CollatzResearch.WordTrace tailWord_6132217 prefixEnd_6132217 3148774798672139406485953 := by
  unfold tailWord_6132217
  simp only [CollatzResearch.WordTrace]
  refine ⟨223660328425032583128954905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149106885616688388752636603 223660328425032583128954905)
  ·
    refine ⟨167745246318774437346716179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223660328425032583128954905 167745246318774437346716179)
    ·
      refine ⟨251617869478161656020074269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167745246318774437346716179 251617869478161656020074269)
      ·
        refine ⟨94356701054310621007527851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251617869478161656020074269 94356701054310621007527851)
        ·
          refine ⟨141535051581465931511291777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94356701054310621007527851 141535051581465931511291777)
          ·
            refine ⟨106151288686099448633468833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141535051581465931511291777 106151288686099448633468833)
            ·
              refine ⟨79613466514574586475101625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106151288686099448633468833 79613466514574586475101625)
              ·
                refine ⟨59710099885930939856326219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79613466514574586475101625 59710099885930939856326219)
                ·
                  refine ⟨89565149828896409784489329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59710099885930939856326219 89565149828896409784489329)
                  ·
                    refine ⟨67173862371672307338366997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89565149828896409784489329 67173862371672307338366997)
                    ·
                      refine ⟨3148774798672139406485953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67173862371672307338366997 3148774798672139406485953)
                      ·
                        rfl

theorem cell23_6132217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_6132217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132217 prefixEnd_6132217 := by exact prefixLift 6132217
  have htrace : WordTrace (prefixWord ++ tailWord_6132217) baseStart_6132217 baseEnd_6132217 := by
    simpa [prefixWord, tailWord_6132217, baseEnd_6132217] using wordTrace_append hprefix tailTrace_6132217
  have hstable : (prefixWord ++ tailWord_6132217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132217).length < 2 ^ (prefixWord ++ tailWord_6132217).sum := by decide
  have hdescent : baseEnd_6132217 < baseStart_6132217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132228 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_6132228 : Nat := 118140960795 + 6132228 * 2 ^ 59
def prefixEnd_6132228 : Nat := 4983230072969 + 3 ^ 40 * 6132228 * 2
def baseEnd_6132228 : Nat := 3148780446959338863448403

theorem tailTrace_6132228 : CollatzResearch.WordTrace tailWord_6132228 prefixEnd_6132228 3148780446959338863448403 := by
  unfold tailWord_6132228
  simp only [CollatzResearch.WordTrace]
  refine ⟨111830364813996366003802669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149107153085328488005070225 111830364813996366003802669)
  ·
    refine ⟨41936386805248637251426001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111830364813996366003802669 41936386805248637251426001)
    ·
      refine ⟨31452290103936477938569501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41936386805248637251426001 31452290103936477938569501)
      ·
        refine ⟨11794608788976179226963563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31452290103936477938569501 11794608788976179226963563)
        ·
          refine ⟨17691913183464268840445345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11794608788976179226963563 17691913183464268840445345)
          ·
            refine ⟨13268934887598201630334009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17691913183464268840445345 13268934887598201630334009)
            ·
              refine ⟨9951701165698651222750507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13268934887598201630334009 9951701165698651222750507)
              ·
                refine ⟨14927551748547976834125761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9951701165698651222750507 14927551748547976834125761)
                ·
                  refine ⟨11195663811410982625594321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14927551748547976834125761 11195663811410982625594321)
                  ·
                    refine ⟨8396747858558236969195741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11195663811410982625594321 8396747858558236969195741)
                    ·
                      refine ⟨3148780446959338863448403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8396747858558236969195741 3148780446959338863448403)
                      ·
                        rfl

theorem cell23_6132228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_6132228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132228 prefixEnd_6132228 := by exact prefixLift 6132228
  have htrace : WordTrace (prefixWord ++ tailWord_6132228) baseStart_6132228 baseEnd_6132228 := by
    simpa [prefixWord, tailWord_6132228, baseEnd_6132228] using wordTrace_append hprefix tailTrace_6132228
  have hstable : (prefixWord ++ tailWord_6132228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132228).length < 2 ^ (prefixWord ++ tailWord_6132228).sum := by decide
  have hdescent : baseEnd_6132228 < baseStart_6132228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132274 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 1, 6]
def baseStart_6132274 : Nat := 118140960795 + 6132274 * 2 ^ 59
def prefixEnd_6132274 : Nat := 4983230072969 + 3 ^ 40 * 6132274 * 2
def baseEnd_6132274 : Nat := 1049601355689815227824397

theorem tailTrace_6132274 : CollatzResearch.WordTrace tailWord_6132274 prefixEnd_6132274 1049601355689815227824397 := by
  unfold tailWord_6132274
  simp only [CollatzResearch.WordTrace]
  refine ⟨55915601846456520465944969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149108271590550721242519917 55915601846456520465944969)
  ·
    refine ⟨41936701384842390349458727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55915601846456520465944969 41936701384842390349458727)
    ·
      refine ⟨62905052077263585524188091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41936701384842390349458727 62905052077263585524188091)
      ·
        refine ⟨94357578115895378286282137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62905052077263585524188091 94357578115895378286282137)
        ·
          refine ⟨70768183586921533714711603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94357578115895378286282137 70768183586921533714711603)
          ·
            refine ⟨106152275380382300572067405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70768183586921533714711603 106152275380382300572067405)
            ·
              refine ⟨39807103267643362714525277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106152275380382300572067405 39807103267643362714525277)
              ·
                refine ⟨14927663725366261017946979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39807103267643362714525277 14927663725366261017946979)
                ·
                  refine ⟨22391495588049391526920469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14927663725366261017946979 22391495588049391526920469)
                  ·
                    refine ⟨1049601355689815227824397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22391495588049391526920469 1049601355689815227824397)
                    ·
                      rfl

theorem cell23_6132274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_6132274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132274 prefixEnd_6132274 := by exact prefixLift 6132274
  have htrace : WordTrace (prefixWord ++ tailWord_6132274) baseStart_6132274 baseEnd_6132274 := by
    simpa [prefixWord, tailWord_6132274, baseEnd_6132274] using wordTrace_append hprefix tailTrace_6132274
  have hstable : (prefixWord ++ tailWord_6132274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132274).length < 2 ^ (prefixWord ++ tailWord_6132274).sum := by decide
  have hdescent : baseEnd_6132274 < baseStart_6132274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132281 : List Nat := [1, 2, 1, 5, 1, 1, 2, 4, 1, 1, 4]
def baseStart_6132281 : Nat := 118140960795 + 6132281 * 2 ^ 59
def prefixEnd_6132281 : Nat := 4983230072969 + 3 ^ 40 * 6132281 * 2
def baseEnd_6132281 : Nat := 3148807661434027156085659

theorem tailTrace_6132281 : CollatzResearch.WordTrace tailWord_6132281 prefixEnd_6132281 3148807661434027156085659 := by
  unfold tailWord_6132281
  simp only [CollatzResearch.WordTrace]
  refine ⟨223662662696800722059284697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149108441797867148039523131 223662662696800722059284697)
  ·
    refine ⟨167746997022600541544463523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223662662696800722059284697 167746997022600541544463523)
    ·
      refine ⟨251620495533900812316695285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167746997022600541544463523 251620495533900812316695285)
      ·
        refine ⟨23589421456303201154690183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 251620495533900812316695285 23589421456303201154690183)
        ·
          refine ⟨35384132184454801732035275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23589421456303201154690183 35384132184454801732035275)
          ·
            refine ⟨53076198276682202598052913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35384132184454801732035275 53076198276682202598052913)
            ·
              refine ⟨39807148707511651948539685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53076198276682202598052913 39807148707511651948539685)
              ·
                refine ⟨7463840382658434740351191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39807148707511651948539685 7463840382658434740351191)
                ·
                  refine ⟨11195760573987652110526787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7463840382658434740351191 11195760573987652110526787)
                  ·
                    refine ⟨16793640860981478165790181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11195760573987652110526787 16793640860981478165790181)
                    ·
                      refine ⟨3148807661434027156085659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16793640860981478165790181 3148807661434027156085659)
                      ·
                        rfl

theorem cell23_6132281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_6132281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132281 prefixEnd_6132281 := by exact prefixLift 6132281
  have htrace : WordTrace (prefixWord ++ tailWord_6132281) baseStart_6132281 baseEnd_6132281 := by
    simpa [prefixWord, tailWord_6132281, baseEnd_6132281] using wordTrace_append hprefix tailTrace_6132281
  have hstable : (prefixWord ++ tailWord_6132281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132281).length < 2 ^ (prefixWord ++ tailWord_6132281).sum := by decide
  have hdescent : baseEnd_6132281 < baseStart_6132281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132285 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 2, 3, 2]
def baseStart_6132285 : Nat := 118140960795 + 6132285 * 2 ^ 59
def prefixEnd_6132285 : Nat := 4983230072969 + 3 ^ 40 * 6132285 * 2
def baseEnd_6132285 : Nat := 3148809715356645140435641

theorem tailTrace_6132285 : CollatzResearch.WordTrace tailWord_6132285 prefixEnd_6132285 3148809715356645140435641 := by
  unfold tailWord_6132285
  simp only [CollatzResearch.WordTrace]
  refine ⟨223662808588786230742430309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149108539059190820494953539 223662808588786230742430309)
  ·
    refine ⟨41936776610397418264205683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223662808588786230742430309 41936776610397418264205683)
    ·
      refine ⟨62905164915596127396308525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41936776610397418264205683 62905164915596127396308525)
      ·
        refine ⟨23589436843348547773615697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62905164915596127396308525 23589436843348547773615697)
        ·
          refine ⟨17692077632511410830211773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23589436843348547773615697 17692077632511410830211773)
          ·
            refine ⟨6634529112191779061329415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17692077632511410830211773 6634529112191779061329415)
            ·
              refine ⟨9951793668287668591994123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6634529112191779061329415 9951793668287668591994123)
              ·
                refine ⟨14927690502431502887991185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9951793668287668591994123 14927690502431502887991185)
                ·
                  refine ⟨11195767876823627165993389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14927690502431502887991185 11195767876823627165993389)
                  ·
                    refine ⟨4198412953808860187247521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11195767876823627165993389 4198412953808860187247521)
                    ·
                      refine ⟨3148809715356645140435641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4198412953808860187247521 3148809715356645140435641)
                      ·
                        rfl

theorem cell23_6132285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_6132285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132285 prefixEnd_6132285 := by exact prefixLift 6132285
  have htrace : WordTrace (prefixWord ++ tailWord_6132285) baseStart_6132285 baseEnd_6132285 := by
    simpa [prefixWord, tailWord_6132285, baseEnd_6132285] using wordTrace_append hprefix tailTrace_6132285
  have hstable : (prefixWord ++ tailWord_6132285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132285).length < 2 ^ (prefixWord ++ tailWord_6132285).sum := by decide
  have hdescent : baseEnd_6132285 < baseStart_6132285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132298 : List Nat := [3, 1, 2, 1, 1, 4, 4, 1, 1, 1, 4]
def baseStart_6132298 : Nat := 118140960795 + 6132298 * 2 ^ 59
def prefixEnd_6132298 : Nat := 4983230072969 + 3 ^ 40 * 6132298 * 2
def baseEnd_6132298 : Nat := 3148816390605153589573081

theorem tailTrace_6132298 : CollatzResearch.WordTrace tailWord_6132298 prefixEnd_6132298 3148816390605153589573081 := by
  unfold tailWord_6132298
  simp only [CollatzResearch.WordTrace]
  refine ⟨55915820684434783490663387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149108855158492755975102365 55915820684434783490663387)
  ·
    refine ⟨83873731026652175235995081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55915820684434783490663387 83873731026652175235995081)
    ·
      refine ⟨62905298269989131426996311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83873731026652175235995081 62905298269989131426996311)
      ·
        refine ⟨94357947404983697140494467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62905298269989131426996311 94357947404983697140494467)
        ·
          refine ⟨141536921107475545710741701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94357947404983697140494467 141536921107475545710741701)
          ·
            refine ⟨26538172707651664820764069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141536921107475545710741701 26538172707651664820764069)
            ·
              refine ⟨4975907382684687153893263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26538172707651664820764069 4975907382684687153893263)
              ·
                refine ⟨7463861074027030730839895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4975907382684687153893263 7463861074027030730839895)
                ·
                  refine ⟨11195791611040546096259843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7463861074027030730839895 11195791611040546096259843)
                  ·
                    refine ⟨16793687416560819144389765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11195791611040546096259843 16793687416560819144389765)
                    ·
                      refine ⟨3148816390605153589573081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16793687416560819144389765 3148816390605153589573081)
                      ·
                        rfl

theorem cell23_6132298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_6132298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132298 prefixEnd_6132298 := by exact prefixLift 6132298
  have htrace : WordTrace (prefixWord ++ tailWord_6132298) baseStart_6132298 baseEnd_6132298 := by
    simpa [prefixWord, tailWord_6132298, baseEnd_6132298] using wordTrace_append hprefix tailTrace_6132298
  have hstable : (prefixWord ++ tailWord_6132298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132298).length < 2 ^ (prefixWord ++ tailWord_6132298).sum := by decide
  have hdescent : baseEnd_6132298 < baseStart_6132298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132308 : List Nat := [2, 4, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_6132308 : Nat := 118140960795 + 6132308 * 2 ^ 59
def prefixEnd_6132308 : Nat := 4983230072969 + 3 ^ 40 * 6132308 * 2
def baseEnd_6132308 : Nat := 1049607175137232850149345

theorem tailTrace_6132308 : CollatzResearch.WordTrace tailWord_6132308 prefixEnd_6132308 1049607175137232850149345 := by
  unfold tailWord_6132308
  simp only [CollatzResearch.WordTrace]
  refine ⟨111831823733851452835258789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149109098311801937113678385 111831823733851452835258789)
  ·
    refine ⟨20968466950097147406611023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111831823733851452835258789 20968466950097147406611023)
    ·
      refine ⟨31452700425145721109916535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20968466950097147406611023 31452700425145721109916535)
      ·
        refine ⟨47179050637718581664874803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31452700425145721109916535 47179050637718581664874803)
        ·
          refine ⟨70768575956577872497312205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47179050637718581664874803 70768575956577872497312205)
          ·
            refine ⟨26538215983716702186492077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70768575956577872497312205 26538215983716702186492077)
            ·
              refine ⟨9951830993893763319934529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26538215983716702186492077 9951830993893763319934529)
              ·
                refine ⟨7463873245420322489950897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9951830993893763319934529 7463873245420322489950897)
                ·
                  refine ⟨5597904934065241867463173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7463873245420322489950897 5597904934065241867463173)
                  ·
                    refine ⟨1049607175137232850149345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5597904934065241867463173 1049607175137232850149345)
                    ·
                      rfl

theorem cell23_6132308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_6132308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132308 prefixEnd_6132308 := by exact prefixLift 6132308
  have htrace : WordTrace (prefixWord ++ tailWord_6132308) baseStart_6132308 baseEnd_6132308 := by
    simpa [prefixWord, tailWord_6132308, baseEnd_6132308] using wordTrace_append hprefix tailTrace_6132308
  have hstable : (prefixWord ++ tailWord_6132308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132308).length < 2 ^ (prefixWord ++ tailWord_6132308).sum := by decide
  have hdescent : baseEnd_6132308 < baseStart_6132308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132314 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3]
def baseStart_6132314 : Nat := 118140960795 + 6132314 * 2 ^ 59
def prefixEnd_6132314 : Nat := 4983230072969 + 3 ^ 40 * 6132314 * 2
def baseEnd_6132314 : Nat := 3148824606295625526973007

theorem tailTrace_6132314 : CollatzResearch.WordTrace tailWord_6132314 prefixEnd_6132314 3148824606295625526973007 := by
  unfold tailWord_6132314
  simp only [CollatzResearch.WordTrace]
  refine ⟨55915966576420292173808999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149109244203787445796823997 55915966576420292173808999)
  ·
    refine ⟨83873949864630438260713499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55915966576420292173808999 83873949864630438260713499)
    ·
      refine ⟨125810924796945657391070249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83873949864630438260713499 125810924796945657391070249)
      ·
        refine ⟨94358193597709243043302687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125810924796945657391070249 94358193597709243043302687)
        ·
          refine ⟨141537290396563864564954031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94358193597709243043302687 141537290396563864564954031)
          ·
            refine ⟨212305935594845796847431047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141537290396563864564954031 212305935594845796847431047)
            ·
              refine ⟨318458903392268695271146571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212305935594845796847431047 318458903392268695271146571)
              ·
                refine ⟨477688355088403042906719857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318458903392268695271146571 477688355088403042906719857)
                ·
                  refine ⟨358266266316302282180039893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477688355088403042906719857 358266266316302282180039893)
                  ·
                    refine ⟨8396865616788334738594685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 358266266316302282180039893 8396865616788334738594685)
                    ·
                      refine ⟨3148824606295625526973007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8396865616788334738594685 3148824606295625526973007)
                      ·
                        rfl

theorem cell23_6132314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_6132314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132314 prefixEnd_6132314 := by exact prefixLift 6132314
  have htrace : WordTrace (prefixWord ++ tailWord_6132314) baseStart_6132314 baseEnd_6132314 := by
    simpa [prefixWord, tailWord_6132314, baseEnd_6132314] using wordTrace_append hprefix tailTrace_6132314
  have hstable : (prefixWord ++ tailWord_6132314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132314).length < 2 ^ (prefixWord ++ tailWord_6132314).sum := by decide
  have hdescent : baseEnd_6132314 < baseStart_6132314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132325 : List Nat := [1, 3, 1, 3, 4, 1, 3, 1, 2, 4]
def baseStart_6132325 : Nat := 118140960795 + 6132325 * 2 ^ 59
def prefixEnd_6132325 : Nat := 4983230072969 + 3 ^ 40 * 6132325 * 2
def baseEnd_6132325 : Nat := 1049610084860941661311819

theorem tailTrace_6132325 : CollatzResearch.WordTrace tailWord_6132325 prefixEnd_6132325 1049610084860941661311819 := by
  unfold tailWord_6132325
  simp only [CollatzResearch.WordTrace]
  refine ⟨223664267508641317573886429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149109511672427545049257619 223664267508641317573886429)
  ·
    refine ⟨83874100315740494090207411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223664267508641317573886429 83874100315740494090207411)
    ·
      refine ⟨125811150473610741135311117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83874100315740494090207411 125811150473610741135311117)
      ·
        refine ⟨47179181427604027925741669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125811150473610741135311117 47179181427604027925741669)
        ·
          refine ⟨8846096517675755236076563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47179181427604027925741669 8846096517675755236076563)
          ·
            refine ⟨13269144776513632854114845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8846096517675755236076563 13269144776513632854114845)
            ·
              refine ⟨4975929291192612320293067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13269144776513632854114845 4975929291192612320293067)
              ·
                refine ⟨7463893936788918480439601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4975929291192612320293067 7463893936788918480439601)
                ·
                  refine ⟨5597920452591688860329701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7463893936788918480439601 5597920452591688860329701)
                  ·
                    refine ⟨1049610084860941661311819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5597920452591688860329701 1049610084860941661311819)
                    ·
                      rfl

theorem cell23_6132325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_6132325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132325 prefixEnd_6132325 := by exact prefixLift 6132325
  have htrace : WordTrace (prefixWord ++ tailWord_6132325) baseStart_6132325 baseEnd_6132325 := by
    simpa [prefixWord, tailWord_6132325, baseEnd_6132325] using wordTrace_append hprefix tailTrace_6132325
  have hstable : (prefixWord ++ tailWord_6132325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132325).length < 2 ^ (prefixWord ++ tailWord_6132325).sum := by decide
  have hdescent : baseEnd_6132325 < baseStart_6132325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132338 : List Nat := [3, 2, 1, 2, 4, 2, 2, 7]
def baseStart_6132338 : Nat := 118140960795 + 6132338 * 2 ^ 59
def prefixEnd_6132338 : Nat := 4983230072969 + 3 ^ 40 * 6132338 * 2
def baseEnd_6132338 : Nat := 116623589993753090113811

theorem tailTrace_6132338 : CollatzResearch.WordTrace tailWord_6132338 prefixEnd_6132338 116623589993753090113811 := by
  unfold tailWord_6132338
  simp only [CollatzResearch.WordTrace]
  refine ⟨55916185414398555198527417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149109827771729480529406445 55916185414398555198527417)
  ·
    refine ⟨41937139060798916398895563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55916185414398555198527417 41937139060798916398895563)
    ·
      refine ⟨62905708591198374598343345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41937139060798916398895563 62905708591198374598343345)
      ·
        refine ⟨47179281443398780948757509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62905708591198374598343345 47179281443398780948757509)
        ·
          refine ⟨8846115270637271427892033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47179281443398780948757509 8846115270637271427892033)
          ·
            refine ⟨6634586452977953570919025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8846115270637271427892033 6634586452977953570919025)
            ·
              refine ⟨4975939839733465178189269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6634586452977953570919025 4975939839733465178189269)
              ·
                refine ⟨116623589993753090113811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4975939839733465178189269 116623589993753090113811)
                ·
                  rfl

theorem cell23_6132338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 7].length) (baseStart_6132338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132338 prefixEnd_6132338 := by exact prefixLift 6132338
  have htrace : WordTrace (prefixWord ++ tailWord_6132338) baseStart_6132338 baseEnd_6132338 := by
    simpa [prefixWord, tailWord_6132338, baseEnd_6132338] using wordTrace_append hprefix tailTrace_6132338
  have hstable : (prefixWord ++ tailWord_6132338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132338).length < 2 ^ (prefixWord ++ tailWord_6132338).sum := by decide
  have hdescent : baseEnd_6132338 < baseStart_6132338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132349 : List Nat := [1, 4, 1, 1, 5, 2, 1, 3, 1, 2, 2]
def baseStart_6132349 : Nat := 118140960795 + 6132349 * 2 ^ 59
def prefixEnd_6132349 : Nat := 4983230072969 + 3 ^ 40 * 6132349 * 2
def baseEnd_6132349 : Nat := 3148842578118532890035347

theorem tailTrace_6132349 : CollatzResearch.WordTrace tailWord_6132349 prefixEnd_6132349 3148842578118532890035347 := by
  unfold tailWord_6132349
  simp only [CollatzResearch.WordTrace]
  refine ⟨223665142860554369672760101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149110095240369579781840067 223665142860554369672760101)
  ·
    refine ⟨41937214286353944313642519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223665142860554369672760101 41937214286353944313642519)
    ·
      refine ⟨62905821429530916470463779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41937214286353944313642519 62905821429530916470463779)
      ·
        refine ⟨94358732144296374705695669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62905821429530916470463779 94358732144296374705695669)
        ·
          refine ⟨8846131138527785128658969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94358732144296374705695669 8846131138527785128658969)
          ·
            refine ⟨6634598353895838846494227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8846131138527785128658969 6634598353895838846494227)
            ·
              refine ⟨9951897530843758269741341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6634598353895838846494227 9951897530843758269741341)
              ·
                refine ⟨3731961574066409351153003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9951897530843758269741341 3731961574066409351153003)
                ·
                  refine ⟨5597942361099614026729505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3731961574066409351153003 5597942361099614026729505)
                  ·
                    refine ⟨4198456770824710520047129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5597942361099614026729505 4198456770824710520047129)
                    ·
                      refine ⟨3148842578118532890035347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4198456770824710520047129 3148842578118532890035347)
                      ·
                        rfl

theorem cell23_6132349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_6132349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132349 prefixEnd_6132349 := by exact prefixLift 6132349
  have htrace : WordTrace (prefixWord ++ tailWord_6132349) baseStart_6132349 baseEnd_6132349 := by
    simpa [prefixWord, tailWord_6132349, baseEnd_6132349] using wordTrace_append hprefix tailTrace_6132349
  have hstable : (prefixWord ++ tailWord_6132349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132349).length < 2 ^ (prefixWord ++ tailWord_6132349).sum := by decide
  have hdescent : baseEnd_6132349 < baseStart_6132349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132364 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 2, 6]
def baseStart_6132364 : Nat := 118140960795 + 6132364 * 2 ^ 59
def prefixEnd_6132364 : Nat := 4983230072969 + 3 ^ 40 * 6132364 * 2
def baseEnd_6132364 : Nat := 1049616760109450110449259

theorem tailTrace_6132364 : CollatzResearch.WordTrace tailWord_6132364 prefixEnd_6132364 1049616760109450110449259 := by
  unfold tailWord_6132364
  simp only [CollatzResearch.WordTrace]
  refine ⟨111832844977750013617278073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149110459970333351489704097 111832844977750013617278073)
  ·
    refine ⟨83874633733312510212958555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111832844977750013617278073 83874633733312510212958555)
    ·
      refine ⟨125811950599968765319437833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83874633733312510212958555 125811950599968765319437833)
      ·
        refine ⟨94358962949976573989578375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125811950599968765319437833 94358962949976573989578375)
        ·
          refine ⟨141538444424964860984367563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94358962949976573989578375 141538444424964860984367563)
          ·
            refine ⟨212307666637447291476551345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141538444424964860984367563 212307666637447291476551345)
            ·
              refine ⟨159230749978085468607413509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212307666637447291476551345 159230749978085468607413509)
              ·
                refine ⟨29855765620891025363890033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159230749978085468607413509 29855765620891025363890033)
                ·
                  refine ⟨22391824215668269022917525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29855765620891025363890033 22391824215668269022917525)
                  ·
                    refine ⟨1049616760109450110449259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22391824215668269022917525 1049616760109450110449259)
                    ·
                      rfl

theorem cell23_6132364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_6132364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132364 prefixEnd_6132364 := by exact prefixLift 6132364
  have htrace : WordTrace (prefixWord ++ tailWord_6132364) baseStart_6132364 baseEnd_6132364 := by
    simpa [prefixWord, tailWord_6132364, baseEnd_6132364] using wordTrace_append hprefix tailTrace_6132364
  have hstable : (prefixWord ++ tailWord_6132364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132364).length < 2 ^ (prefixWord ++ tailWord_6132364).sum := by decide
  have hdescent : baseEnd_6132364 < baseStart_6132364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132371 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 3, 4, 2]
def baseStart_6132371 : Nat := 118140960795 + 6132371 * 2 ^ 59
def prefixEnd_6132371 : Nat := 4983230072969 + 3 ^ 40 * 6132371 * 2
def baseEnd_6132371 : Nat := 3148853874692931803960245

theorem tailTrace_6132371 : CollatzResearch.WordTrace tailWord_6132371 prefixEnd_6132371 3148853874692931803960245 := by
  unfold tailWord_6132371
  simp only [CollatzResearch.WordTrace]
  refine ⟨223665945266474667430060967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149110630177649778286707311 223665945266474667430060967)
  ·
    refine ⟨335498917899712001145091451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223665945266474667430060967 335498917899712001145091451)
    ·
      refine ⟨503248376849568001717637177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335498917899712001145091451 503248376849568001717637177)
      ·
        refine ⟨377436282637176001288227883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503248376849568001717637177 377436282637176001288227883)
        ·
          refine ⟨566154423955764001932341825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377436282637176001288227883 566154423955764001932341825)
          ·
            refine ⟨424615817966823001449256369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 566154423955764001932341825 424615817966823001449256369)
            ·
              refine ⟨318461863475117251086942277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424615817966823001449256369 318461863475117251086942277)
              ·
                refine ⟨59711599401584484578801677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 318461863475117251086942277 59711599401584484578801677)
                ·
                  refine ⟨22391849775594181717050629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59711599401584484578801677 22391849775594181717050629)
                  ·
                    refine ⟨4198471832923909071946993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22391849775594181717050629 4198471832923909071946993)
                    ·
                      refine ⟨3148853874692931803960245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4198471832923909071946993 3148853874692931803960245)
                      ·
                        rfl

theorem cell23_6132371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 4, 2].length) (baseStart_6132371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132371 prefixEnd_6132371 := by exact prefixLift 6132371
  have htrace : WordTrace (prefixWord ++ tailWord_6132371) baseStart_6132371 baseEnd_6132371 := by
    simpa [prefixWord, tailWord_6132371, baseEnd_6132371] using wordTrace_append hprefix tailTrace_6132371
  have hstable : (prefixWord ++ tailWord_6132371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132371).length < 2 ^ (prefixWord ++ tailWord_6132371).sum := by decide
  have hdescent : baseEnd_6132371 < baseStart_6132371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132388 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 1, 4, 2]
def baseStart_6132388 : Nat := 118140960795 + 6132388 * 2 ^ 59
def prefixEnd_6132388 : Nat := 4983230072969 + 3 ^ 40 * 6132388 * 2
def baseEnd_6132388 : Nat := 3148862603864058237447667

theorem tailTrace_6132388 : CollatzResearch.WordTrace tailWord_6132388 prefixEnd_6132388 3148862603864058237447667 := by
  unfold tailWord_6132388
  simp only [CollatzResearch.WordTrace]
  refine ⟨111833282653706539666714909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149111043538275386222286545 111833282653706539666714909)
  ·
    refine ⟨41937480995139952375018091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111833282653706539666714909 41937480995139952375018091)
    ·
      refine ⟨62906221492709928562527137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41937480995139952375018091 62906221492709928562527137)
      ·
        refine ⟨47179666119532446421895353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62906221492709928562527137 47179666119532446421895353)
        ·
          refine ⟨35384749589649334816421515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47179666119532446421895353 35384749589649334816421515)
          ·
            refine ⟨53077124384474002224632273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35384749589649334816421515 53077124384474002224632273)
            ·
              refine ⟨39807843288355501668474205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53077124384474002224632273 39807843288355501668474205)
              ·
                refine ⟨14927941233133313125677827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39807843288355501668474205 14927941233133313125677827)
                ·
                  refine ⟨22391911849699969688516741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14927941233133313125677827 22391911849699969688516741)
                  ·
                    refine ⟨4198483471818744316596889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22391911849699969688516741 4198483471818744316596889)
                    ·
                      refine ⟨3148862603864058237447667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4198483471818744316596889 3148862603864058237447667)
                      ·
                        rfl

theorem cell23_6132388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_6132388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132388 prefixEnd_6132388 := by exact prefixLift 6132388
  have htrace : WordTrace (prefixWord ++ tailWord_6132388) baseStart_6132388 baseEnd_6132388 := by
    simpa [prefixWord, tailWord_6132388, baseEnd_6132388] using wordTrace_append hprefix tailTrace_6132388
  have hstable : (prefixWord ++ tailWord_6132388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132388).length < 2 ^ (prefixWord ++ tailWord_6132388).sum := by decide
  have hdescent : baseEnd_6132388 < baseStart_6132388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132405 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 1, 4, 2]
def baseStart_6132405 : Nat := 118140960795 + 6132405 * 2 ^ 59
def prefixEnd_6132405 : Nat := 4983230072969 + 3 ^ 40 * 6132405 * 2
def baseEnd_6132405 : Nat := 3148871333035184670935089

theorem tailTrace_6132405 : CollatzResearch.WordTrace tailWord_6132405 prefixEnd_6132405 3148871333035184670935089 := by
  unfold tailWord_6132405
  simp only [CollatzResearch.WordTrace]
  refine ⟨223667185348351491236798669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149111456898900994157865779 223667185348351491236798669)
  ·
    refine ⟨83875194505631809213799501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223667185348351491236798669 83875194505631809213799501)
    ·
      refine ⟨31453197939611928455174813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83875194505631809213799501 31453197939611928455174813)
      ·
        refine ⟨11794949227354473170690555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31453197939611928455174813 11794949227354473170690555)
        ·
          refine ⟨17692423841031709756035833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11794949227354473170690555 17692423841031709756035833)
          ·
            refine ⟨13269317880773782317026875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17692423841031709756035833 13269317880773782317026875)
            ·
              refine ⟨19903976821160673475540313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13269317880773782317026875 19903976821160673475540313)
              ·
                refine ⟨14927982615870505106655235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19903976821160673475540313 14927982615870505106655235)
                ·
                  refine ⟨22391973923805757659982853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14927982615870505106655235 22391973923805757659982853)
                  ·
                    refine ⟨4198495110713579561246785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22391973923805757659982853 4198495110713579561246785)
                    ·
                      refine ⟨3148871333035184670935089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4198495110713579561246785 3148871333035184670935089)
                      ·
                        rfl

theorem cell23_6132405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_6132405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132405 prefixEnd_6132405 := by exact prefixLift 6132405
  have htrace : WordTrace (prefixWord ++ tailWord_6132405) baseStart_6132405 baseEnd_6132405 := by
    simpa [prefixWord, tailWord_6132405, baseEnd_6132405] using wordTrace_append hprefix tailTrace_6132405
  have hstable : (prefixWord ++ tailWord_6132405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132405).length < 2 ^ (prefixWord ++ tailWord_6132405).sum := by decide
  have hdescent : baseEnd_6132405 < baseStart_6132405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132471 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 7, 4]
def baseStart_6132471 : Nat := 118140960795 + 6132471 * 2 ^ 59
def prefixEnd_6132471 : Nat := 4983230072969 + 3 ^ 40 * 6132471 * 2
def baseEnd_6132471 : Nat := 1049635074252793804236595

theorem tailTrace_6132471 : CollatzResearch.WordTrace tailWord_6132471 prefixEnd_6132471 1049635074252793804236595 := by
  unfold tailWord_6132471
  simp only [CollatzResearch.WordTrace]
  refine ⟨223669592566112384508701267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149113061710741589672467511 223669592566112384508701267)
  ·
    refine ⟨335504388849168576763051901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223669592566112384508701267 335504388849168576763051901)
    ·
      refine ⟨125814145818438216286144463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335504388849168576763051901 125814145818438216286144463)
      ·
        refine ⟨188721218727657324429216695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125814145818438216286144463 188721218727657324429216695)
        ·
          refine ⟨283081828091485986643825043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188721218727657324429216695 283081828091485986643825043)
          ·
            refine ⟨424622742137228979965737565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283081828091485986643825043 424622742137228979965737565)
            ·
              refine ⟨159233528301460867487151587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 424622742137228979965737565 159233528301460867487151587)
              ·
                refine ⟨238850292452191301230727381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159233528301460867487151587 238850292452191301230727381)
                ·
                  refine ⟨5598053729348233622595173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 238850292452191301230727381 5598053729348233622595173)
                  ·
                    refine ⟨1049635074252793804236595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5598053729348233622595173 1049635074252793804236595)
                    ·
                      rfl

theorem cell23_6132471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_6132471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132471 prefixEnd_6132471 := by exact prefixLift 6132471
  have htrace : WordTrace (prefixWord ++ tailWord_6132471) baseStart_6132471 baseEnd_6132471 := by
    simpa [prefixWord, tailWord_6132471, baseEnd_6132471] using wordTrace_append hprefix tailTrace_6132471
  have hstable : (prefixWord ++ tailWord_6132471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132471).length < 2 ^ (prefixWord ++ tailWord_6132471).sum := by decide
  have hdescent : baseEnd_6132471 < baseStart_6132471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132488 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 3, 4]
def baseStart_6132488 : Nat := 118140960795 + 6132488 * 2 ^ 59
def prefixEnd_6132488 : Nat := 4983230072969 + 3 ^ 40 * 6132488 * 2
def baseEnd_6132488 : Nat := 1049637983976502615399069

theorem tailTrace_6132488 : CollatzResearch.WordTrace tailWord_6132488 prefixEnd_6132488 1049637983976502615399069 := by
  unfold tailWord_6132488
  simp only [CollatzResearch.WordTrace]
  refine ⟨111835106303525398206035059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149113475071367197608046745 111835106303525398206035059)
  ·
    refine ⟨167752659455288097309052589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111835106303525398206035059 167752659455288097309052589)
    ·
      refine ⟨62907247295733036490894721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167752659455288097309052589 62907247295733036490894721)
      ·
        refine ⟨47180435471799777368171041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62907247295733036490894721 47180435471799777368171041)
        ·
          refine ⟨35385326603849833026128281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47180435471799777368171041 35385326603849833026128281)
          ·
            refine ⟨26538994952887374769596211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35385326603849833026128281 26538994952887374769596211)
            ·
              refine ⟨39808492429331062154394317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26538994952887374769596211 39808492429331062154394317)
              ·
                refine ⟨14928184660999148307897869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39808492429331062154394317 14928184660999148307897869)
                ·
                  refine ⟨5598069247874680615461701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14928184660999148307897869 5598069247874680615461701)
                  ·
                    refine ⟨1049637983976502615399069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5598069247874680615461701 1049637983976502615399069)
                    ·
                      rfl

theorem cell23_6132488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_6132488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132488 prefixEnd_6132488 := by exact prefixLift 6132488
  have htrace : WordTrace (prefixWord ++ tailWord_6132488) baseStart_6132488 baseEnd_6132488 := by
    simpa [prefixWord, tailWord_6132488, baseEnd_6132488] using wordTrace_append hprefix tailTrace_6132488
  have hstable : (prefixWord ++ tailWord_6132488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132488).length < 2 ^ (prefixWord ++ tailWord_6132488).sum := by decide
  have hdescent : baseEnd_6132488 < baseStart_6132488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132528 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 5, 1, 3]
def baseStart_6132528 : Nat := 118140960795 + 6132528 * 2 ^ 59
def prefixEnd_6132528 : Nat := 4983230072969 + 3 ^ 40 * 6132528 * 2
def baseEnd_6132528 : Nat := 3148934491155687689697023

theorem tailTrace_6132528 : CollatzResearch.WordTrace tailWord_6132528 prefixEnd_6132528 3148934491155687689697023 := by
  unfold tailWord_6132528
  simp only [CollatzResearch.WordTrace]
  refine ⟨111835835763452941621763119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149114447684603922162350825 111835835763452941621763119)
  ·
    refine ⟨167753753645179412432644679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111835835763452941621763119 167753753645179412432644679)
    ·
      refine ⟨251630630467769118648967019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167753753645179412432644679 251630630467769118648967019)
      ·
        refine ⟨377445945701653677973450529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251630630467769118648967019 377445945701653677973450529)
        ·
          refine ⟨283084459276240258480087897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377445945701653677973450529 283084459276240258480087897)
          ·
            refine ⟨212313344457180193860065923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283084459276240258480087897 212313344457180193860065923)
            ·
              refine ⟨318470016685770290790098885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212313344457180193860065923 318470016685770290790098885)
              ·
                refine ⟨59713128128581929523143541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 318470016685770290790098885 59713128128581929523143541)
                ·
                  refine ⟨5598105762054555892794707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59713128128581929523143541 5598105762054555892794707)
                  ·
                    refine ⟨8397158643081833839192061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5598105762054555892794707 8397158643081833839192061)
                    ·
                      refine ⟨3148934491155687689697023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8397158643081833839192061 3148934491155687689697023)
                      ·
                        rfl

theorem cell23_6132528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 5, 1, 3].length) (baseStart_6132528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132528 prefixEnd_6132528 := by exact prefixLift 6132528
  have htrace : WordTrace (prefixWord ++ tailWord_6132528) baseStart_6132528 baseEnd_6132528 := by
    simpa [prefixWord, tailWord_6132528, baseEnd_6132528] using wordTrace_append hprefix tailTrace_6132528
  have hstable : (prefixWord ++ tailWord_6132528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132528).length < 2 ^ (prefixWord ++ tailWord_6132528).sum := by decide
  have hdescent : baseEnd_6132528 < baseStart_6132528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132532 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_6132532 : Nat := 118140960795 + 6132532 * 2 ^ 59
def prefixEnd_6132532 : Nat := 4983230072969 + 3 ^ 40 * 6132532 * 2
def baseEnd_6132532 : Nat := 3148936545078305674047005

theorem tailTrace_6132532 : CollatzResearch.WordTrace tailWord_6132532 prefixEnd_6132532 3148936545078305674047005 := by
  unfold tailWord_6132532
  simp only [CollatzResearch.WordTrace]
  refine ⟨111835908709445695963335925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149114544945927594617781233 111835908709445695963335925)
  ·
    refine ⟨10484616441510533996562743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111835908709445695963335925 10484616441510533996562743)
    ·
      refine ⟨15726924662265800994844115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10484616441510533996562743 15726924662265800994844115)
      ·
        refine ⟨23590386993398701492266173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15726924662265800994844115 23590386993398701492266173)
        ·
          refine ⟨8846395122524513059599815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23590386993398701492266173 8846395122524513059599815)
          ·
            refine ⟨13269592683786769589399723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8846395122524513059599815 13269592683786769589399723)
            ·
              refine ⟨19904389025680154384099585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13269592683786769589399723 19904389025680154384099585)
              ·
                refine ⟨14928291769260115788074689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19904389025680154384099585 14928291769260115788074689)
                ·
                  refine ⟨11196218826945086841056017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14928291769260115788074689 11196218826945086841056017)
                  ·
                    refine ⟨8397164120208815130792013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11196218826945086841056017 8397164120208815130792013)
                    ·
                      refine ⟨3148936545078305674047005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8397164120208815130792013 3148936545078305674047005)
                      ·
                        rfl

theorem cell23_6132532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_6132532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132532 prefixEnd_6132532 := by exact prefixLift 6132532
  have htrace : WordTrace (prefixWord ++ tailWord_6132532) baseStart_6132532 baseEnd_6132532 := by
    simpa [prefixWord, tailWord_6132532, baseEnd_6132532] using wordTrace_append hprefix tailTrace_6132532
  have hstable : (prefixWord ++ tailWord_6132532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132532).length < 2 ^ (prefixWord ++ tailWord_6132532).sum := by decide
  have hdescent : baseEnd_6132532 < baseStart_6132532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132551 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_6132551 : Nat := 118140960795 + 6132551 * 2 ^ 59
def prefixEnd_6132551 : Nat := 4983230072969 + 3 ^ 40 * 6132551 * 2
def baseEnd_6132551 : Nat := 3148946301210741099709417

theorem tailTrace_6132551 : CollatzResearch.WordTrace tailWord_6132551 prefixEnd_6132551 3148946301210741099709417 := by
  unfold tailWord_6132551
  simp only [CollatzResearch.WordTrace]
  refine ⟨223672510405822558171613507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149115006937215038781075671 223672510405822558171613507)
  ·
    refine ⟨335508765608733837257420261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223672510405822558171613507 335508765608733837257420261)
    ·
      refine ⟨62907893551637594485766299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335508765608733837257420261 62907893551637594485766299)
      ·
        refine ⟨94361840327456391728649449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62907893551637594485766299 94361840327456391728649449)
        ·
          refine ⟨70771380245592293796487087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94361840327456391728649449 70771380245592293796487087)
          ·
            refine ⟨106157070368388440694730631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70771380245592293796487087 106157070368388440694730631)
            ·
              refine ⟨159235605552582661042095947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106157070368388440694730631 159235605552582661042095947)
              ·
                refine ⟨238853408328873991563143921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159235605552582661042095947 238853408328873991563143921)
                ·
                  refine ⟨179140056246655493672357941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238853408328873991563143921 179140056246655493672357941)
                  ·
                    refine ⟨16794380273123952531783557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 179140056246655493672357941 16794380273123952531783557)
                    ·
                      refine ⟨3148946301210741099709417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16794380273123952531783557 3148946301210741099709417)
                      ·
                        rfl

theorem cell23_6132551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_6132551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132551 prefixEnd_6132551 := by exact prefixLift 6132551
  have htrace : WordTrace (prefixWord ++ tailWord_6132551) baseStart_6132551 baseEnd_6132551 := by
    simpa [prefixWord, tailWord_6132551, baseEnd_6132551] using wordTrace_append hprefix tailTrace_6132551
  have hstable : (prefixWord ++ tailWord_6132551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132551).length < 2 ^ (prefixWord ++ tailWord_6132551).sum := by decide
  have hdescent : baseEnd_6132551 < baseStart_6132551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132568 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 2, 6, 2]
def baseStart_6132568 : Nat := 118140960795 + 6132568 * 2 ^ 59
def prefixEnd_6132568 : Nat := 4983230072969 + 3 ^ 40 * 6132568 * 2
def baseEnd_6132568 : Nat := 3148955030381867533196839

theorem tailTrace_6132568 : CollatzResearch.WordTrace tailWord_6132568 prefixEnd_6132568 3148955030381867533196839 := by
  unfold tailWord_6132568
  simp only [CollatzResearch.WordTrace]
  refine ⟨111836565223380485037491179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149115420297840646716654905 111836565223380485037491179)
  ·
    refine ⟨167754847835070727556236769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111836565223380485037491179 167754847835070727556236769)
    ·
      refine ⟨125816135876303045667177577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167754847835070727556236769 125816135876303045667177577)
      ·
        refine ⟨94362101907227284250383183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125816135876303045667177577 94362101907227284250383183)
        ·
          refine ⟨141543152860840926375574775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94362101907227284250383183 141543152860840926375574775)
          ·
            refine ⟨212314729291261389563362163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141543152860840926375574775 212314729291261389563362163)
            ·
              refine ⟨318472093936892084345043245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212314729291261389563362163 318472093936892084345043245)
              ·
                refine ⟨119427035226334531629391217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318472093936892084345043245 119427035226334531629391217)
                ·
                  refine ⟨89570276419750898722043413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119427035226334531629391217 89570276419750898722043413)
                  ·
                    refine ⟨4198606707175823377595785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89570276419750898722043413 4198606707175823377595785)
                    ·
                      refine ⟨3148955030381867533196839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4198606707175823377595785 3148955030381867533196839)
                      ·
                        rfl

theorem cell23_6132568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_6132568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132568 prefixEnd_6132568 := by exact prefixLift 6132568
  have htrace : WordTrace (prefixWord ++ tailWord_6132568) baseStart_6132568 baseEnd_6132568 := by
    simpa [prefixWord, tailWord_6132568, baseEnd_6132568] using wordTrace_append hprefix tailTrace_6132568
  have hstable : (prefixWord ++ tailWord_6132568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132568).length < 2 ^ (prefixWord ++ tailWord_6132568).sum := by decide
  have hdescent : baseEnd_6132568 < baseStart_6132568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132572 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_6132572 : Nat := 118140960795 + 6132572 * 2 ^ 59
def prefixEnd_6132572 : Nat := 4983230072969 + 3 ^ 40 * 6132572 * 2
def baseEnd_6132572 : Nat := 3148957084304485517546821

theorem tailTrace_6132572 : CollatzResearch.WordTrace tailWord_6132572 prefixEnd_6132572 3148957084304485517546821 := by
  unfold tailWord_6132572
  simp only [CollatzResearch.WordTrace]
  refine ⟨111836638169373239379063985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149115517559164319172085313 111836638169373239379063985)
  ·
    refine ⟨83877478627029929534297989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111836638169373239379063985 83877478627029929534297989)
    ·
      refine ⟨15727027242568111787680873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83877478627029929534297989 15727027242568111787680873)
      ·
        refine ⟨11795270431926083840760655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15727027242568111787680873 11795270431926083840760655)
        ·
          refine ⟨17692905647889125761140983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11795270431926083840760655 17692905647889125761140983)
          ·
            refine ⟨26539358471833688641711475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17692905647889125761140983 26539358471833688641711475)
            ·
              refine ⟨39809037707750532962567213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26539358471833688641711475 39809037707750532962567213)
              ·
                refine ⟨14928389140406449860962705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39809037707750532962567213 14928389140406449860962705)
                ·
                  refine ⟨11196291855304837395722029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14928389140406449860962705 11196291855304837395722029)
                  ·
                    refine ⟨4198609445739314023395761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11196291855304837395722029 4198609445739314023395761)
                    ·
                      refine ⟨3148957084304485517546821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4198609445739314023395761 3148957084304485517546821)
                      ·
                        rfl

theorem cell23_6132572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_6132572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132572 prefixEnd_6132572 := by exact prefixLift 6132572
  have htrace : WordTrace (prefixWord ++ tailWord_6132572) baseStart_6132572 baseEnd_6132572 := by
    simpa [prefixWord, tailWord_6132572, baseEnd_6132572] using wordTrace_append hprefix tailTrace_6132572
  have hstable : (prefixWord ++ tailWord_6132572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132572).length < 2 ^ (prefixWord ++ tailWord_6132572).sum := by decide
  have hdescent : baseEnd_6132572 < baseStart_6132572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132615 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 4]
def baseStart_6132615 : Nat := 118140960795 + 6132615 * 2 ^ 59
def prefixEnd_6132615 : Nat := 4983230072969 + 3 ^ 40 * 6132615 * 2
def baseEnd_6132615 : Nat := 3148979163972628849309123

theorem tailTrace_6132615 : CollatzResearch.WordTrace tailWord_6132615 prefixEnd_6132615 3148979163972628849309123 := by
  unfold tailWord_6132615
  simp only [CollatzResearch.WordTrace]
  refine ⟨223674844677590697101943299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149116563118393798067962199 223674844677590697101943299)
  ·
    refine ⟨335512267016386045652914949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223674844677590697101943299 335512267016386045652914949)
    ·
      refine ⟨62908550065572383559921553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335512267016386045652914949 62908550065572383559921553)
      ·
        refine ⟨47181412549179287669941165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62908550065572383559921553 47181412549179287669941165)
        ·
          refine ⟨17693029705942232876227937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47181412549179287669941165 17693029705942232876227937)
          ·
            refine ⟨13269772279456674657170953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17693029705942232876227937 13269772279456674657170953)
            ·
              refine ⟨9952329209592505992878215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13269772279456674657170953 9952329209592505992878215)
              ·
                refine ⟨14928493814388758989317323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9952329209592505992878215 14928493814388758989317323)
                ·
                  refine ⟨22392740721583138483975985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14928493814388758989317323 22392740721583138483975985)
                  ·
                    refine ⟨16794555541187353862981989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22392740721583138483975985 16794555541187353862981989)
                    ·
                      refine ⟨3148979163972628849309123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16794555541187353862981989 3148979163972628849309123)
                      ·
                        rfl

theorem cell23_6132615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_6132615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132615 prefixEnd_6132615 := by exact prefixLift 6132615
  have htrace : WordTrace (prefixWord ++ tailWord_6132615) baseStart_6132615 baseEnd_6132615 := by
    simpa [prefixWord, tailWord_6132615, baseEnd_6132615] using wordTrace_append hprefix tailTrace_6132615
  have hstable : (prefixWord ++ tailWord_6132615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132615).length < 2 ^ (prefixWord ++ tailWord_6132615).sum := by decide
  have hdescent : baseEnd_6132615 < baseStart_6132615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132636 : List Nat := [2, 2, 3, 3, 3, 1, 2, 1, 1, 1, 4]
def baseStart_6132636 : Nat := 118140960795 + 6132636 * 2 ^ 59
def prefixEnd_6132636 : Nat := 4983230072969 + 3 ^ 40 * 6132636 * 2
def baseEnd_6132636 : Nat := 3148989947066373267146527

theorem tailTrace_6132636 : CollatzResearch.WordTrace tailWord_6132636 prefixEnd_6132636 3148989947066373267146527 := by
  unfold tailWord_6132636
  simp only [CollatzResearch.WordTrace]
  refine ⟨111837805305257308844228881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149117073740343078458971841 111837805305257308844228881)
  ·
    refine ⟨83878353978942981633171661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111837805305257308844228881 83878353978942981633171661)
    ·
      refine ⟨31454382742103618112439373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83878353978942981633171661 31454382742103618112439373)
      ·
        refine ⟨11795393528288856792164765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31454382742103618112439373 11795393528288856792164765)
        ·
          refine ⟨4423272573108321297061787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11795393528288856792164765 4423272573108321297061787)
          ·
            refine ⟨6634908859662481945592681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423272573108321297061787 6634908859662481945592681)
            ·
              refine ⟨4976181644746861459194511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6634908859662481945592681 4976181644746861459194511)
              ·
                refine ⟨7464272467120292188791767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4976181644746861459194511 7464272467120292188791767)
                ·
                  refine ⟨11196408700680438283187651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7464272467120292188791767 11196408700680438283187651)
                  ·
                    refine ⟨16794613051020657424781477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11196408700680438283187651 16794613051020657424781477)
                    ·
                      refine ⟨3148989947066373267146527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16794613051020657424781477 3148989947066373267146527)
                      ·
                        rfl

theorem cell23_6132636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_6132636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132636 prefixEnd_6132636 := by exact prefixLift 6132636
  have htrace : WordTrace (prefixWord ++ tailWord_6132636) baseStart_6132636 baseEnd_6132636 := by
    simpa [prefixWord, tailWord_6132636, baseEnd_6132636] using wordTrace_append hprefix tailTrace_6132636
  have hstable : (prefixWord ++ tailWord_6132636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132636).length < 2 ^ (prefixWord ++ tailWord_6132636).sum := by decide
  have hdescent : baseEnd_6132636 < baseStart_6132636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132639 : List Nat := [1, 1, 2, 5, 2, 3, 2, 1, 1, 2, 3]
def baseStart_6132639 : Nat := 118140960795 + 6132639 * 2 ^ 59
def prefixEnd_6132639 : Nat := 4983230072969 + 3 ^ 40 * 6132639 * 2
def baseEnd_6132639 : Nat := 3148991487508336755409013

theorem tailTrace_6132639 : CollatzResearch.WordTrace tailWord_6132639 prefixEnd_6132639 3148991487508336755409013 := by
  unfold tailWord_6132639
  simp only [CollatzResearch.WordTrace]
  refine ⟨223675720029503749200816971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149117146686335832800544647 223675720029503749200816971)
  ·
    refine ⟨335513580044255623801225457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223675720029503749200816971 335513580044255623801225457)
    ·
      refine ⟨251635185033191717850919093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335513580044255623801225457 251635185033191717850919093)
      ·
        refine ⟨23590798596861723548523665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 251635185033191717850919093 23590798596861723548523665)
        ·
          refine ⟨17693098947646292661392749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23590798596861723548523665 17693098947646292661392749)
          ·
            refine ⟨6634912105367359748022281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17693098947646292661392749 6634912105367359748022281)
            ·
              refine ⟨4976184079025519811016711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6634912105367359748022281 4976184079025519811016711)
              ·
                refine ⟨7464276118538279716525067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4976184079025519811016711 7464276118538279716525067)
                ·
                  refine ⟨11196414177807419574787601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7464276118538279716525067 11196414177807419574787601)
                  ·
                    refine ⟨8397310633355564681090701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11196414177807419574787601 8397310633355564681090701)
                    ·
                      refine ⟨3148991487508336755409013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8397310633355564681090701 3148991487508336755409013)
                      ·
                        rfl

theorem cell23_6132639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_6132639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132639 prefixEnd_6132639 := by exact prefixLift 6132639
  have htrace : WordTrace (prefixWord ++ tailWord_6132639) baseStart_6132639 baseEnd_6132639 := by
    simpa [prefixWord, tailWord_6132639, baseEnd_6132639] using wordTrace_append hprefix tailTrace_6132639
  have hstable : (prefixWord ++ tailWord_6132639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132639).length < 2 ^ (prefixWord ++ tailWord_6132639).sum := by decide
  have hdescent : baseEnd_6132639 < baseStart_6132639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132651 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 3, 8]
def baseStart_6132651 : Nat := 118140960795 + 6132651 * 2 ^ 59
def prefixEnd_6132651 : Nat := 4983230072969 + 3 ^ 40 * 6132651 * 2
def baseEnd_6132651 : Nat := 1049665883092063569486319

theorem tailTrace_6132651 : CollatzResearch.WordTrace tailWord_6132651 prefixEnd_6132651 1049665883092063569486319 := by
  unfold tailWord_6132651
  simp only [CollatzResearch.WordTrace]
  refine ⟨223676157705460275250253807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149117438470306850166835871 223676157705460275250253807)
  ·
    refine ⟨335514236558190412875380711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223676157705460275250253807 335514236558190412875380711)
    ·
      refine ⟨503271354837285619313071067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335514236558190412875380711 503271354837285619313071067)
      ·
        refine ⟨754907032255928428969606601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503271354837285619313071067 754907032255928428969606601)
        ·
          refine ⟨566180274191946321727204951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 754907032255928428969606601 566180274191946321727204951)
          ·
            refine ⟨849270411287919482590807427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566180274191946321727204951 849270411287919482590807427)
            ·
              refine ⟨1273905616931879223886211141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849270411287919482590807427 1273905616931879223886211141)
              ·
                refine ⟨238857303174727354478664589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1273905616931879223886211141 238857303174727354478664589)
                ·
                  refine ⟨89571488690522757929499221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238857303174727354478664589 89571488690522757929499221)
                  ·
                    refine ⟨1049665883092063569486319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89571488690522757929499221 1049665883092063569486319)
                    ·
                      rfl

theorem cell23_6132651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 8].length) (baseStart_6132651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132651 prefixEnd_6132651 := by exact prefixLift 6132651
  have htrace : WordTrace (prefixWord ++ tailWord_6132651) baseStart_6132651 baseEnd_6132651 := by
    simpa [prefixWord, tailWord_6132651, baseEnd_6132651] using wordTrace_append hprefix tailTrace_6132651
  have hstable : (prefixWord ++ tailWord_6132651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132651).length < 2 ^ (prefixWord ++ tailWord_6132651).sum := by decide
  have hdescent : baseEnd_6132651 < baseStart_6132651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132669 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 1, 3, 3]
def baseStart_6132669 : Nat := 118140960795 + 6132669 * 2 ^ 59
def prefixEnd_6132669 : Nat := 4983230072969 + 3 ^ 40 * 6132669 * 2
def baseEnd_6132669 : Nat := 3149006891927971638033875

theorem tailTrace_6132669 : CollatzResearch.WordTrace tailWord_6132669 prefixEnd_6132669 3149006891927971638033875 := by
  unfold tailWord_6132669
  simp only [CollatzResearch.WordTrace]
  refine ⟨223676814219395064324409061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149117876146263376216272707 223676814219395064324409061)
  ·
    refine ⟨41939402666136574560826699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223676814219395064324409061 41939402666136574560826699)
    ·
      refine ⟨62909103999204861841240049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41939402666136574560826699 62909103999204861841240049)
      ·
        refine ⟨47181827999403646380930037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62909103999204861841240049 47181827999403646380930037)
        ·
          refine ⟨4423296374944091848212191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47181827999403646380930037 4423296374944091848212191)
          ·
            refine ⟨6634944562416137772318287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423296374944091848212191 6634944562416137772318287)
            ·
              refine ⟨9952416843624206658477431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6634944562416137772318287 9952416843624206658477431)
              ·
                refine ⟨14928625265436309987716147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9952416843624206658477431 14928625265436309987716147)
                ·
                  refine ⟨22392937898154464981574221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14928625265436309987716147 22392937898154464981574221)
                  ·
                    refine ⟨8397351711807924368090333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22392937898154464981574221 8397351711807924368090333)
                    ·
                      refine ⟨3149006891927971638033875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8397351711807924368090333 3149006891927971638033875)
                      ·
                        rfl

theorem cell23_6132669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_6132669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132669 prefixEnd_6132669 := by exact prefixLift 6132669
  have htrace : WordTrace (prefixWord ++ tailWord_6132669) baseStart_6132669 baseEnd_6132669 := by
    simpa [prefixWord, tailWord_6132669, baseEnd_6132669] using wordTrace_append hprefix tailTrace_6132669
  have hstable : (prefixWord ++ tailWord_6132669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132669).length < 2 ^ (prefixWord ++ tailWord_6132669).sum := by decide
  have hdescent : baseEnd_6132669 < baseStart_6132669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132726 : List Nat := [5, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2]
def baseStart_6132726 : Nat := 118140960795 + 6132726 * 2 ^ 59
def prefixEnd_6132726 : Nat := 4983230072969 + 3 ^ 40 * 6132726 * 2
def baseEnd_6132726 : Nat := 3149036160325277915021113

theorem tailTrace_6132726 : CollatzResearch.WordTrace tailWord_6132726 prefixEnd_6132726 3149036160325277915021113 := by
  unfold tailWord_6132726
  simp only [CollatzResearch.WordTrace]
  refine ⟨13979930823761785191202127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149119262120125708706156021 13979930823761785191202127)
  ·
    refine ⟨20969896235642677786803191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13979930823761785191202127 20969896235642677786803191)
    ·
      refine ⟨31454844353464016680204787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20969896235642677786803191 31454844353464016680204787)
      ·
        refine ⟨47182266530196025020307181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31454844353464016680204787 47182266530196025020307181)
        ·
          refine ⟨17693349948823509382615193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47182266530196025020307181 17693349948823509382615193)
          ·
            refine ⟨13270012461617632036961395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17693349948823509382615193 13270012461617632036961395)
            ·
              refine ⟨19905018692426448055442093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13270012461617632036961395 19905018692426448055442093)
              ·
                refine ⟨7464382009659918020790785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19905018692426448055442093 7464382009659918020790785)
                ·
                  refine ⟨5598286507244938515593089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7464382009659918020790785 5598286507244938515593089)
                  ·
                    refine ⟨4198714880433703886694817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5598286507244938515593089 4198714880433703886694817)
                    ·
                      refine ⟨3149036160325277915021113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4198714880433703886694817 3149036160325277915021113)
                      ·
                        rfl

theorem cell23_6132726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_6132726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132726 prefixEnd_6132726 := by exact prefixLift 6132726
  have htrace : WordTrace (prefixWord ++ tailWord_6132726) baseStart_6132726 baseEnd_6132726 := by
    simpa [prefixWord, tailWord_6132726, baseEnd_6132726] using wordTrace_append hprefix tailTrace_6132726
  have hstable : (prefixWord ++ tailWord_6132726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132726).length < 2 ^ (prefixWord ++ tailWord_6132726).sum := by decide
  have hdescent : baseEnd_6132726 < baseStart_6132726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132728 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 6, 5]
def baseStart_6132728 : Nat := 118140960795 + 6132728 * 2 ^ 59
def prefixEnd_6132728 : Nat := 4983230072969 + 3 ^ 40 * 6132728 * 2
def baseEnd_6132728 : Nat := 1049679062428862302398701

theorem tailTrace_6132728 : CollatzResearch.WordTrace tailWord_6132728 prefixEnd_6132728 1049679062428862302398701 := by
  unfold tailWord_6132728
  simp only [CollatzResearch.WordTrace]
  refine ⟨111839483063090658700403419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149119310750787544933871225 111839483063090658700403419)
  ·
    refine ⟨167759224594635988050605129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111839483063090658700403419 167759224594635988050605129)
    ·
      refine ⟨125819418445976991037953847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167759224594635988050605129 125819418445976991037953847)
      ·
        refine ⟨188729127668965486556930771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125819418445976991037953847 188729127668965486556930771)
        ·
          refine ⟨283093691503448229835396157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188729127668965486556930771 283093691503448229835396157)
          ·
            refine ⟨106160134313793086188273559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283093691503448229835396157 106160134313793086188273559)
            ·
              refine ⟨159240201470689629282410339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106160134313793086188273559 159240201470689629282410339)
              ·
                refine ⟨238860302206034443923615509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159240201470689629282410339 238860302206034443923615509)
                ·
                  refine ⟨11196576665907864558919477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 238860302206034443923615509 11196576665907864558919477)
                  ·
                    refine ⟨1049679062428862302398701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11196576665907864558919477 1049679062428862302398701)
                    ·
                      rfl

theorem cell23_6132728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_6132728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132728 prefixEnd_6132728 := by exact prefixLift 6132728
  have htrace : WordTrace (prefixWord ++ tailWord_6132728) baseStart_6132728 baseEnd_6132728 := by
    simpa [prefixWord, tailWord_6132728, baseEnd_6132728] using wordTrace_append hprefix tailTrace_6132728
  have hstable : (prefixWord ++ tailWord_6132728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132728).length < 2 ^ (prefixWord ++ tailWord_6132728).sum := by decide
  have hdescent : baseEnd_6132728 < baseStart_6132728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132785 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 1, 4, 3]
def baseStart_6132785 : Nat := 118140960795 + 6132785 * 2 ^ 59
def prefixEnd_6132785 : Nat := 4983230072969 + 3 ^ 40 * 6132785 * 2
def baseEnd_6132785 : Nat := 3149066455683893184183341

theorem tailTrace_6132785 : CollatzResearch.WordTrace tailWord_6132785 prefixEnd_6132785 3149066455683893184183341 := by
  unfold tailWord_6132785
  simp only [CollatzResearch.WordTrace]
  refine ⟨223681045086974816135631809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149120696724649877423754539 223681045086974816135631809)
  ·
    refine ⟨167760783815231112101723857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223681045086974816135631809 167760783815231112101723857)
    ·
      refine ⟨125820587861423334076292893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167760783815231112101723857 125820587861423334076292893)
      ·
        refine ⟨47182720448033750278609835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125820587861423334076292893 47182720448033750278609835)
        ·
          refine ⟨70774080672050625417914753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47182720448033750278609835 70774080672050625417914753)
          ·
            refine ⟨53080560504037969063436065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70774080672050625417914753 53080560504037969063436065)
            ·
              refine ⟨39810420378028476797577049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53080560504037969063436065 39810420378028476797577049)
              ·
                refine ⟨29857815283521357598182787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39810420378028476797577049 29857815283521357598182787)
                ·
                  refine ⟨44786722925282036397274181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29857815283521357598182787 44786722925282036397274181)
                  ·
                    refine ⟨8397510548490381824488909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44786722925282036397274181 8397510548490381824488909)
                    ·
                      refine ⟨3149066455683893184183341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8397510548490381824488909 3149066455683893184183341)
                      ·
                        rfl

theorem cell23_6132785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_6132785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132785 prefixEnd_6132785 := by exact prefixLift 6132785
  have htrace : WordTrace (prefixWord ++ tailWord_6132785) baseStart_6132785 baseEnd_6132785 := by
    simpa [prefixWord, tailWord_6132785, baseEnd_6132785] using wordTrace_append hprefix tailTrace_6132785
  have hstable : (prefixWord ++ tailWord_6132785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132785).length < 2 ^ (prefixWord ++ tailWord_6132785).sum := by decide
  have hdescent : baseEnd_6132785 < baseStart_6132785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132792 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 3, 4]
def baseStart_6132792 : Nat := 118140960795 + 6132792 * 2 ^ 59
def prefixEnd_6132792 : Nat := 4983230072969 + 3 ^ 40 * 6132792 * 2
def baseEnd_6132792 : Nat := 1049690016682824885598603

theorem tailTrace_6132792 : CollatzResearch.WordTrace tailWord_6132792 prefixEnd_6132792 1049690016682824885598603 := by
  unfold tailWord_6132792
  simp only [CollatzResearch.WordTrace]
  refine ⟨111840650198974728165568315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149120866931966304220757753 111840650198974728165568315)
  ·
    refine ⟨167760975298462092248352473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111840650198974728165568315 167760975298462092248352473)
    ·
      refine ⟨125820731473846569186264355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167760975298462092248352473 125820731473846569186264355)
      ·
        refine ⟨188731097210769853779396533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125820731473846569186264355 188731097210769853779396533)
        ·
          refine ⟨17693540363509673791818425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188731097210769853779396533 17693540363509673791818425)
          ·
            refine ⟨13270155272632255343863819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17693540363509673791818425 13270155272632255343863819)
            ·
              refine ⟨19905232908948383015795729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13270155272632255343863819 19905232908948383015795729)
              ·
                refine ⟨14928924681711287261846797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19905232908948383015795729 14928924681711287261846797)
                ·
                  refine ⟨5598346755641732723192549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14928924681711287261846797 5598346755641732723192549)
                  ·
                    refine ⟨1049690016682824885598603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5598346755641732723192549 1049690016682824885598603)
                    ·
                      rfl

theorem cell23_6132792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_6132792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132792 prefixEnd_6132792 := by exact prefixLift 6132792
  have htrace : WordTrace (prefixWord ++ tailWord_6132792) baseStart_6132792 baseEnd_6132792 := by
    simpa [prefixWord, tailWord_6132792, baseEnd_6132792] using wordTrace_append hprefix tailTrace_6132792
  have hstable : (prefixWord ++ tailWord_6132792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132792).length < 2 ^ (prefixWord ++ tailWord_6132792).sum := by decide
  have hdescent : baseEnd_6132792 < baseStart_6132792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132885 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_6132885 : Nat := 118140960795 + 6132885 * 2 ^ 59
def prefixEnd_6132885 : Nat := 4983230072969 + 3 ^ 40 * 6132885 * 2
def baseEnd_6132885 : Nat := 3149117803749342792932881

theorem tailTrace_6132885 : CollatzResearch.WordTrace tailWord_6132885 prefixEnd_6132885 3149117803749342792932881 := by
  unfold tailWord_6132885
  simp only [CollatzResearch.WordTrace]
  refine ⟨223684692386612533214272109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149123128257741688809514739 223684692386612533214272109)
  ·
    refine ⟨83881759644979699955352041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223684692386612533214272109 83881759644979699955352041)
    ·
      refine ⟨62911319733734774966514031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83881759644979699955352041 62911319733734774966514031)
      ·
        refine ⟨94366979600602162449771047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62911319733734774966514031 94366979600602162449771047)
        ·
          refine ⟨141550469400903243674656571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94366979600602162449771047 141550469400903243674656571)
          ·
            refine ⟨212325704101354865511984857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141550469400903243674656571 212325704101354865511984857)
            ·
              refine ⟨159244278076016149133988643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212325704101354865511984857 159244278076016149133988643)
              ·
                refine ⟨238866417114024223700982965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159244278076016149133988643 238866417114024223700982965)
                ·
                  refine ⟨22393726604439770971967153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 238866417114024223700982965 22393726604439770971967153)
                  ·
                    refine ⟨16795294953329828228975365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22393726604439770971967153 16795294953329828228975365)
                    ·
                      refine ⟨3149117803749342792932881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16795294953329828228975365 3149117803749342792932881)
                      ·
                        rfl

theorem cell23_6132885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_6132885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132885 prefixEnd_6132885 := by exact prefixLift 6132885
  have htrace : WordTrace (prefixWord ++ tailWord_6132885) baseStart_6132885 baseEnd_6132885 := by
    simpa [prefixWord, tailWord_6132885, baseEnd_6132885] using wordTrace_append hprefix tailTrace_6132885
  have hstable : (prefixWord ++ tailWord_6132885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132885).length < 2 ^ (prefixWord ++ tailWord_6132885).sum := by decide
  have hdescent : baseEnd_6132885 < baseStart_6132885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132892 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_6132892 : Nat := 118140960795 + 6132892 * 2 ^ 59
def prefixEnd_6132892 : Nat := 4983230072969 + 3 ^ 40 * 6132892 * 2
def baseEnd_6132892 : Nat := 3149121398113924265545349

theorem tailTrace_6132892 : CollatzResearch.WordTrace tailWord_6132892 prefixEnd_6132892 3149121398113924265545349 := by
  unfold tailWord_6132892
  simp only [CollatzResearch.WordTrace]
  refine ⟨111842473848793586704888465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149123298465058115606517953 111842473848793586704888465)
  ·
    refine ⟨83881855386595190028666349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111842473848793586704888465 83881855386595190028666349)
    ·
      refine ⟨31455695769973196260749881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83881855386595190028666349 31455695769973196260749881)
      ·
        refine ⟨23591771827479897195562411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31455695769973196260749881 23591771827479897195562411)
        ·
          refine ⟨35387657741219845793343617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23591771827479897195562411 35387657741219845793343617)
          ·
            refine ⟨26540743305914884345007713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35387657741219845793343617 26540743305914884345007713)
            ·
              refine ⟨19905557479436163258755785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26540743305914884345007713 19905557479436163258755785)
              ·
                refine ⟨14929168109577122444066839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19905557479436163258755785 14929168109577122444066839)
                ·
                  refine ⟨22393752164365683666100259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14929168109577122444066839 22393752164365683666100259)
                  ·
                    refine ⟨33590628246548525499150389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22393752164365683666100259 33590628246548525499150389)
                    ·
                      refine ⟨3149121398113924265545349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33590628246548525499150389 3149121398113924265545349)
                      ·
                        rfl

theorem cell23_6132892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_6132892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132892 prefixEnd_6132892 := by exact prefixLift 6132892
  have htrace : WordTrace (prefixWord ++ tailWord_6132892) baseStart_6132892 baseEnd_6132892 := by
    simpa [prefixWord, tailWord_6132892, baseEnd_6132892] using wordTrace_append hprefix tailTrace_6132892
  have hstable : (prefixWord ++ tailWord_6132892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132892).length < 2 ^ (prefixWord ++ tailWord_6132892).sum := by decide
  have hdescent : baseEnd_6132892 < baseStart_6132892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132906 : List Nat := [3, 1, 5, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_6132906 : Nat := 118140960795 + 6132906 * 2 ^ 59
def prefixEnd_6132906 : Nat := 4983230072969 + 3 ^ 40 * 6132906 * 2
def baseEnd_6132906 : Nat := 3149128586843087210770285

theorem tailTrace_6132906 : CollatzResearch.WordTrace tailWord_6132906 prefixEnd_6132906 3149128586843087210770285 := by
  unfold tailWord_6132906
  simp only [CollatzResearch.WordTrace]
  refine ⟨55921364579884113450196643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149123638879690969200524381 55921364579884113450196643)
  ·
    refine ⟨83882046869826170175294965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55921364579884113450196643 83882046869826170175294965)
    ·
      refine ⟨7863941894046203453933903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83882046869826170175294965 7863941894046203453933903)
      ·
        refine ⟨11795912841069305180900855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7863941894046203453933903 11795912841069305180900855)
        ·
          refine ⟨17693869261603957771351283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11795912841069305180900855 17693869261603957771351283)
          ·
            refine ⟨26540803892405936657026925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17693869261603957771351283 26540803892405936657026925)
            ·
              refine ⟨9952801459652226246385097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26540803892405936657026925 9952801459652226246385097)
              ·
                refine ⟨7464601094739169684788823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9952801459652226246385097 7464601094739169684788823)
                ·
                  refine ⟨11196901642108754527183235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7464601094739169684788823 11196901642108754527183235)
                  ·
                    refine ⟨16795352463163131790774853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11196901642108754527183235 16795352463163131790774853)
                    ·
                      refine ⟨3149128586843087210770285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16795352463163131790774853 3149128586843087210770285)
                      ·
                        rfl

theorem cell23_6132906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_6132906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132906 prefixEnd_6132906 := by exact prefixLift 6132906
  have htrace : WordTrace (prefixWord ++ tailWord_6132906) baseStart_6132906 baseEnd_6132906 := by
    simpa [prefixWord, tailWord_6132906, baseEnd_6132906] using wordTrace_append hprefix tailTrace_6132906
  have hstable : (prefixWord ++ tailWord_6132906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132906).length < 2 ^ (prefixWord ++ tailWord_6132906).sum := by decide
  have hdescent : baseEnd_6132906 < baseStart_6132906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132935 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_6132935 : Nat := 118140960795 + 6132935 * 2 ^ 59
def prefixEnd_6132935 : Nat := 4983230072969 + 3 ^ 40 * 6132935 * 2
def baseEnd_6132935 : Nat := 3149143477782067597307651

theorem tailTrace_6132935 : CollatzResearch.WordTrace tailWord_6132935 prefixEnd_6132935 3149143477782067597307651 := by
  unfold tailWord_6132935
  simp only [CollatzResearch.WordTrace]
  refine ⟨223686516036431391753592259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149124344024287594502394839 223686516036431391753592259)
  ·
    refine ⟨335529774054647087630388389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223686516036431391753592259 335529774054647087630388389)
    ·
      refine ⟨62911832635246328930697823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335529774054647087630388389 62911832635246328930697823)
      ·
        refine ⟨94367748952869493396046735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62911832635246328930697823 94367748952869493396046735)
        ·
          refine ⟨141551623429304240094070103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94367748952869493396046735 141551623429304240094070103)
          ·
            refine ⟨212327435143956360141105155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141551623429304240094070103 212327435143956360141105155)
            ·
              refine ⟨318491152715934540211657733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212327435143956360141105155 318491152715934540211657733)
              ·
                refine ⟨59717091134237726289685825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 318491152715934540211657733 59717091134237726289685825)
                ·
                  refine ⟨44787818350678294717264369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59717091134237726289685825 44787818350678294717264369)
                  ·
                    refine ⟨33590863763008721037948277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44787818350678294717264369 33590863763008721037948277)
                    ·
                      refine ⟨3149143477782067597307651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33590863763008721037948277 3149143477782067597307651)
                      ·
                        rfl

theorem cell23_6132935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_6132935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132935 prefixEnd_6132935 := by exact prefixLift 6132935
  have htrace : WordTrace (prefixWord ++ tailWord_6132935) baseStart_6132935 baseEnd_6132935 := by
    simpa [prefixWord, tailWord_6132935, baseEnd_6132935] using wordTrace_append hprefix tailTrace_6132935
  have hstable : (prefixWord ++ tailWord_6132935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132935).length < 2 ^ (prefixWord ++ tailWord_6132935).sum := by decide
  have hdescent : baseEnd_6132935 < baseStart_6132935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132979 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 1, 4, 2]
def baseStart_6132979 : Nat := 118140960795 + 6132979 * 2 ^ 59
def prefixEnd_6132979 : Nat := 4983230072969 + 3 ^ 40 * 6132979 * 2
def baseEnd_6132979 : Nat := 3149166070930865425157449

theorem tailTrace_6132979 : CollatzResearch.WordTrace tailWord_6132979 prefixEnd_6132979 3149166070930865425157449 := by
  unfold tailWord_6132979
  simp only [CollatzResearch.WordTrace]
  refine ⟨223688120848271987268193991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149125413898847991512129327 223688120848271987268193991)
  ·
    refine ⟨335532181272407980902290987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223688120848271987268193991 335532181272407980902290987)
    ·
      refine ⟨503298271908611971353436481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335532181272407980902290987 503298271908611971353436481)
      ·
        refine ⟨377473703931458978515077361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503298271908611971353436481 377473703931458978515077361)
        ·
          refine ⟨283105277948594233886308021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377473703931458978515077361 283105277948594233886308021)
          ·
            refine ⟨26541119807680709426841377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 283105277948594233886308021 26541119807680709426841377)
            ·
              refine ⟨19905839855760532070131033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26541119807680709426841377 19905839855760532070131033)
              ·
                refine ⟨14929379891820399052598275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19905839855760532070131033 14929379891820399052598275)
                ·
                  refine ⟨22394069837730598578897413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14929379891820399052598275 22394069837730598578897413)
                  ·
                    refine ⟨4198888094574487233543265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22394069837730598578897413 4198888094574487233543265)
                    ·
                      refine ⟨3149166070930865425157449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4198888094574487233543265 3149166070930865425157449)
                      ·
                        rfl

theorem cell23_6132979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 4, 2].length) (baseStart_6132979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132979 prefixEnd_6132979 := by exact prefixLift 6132979
  have htrace : WordTrace (prefixWord ++ tailWord_6132979) baseStart_6132979 baseEnd_6132979 := by
    simpa [prefixWord, tailWord_6132979, baseEnd_6132979] using wordTrace_append hprefix tailTrace_6132979
  have hstable : (prefixWord ++ tailWord_6132979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132979).length < 2 ^ (prefixWord ++ tailWord_6132979).sum := by decide
  have hdescent : baseEnd_6132979 < baseStart_6132979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132982 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_6132982 : Nat := 118140960795 + 6132982 * 2 ^ 59
def prefixEnd_6132982 : Nat := 4983230072969 + 3 ^ 40 * 6132982 * 2
def baseEnd_6132982 : Nat := 3149167611372828913419935

theorem tailTrace_6132982 : CollatzResearch.WordTrace tailWord_6132982 prefixEnd_6132982 3149167611372828913419935 := by
  unfold tailWord_6132982
  simp only [CollatzResearch.WordTrace]
  refine ⟨13980514391703819923784575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149125486844840745853702133 13980514391703819923784575)
  ·
    refine ⟨20970771587555729885676863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13980514391703819923784575 20970771587555729885676863)
    ·
      refine ⟨31456157381333594828515295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20970771587555729885676863 31456157381333594828515295)
      ·
        refine ⟨47184236072000392242772943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31456157381333594828515295 47184236072000392242772943)
        ·
          refine ⟨70776354108000588364159415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47184236072000392242772943 70776354108000588364159415)
          ·
            refine ⟨106164531162000882546239123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70776354108000588364159415 106164531162000882546239123)
            ·
              refine ⟨159246796743001323819358685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106164531162000882546239123 159246796743001323819358685)
              ·
                refine ⟨59717548778625496432259507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159246796743001323819358685 59717548778625496432259507)
                ·
                  refine ⟨89576323167938244648389261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59717548778625496432259507 89576323167938244648389261)
                  ·
                    refine ⟨33591121187976841743145973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89576323167938244648389261 33591121187976841743145973)
                    ·
                      refine ⟨3149167611372828913419935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33591121187976841743145973 3149167611372828913419935)
                      ·
                        rfl

theorem cell23_6132982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_6132982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132982 prefixEnd_6132982 := by exact prefixLift 6132982
  have htrace : WordTrace (prefixWord ++ tailWord_6132982) baseStart_6132982 baseEnd_6132982 := by
    simpa [prefixWord, tailWord_6132982, baseEnd_6132982] using wordTrace_append hprefix tailTrace_6132982
  have hstable : (prefixWord ++ tailWord_6132982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132982).length < 2 ^ (prefixWord ++ tailWord_6132982).sum := by decide
  have hdescent : baseEnd_6132982 < baseStart_6132982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6132985 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 9]
def baseStart_6132985 : Nat := 118140960795 + 6132985 * 2 ^ 59
def prefixEnd_6132985 : Nat := 4983230072969 + 3 ^ 40 * 6132985 * 2
def baseEnd_6132985 : Nat := 349907683534976933520269

theorem tailTrace_6132985 : CollatzResearch.WordTrace tailWord_6132985 prefixEnd_6132985 349907683534976933520269 := by
  unfold tailWord_6132985
  simp only [CollatzResearch.WordTrace]
  refine ⟨223688339686250250292912409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149125559790833500195274939 223688339686250250292912409)
  ·
    refine ⟨167766254764687687719684307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223688339686250250292912409 167766254764687687719684307)
    ·
      refine ⟨251649382147031531579526461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167766254764687687719684307 251649382147031531579526461)
      ·
        refine ⟨94368518305136824342322423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251649382147031531579526461 94368518305136824342322423)
        ·
          refine ⟨141552777457705236513483635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94368518305136824342322423 141552777457705236513483635)
          ·
            refine ⟨212329166186557854770225453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141552777457705236513483635 212329166186557854770225453)
            ·
              refine ⟨79623437319959195538834545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212329166186557854770225453 79623437319959195538834545)
              ·
                refine ⟨59717577989969396654125909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79623437319959195538834545 59717577989969396654125909)
                ·
                  refine ⟨349907683534976933520269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59717577989969396654125909 349907683534976933520269)
                  ·
                    rfl

theorem cell23_6132985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 9].length) (baseStart_6132985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6132985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6132985 prefixEnd_6132985 := by exact prefixLift 6132985
  have htrace : WordTrace (prefixWord ++ tailWord_6132985) baseStart_6132985 baseEnd_6132985 := by
    simpa [prefixWord, tailWord_6132985, baseEnd_6132985] using wordTrace_append hprefix tailTrace_6132985
  have hstable : (prefixWord ++ tailWord_6132985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6132985).length < 2 ^ (prefixWord ++ tailWord_6132985).sum := by decide
  have hdescent : baseEnd_6132985 < baseStart_6132985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6132985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133053 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 7]
def baseStart_6133053 : Nat := 118140960795 + 6133053 * 2 ^ 59
def prefixEnd_6133053 : Nat := 4983230072969 + 3 ^ 40 * 6133053 * 2
def baseEnd_6133053 : Nat := 349911563166588681736901

theorem tailTrace_6133053 : CollatzResearch.WordTrace tailWord_6133053 prefixEnd_6133053 349911563166588681736901 := by
  unfold tailWord_6133053
  simp only [CollatzResearch.WordTrace]
  refine ⟨223690819850003897906387813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149127213233335931937591875 223690819850003897906387813)
  ·
    refine ⟨41942028721875730857447715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223690819850003897906387813 41942028721875730857447715)
    ·
      refine ⟨62913043082813596286171573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41942028721875730857447715 62913043082813596286171573)
      ·
        refine ⟨5898097789013774651828585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62913043082813596286171573 5898097789013774651828585)
        ·
          refine ⟨4423573341760330988871439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5898097789013774651828585 4423573341760330988871439)
          ·
            refine ⟨6635360012640496483307159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423573341760330988871439 6635360012640496483307159)
            ·
              refine ⟨9953040018960744724960739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6635360012640496483307159 9953040018960744724960739)
              ·
                refine ⟨14929560028441117087441109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9953040018960744724960739 14929560028441117087441109)
                ·
                  refine ⟨349911563166588681736901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14929560028441117087441109 349911563166588681736901)
                  ·
                    rfl

theorem cell23_6133053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_6133053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133053 prefixEnd_6133053 := by exact prefixLift 6133053
  have htrace : WordTrace (prefixWord ++ tailWord_6133053) baseStart_6133053 baseEnd_6133053 := by
    simpa [prefixWord, tailWord_6133053, baseEnd_6133053] using wordTrace_append hprefix tailTrace_6133053
  have hstable : (prefixWord ++ tailWord_6133053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133053).length < 2 ^ (prefixWord ++ tailWord_6133053).sum := by decide
  have hdescent : baseEnd_6133053 < baseStart_6133053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133082 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4]
def baseStart_6133082 : Nat := 118140960795 + 6133082 * 2 ^ 59
def prefixEnd_6133082 : Nat := 4983230072969 + 3 ^ 40 * 6133082 * 2
def baseEnd_6133082 : Nat := 3149218959438278522169475

theorem tailTrace_6133082 : CollatzResearch.WordTrace tailWord_6133082 prefixEnd_6133082 3149218959438278522169475 := by
  unfold tailWord_6133082
  simp only [CollatzResearch.WordTrace]
  refine ⟨55922969391724708964798375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149127918377932557239462333 55922969391724708964798375)
  ·
    refine ⟨83884454087587063447197563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55922969391724708964798375 83884454087587063447197563)
    ·
      refine ⟨125826681131380595170796345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83884454087587063447197563 125826681131380595170796345)
      ·
        refine ⟨94370010848535446378097259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125826681131380595170796345 94370010848535446378097259)
        ·
          refine ⟨141555016272803169567145889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94370010848535446378097259 141555016272803169567145889)
          ·
            refine ⟨106166262204602377175359417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141555016272803169567145889 106166262204602377175359417)
            ·
              refine ⟨79624696653451782881519563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106166262204602377175359417 79624696653451782881519563)
              ·
                refine ⟨119437044980177674322279345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79624696653451782881519563 119437044980177674322279345)
                ·
                  refine ⟨89577783735133255741709509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119437044980177674322279345 89577783735133255741709509)
                  ·
                    refine ⟨16795834450337485451570533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89577783735133255741709509 16795834450337485451570533)
                    ·
                      refine ⟨3149218959438278522169475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16795834450337485451570533 3149218959438278522169475)
                      ·
                        rfl

theorem cell23_6133082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_6133082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133082 prefixEnd_6133082 := by exact prefixLift 6133082
  have htrace : WordTrace (prefixWord ++ tailWord_6133082) baseStart_6133082 baseEnd_6133082 := by
    simpa [prefixWord, tailWord_6133082, baseEnd_6133082] using wordTrace_append hprefix tailTrace_6133082
  have hstable : (prefixWord ++ tailWord_6133082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133082).length < 2 ^ (prefixWord ++ tailWord_6133082).sum := by decide
  have hdescent : baseEnd_6133082 < baseStart_6133082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133113 : List Nat := [1, 2, 1, 3, 2, 1, 6, 2, 1, 4]
def baseStart_6133113 : Nat := 118140960795 + 6133113 * 2 ^ 59
def prefixEnd_6133113 : Nat := 4983230072969 + 3 ^ 40 * 6133113 * 2
def baseEnd_6133113 : Nat := 1049744959112855966960611

theorem tailTrace_6133113 : CollatzResearch.WordTrace tailWord_6133113 prefixEnd_6133113 1049744959112855966960611 := by
  unfold tailWord_6133113
  simp only [CollatzResearch.WordTrace]
  refine ⟨223693008229786528153571993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149128672153191018769047995 223693008229786528153571993)
  ·
    refine ⟨167769756172339896115178995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223693008229786528153571993 167769756172339896115178995)
    ·
      refine ⟨251654634258509844172768493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167769756172339896115178995 251654634258509844172768493)
      ·
        refine ⟨94370487846941191564788185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251654634258509844172768493 94370487846941191564788185)
        ·
          refine ⟨70777865885205893673591139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94370487846941191564788185 70777865885205893673591139)
          ·
            refine ⟨106166798827808840510386709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70777865885205893673591139 106166798827808840510386709)
            ·
              refine ⟨4976568695053539398924377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106166798827808840510386709 4976568695053539398924377)
              ·
                refine ⟨3732426521290154549193283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4976568695053539398924377 3732426521290154549193283)
                ·
                  refine ⟨5598639781935231823789925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3732426521290154549193283 5598639781935231823789925)
                  ·
                    refine ⟨1049744959112855966960611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5598639781935231823789925 1049744959112855966960611)
                    ·
                      rfl

theorem cell23_6133113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 1, 4].length) (baseStart_6133113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133113 prefixEnd_6133113 := by exact prefixLift 6133113
  have htrace : WordTrace (prefixWord ++ tailWord_6133113) baseStart_6133113 baseEnd_6133113 := by
    simpa [prefixWord, tailWord_6133113, baseEnd_6133113] using wordTrace_append hprefix tailTrace_6133113
  have hstable : (prefixWord ++ tailWord_6133113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133113).length < 2 ^ (prefixWord ++ tailWord_6133113).sum := by decide
  have hdescent : baseEnd_6133113 < baseStart_6133113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133132 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 2, 1, 7]
def baseStart_6133132 : Nat := 118140960795 + 6133132 * 2 ^ 59
def prefixEnd_6133132 : Nat := 4983230072969 + 3 ^ 40 * 6133132 * 2
def baseEnd_6133132 : Nat := 3149244633471003326544245

theorem tailTrace_6133132 : CollatzResearch.WordTrace tailWord_6133132 prefixEnd_6133132 3149244633471003326544245 := by
  unfold tailWord_6133132
  simp only [CollatzResearch.WordTrace]
  refine ⟨111846850608358847199256825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149129134144478462932342433 111846850608358847199256825)
  ·
    refine ⟨83885137956269135399442619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111846850608358847199256825 83885137956269135399442619)
    ·
      refine ⟨125827706934403703099163929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83885137956269135399442619 125827706934403703099163929)
      ·
        refine ⟨94370780200802777324372947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125827706934403703099163929 94370780200802777324372947)
        ·
          refine ⟨141556170301204165986559421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94370780200802777324372947 141556170301204165986559421)
          ·
            refine ⟨53083563862951562244959783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141556170301204165986559421 53083563862951562244959783)
            ·
              refine ⟨79625345794427343367439675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53083563862951562244959783 79625345794427343367439675)
              ·
                refine ⟨119438018691641015051159513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79625345794427343367439675 119438018691641015051159513)
                ·
                  refine ⟨89578514018730761288369635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119438018691641015051159513 89578514018730761288369635)
                  ·
                    refine ⟨134367771028096141932554453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89578514018730761288369635 134367771028096141932554453)
                    ·
                      refine ⟨3149244633471003326544245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134367771028096141932554453 3149244633471003326544245)
                      ·
                        rfl

theorem cell23_6133132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_6133132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133132 prefixEnd_6133132 := by exact prefixLift 6133132
  have htrace : WordTrace (prefixWord ++ tailWord_6133132) baseStart_6133132 baseEnd_6133132 := by
    simpa [prefixWord, tailWord_6133132, baseEnd_6133132] using wordTrace_append hprefix tailTrace_6133132
  have hstable : (prefixWord ++ tailWord_6133132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133132).length < 2 ^ (prefixWord ++ tailWord_6133132).sum := by decide
  have hdescent : baseEnd_6133132 < baseStart_6133132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133146 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2]
def baseStart_6133146 : Nat := 118140960795 + 6133146 * 2 ^ 59
def prefixEnd_6133146 : Nat := 4983230072969 + 3 ^ 40 * 6133146 * 2
def baseEnd_6133146 : Nat := 3149251822200166271769181

theorem tailTrace_6133146 : CollatzResearch.WordTrace tailWord_6133146 prefixEnd_6133146 3149251822200166271769181 := by
  unfold tailWord_6133146
  simp only [CollatzResearch.WordTrace]
  refine ⟨55923552959666743697380823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149129474559111316526348861 55923552959666743697380823)
  ·
    refine ⟨83885329439500115546071235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55923552959666743697380823 83885329439500115546071235)
    ·
      refine ⟨125827994159250173319106853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83885329439500115546071235 125827994159250173319106853)
      ·
        refine ⟨23592748904859407497332535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125827994159250173319106853 23592748904859407497332535)
        ·
          refine ⟨35389123357289111245998803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23592748904859407497332535 35389123357289111245998803)
          ·
            refine ⟨53083685035933666868998205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35389123357289111245998803 53083685035933666868998205)
            ·
              refine ⟨19906381888475125075874327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53083685035933666868998205 19906381888475125075874327)
              ·
                refine ⟨29859572832712687613811491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19906381888475125075874327 29859572832712687613811491)
                ·
                  refine ⟨44789359249069031420717237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29859572832712687613811491 44789359249069031420717237)
                  ·
                    refine ⟨4199002429600221695692241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44789359249069031420717237 4199002429600221695692241)
                    ·
                      refine ⟨3149251822200166271769181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4199002429600221695692241 3149251822200166271769181)
                      ·
                        rfl

theorem cell23_6133146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_6133146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133146 prefixEnd_6133146 := by exact prefixLift 6133146
  have htrace : WordTrace (prefixWord ++ tailWord_6133146) baseStart_6133146 baseEnd_6133146 := by
    simpa [prefixWord, tailWord_6133146, baseEnd_6133146] using wordTrace_append hprefix tailTrace_6133146
  have hstable : (prefixWord ++ tailWord_6133146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133146).length < 2 ^ (prefixWord ++ tailWord_6133146).sum := by decide
  have hdescent : baseEnd_6133146 < baseStart_6133146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133160 : List Nat := [2, 1, 6, 1, 3, 1, 1, 2, 6]
def baseStart_6133160 : Nat := 118140960795 + 6133160 * 2 ^ 59
def prefixEnd_6133160 : Nat := 4983230072969 + 3 ^ 40 * 6133160 * 2
def baseEnd_6133160 : Nat := 349917667881036579666013

theorem tailTrace_6133160 : CollatzResearch.WordTrace tailWord_6133160 prefixEnd_6133160 349917667881036579666013 := by
  unfold tailWord_6133160
  simp only [CollatzResearch.WordTrace]
  refine ⟨111847361230308127590266467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149129814973744170120355289 111847361230308127590266467)
  ·
    refine ⟨167771041845462191385399701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111847361230308127590266467 167771041845462191385399701)
    ·
      refine ⟨7864267586506040221190611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 167771041845462191385399701 7864267586506040221190611)
      ·
        refine ⟨11796401379759060331785917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7864267586506040221190611 11796401379759060331785917)
        ·
          refine ⟨4423650517409647624419719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11796401379759060331785917 4423650517409647624419719)
          ·
            refine ⟨6635475776114471436629579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423650517409647624419719 6635475776114471436629579)
            ·
              refine ⟨9953213664171707154944369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6635475776114471436629579 9953213664171707154944369)
              ·
                refine ⟨7464910248128780366208277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9953213664171707154944369 7464910248128780366208277)
                ·
                  refine ⟨349917667881036579666013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7464910248128780366208277 349917667881036579666013)
                  ·
                    rfl

theorem cell23_6133160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 6].length) (baseStart_6133160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133160 prefixEnd_6133160 := by exact prefixLift 6133160
  have htrace : WordTrace (prefixWord ++ tailWord_6133160) baseStart_6133160 baseEnd_6133160 := by
    simpa [prefixWord, tailWord_6133160, baseEnd_6133160] using wordTrace_append hprefix tailTrace_6133160
  have hstable : (prefixWord ++ tailWord_6133160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133160).length < 2 ^ (prefixWord ++ tailWord_6133160).sum := by decide
  have hdescent : baseEnd_6133160 < baseStart_6133160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133199 : List Nat := [1, 1, 2, 1, 1, 4, 6, 7]
def baseStart_6133199 : Nat := 118140960795 + 6133199 * 2 ^ 59
def prefixEnd_6133199 : Nat := 4983230072969 + 3 ^ 40 * 6133199 * 2
def baseEnd_6133199 : Nat := 116639964321290909792831

theorem tailTrace_6133199 : CollatzResearch.WordTrace tailWord_6133199 prefixEnd_6133199 116639964321290909792831 := by
  unfold tailWord_6133199
  simp only [CollatzResearch.WordTrace]
  refine ⟨223696144907474964841202651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149130763271649976560801767 223696144907474964841202651)
  ·
    refine ⟨335544217361212447261803977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223696144907474964841202651 335544217361212447261803977)
    ·
      refine ⟨251658163020909335446352983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335544217361212447261803977 251658163020909335446352983)
      ·
        refine ⟨377487244531364003169529475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251658163020909335446352983 377487244531364003169529475)
        ·
          refine ⟨566230866797046004754294213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377487244531364003169529475 566230866797046004754294213)
          ·
            refine ⟨106168287524446125891430165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 566230866797046004754294213 106168287524446125891430165)
            ·
              refine ⟨4976638477708412151160789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106168287524446125891430165 4976638477708412151160789)
              ·
                refine ⟨116639964321290909792831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4976638477708412151160789 116639964321290909792831)
                ·
                  rfl

theorem cell23_6133199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 7].length) (baseStart_6133199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133199 prefixEnd_6133199 := by exact prefixLift 6133199
  have htrace : WordTrace (prefixWord ++ tailWord_6133199) baseStart_6133199 baseEnd_6133199 := by
    simpa [prefixWord, tailWord_6133199, baseEnd_6133199] using wordTrace_append hprefix tailTrace_6133199
  have hstable : (prefixWord ++ tailWord_6133199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133199).length < 2 ^ (prefixWord ++ tailWord_6133199).sum := by decide
  have hdescent : baseEnd_6133199 < baseStart_6133199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133204 : List Nat := [2, 4, 1, 2, 4, 1, 1, 3, 1, 1, 3]
def baseStart_6133204 : Nat := 118140960795 + 6133204 * 2 ^ 59
def prefixEnd_6133204 : Nat := 4983230072969 + 3 ^ 40 * 6133204 * 2
def baseEnd_6133204 : Nat := 3149281604078127044843915

theorem tailTrace_6133204 : CollatzResearch.WordTrace tailWord_6133204 prefixEnd_6133204 3149281604078127044843915 := by
  unfold tailWord_6133204
  simp only [CollatzResearch.WordTrace]
  refine ⟨111848163636228425347567333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149130884848304567130089777 111848163636228425347567333)
  ·
    refine ⟨20971530681792829752668875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111848163636228425347567333 20971530681792829752668875)
    ·
      refine ⟨31457296022689244629003313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20971530681792829752668875 31457296022689244629003313)
      ·
        refine ⟨23592972017016933471752485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31457296022689244629003313 23592972017016933471752485)
        ·
          refine ⟨4423682253190675025953591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23592972017016933471752485 4423682253190675025953591)
          ·
            refine ⟨6635523379786012538930387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423682253190675025953591 6635523379786012538930387)
            ·
              refine ⟨9953285069679018808395581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6635523379786012538930387 9953285069679018808395581)
              ·
                refine ⟨3732481901129632053148343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9953285069679018808395581 3732481901129632053148343)
                ·
                  refine ⟨5598722851694448079722515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3732481901129632053148343 5598722851694448079722515)
                  ·
                    refine ⟨8398084277541672119583773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5598722851694448079722515 8398084277541672119583773)
                    ·
                      refine ⟨3149281604078127044843915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8398084277541672119583773 3149281604078127044843915)
                      ·
                        rfl

theorem cell23_6133204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_6133204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133204 prefixEnd_6133204 := by exact prefixLift 6133204
  have htrace : WordTrace (prefixWord ++ tailWord_6133204) baseStart_6133204 baseEnd_6133204 := by
    simpa [prefixWord, tailWord_6133204, baseEnd_6133204] using wordTrace_append hprefix tailTrace_6133204
  have hstable : (prefixWord ++ tailWord_6133204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133204).length < 2 ^ (prefixWord ++ tailWord_6133204).sum := by decide
  have hdescent : baseEnd_6133204 < baseStart_6133204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133213 : List Nat := [1, 4, 3, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_6133213 : Nat := 118140960795 + 6133213 * 2 ^ 59
def prefixEnd_6133213 : Nat := 4983230072969 + 3 ^ 40 * 6133213 * 2
def baseEnd_6133213 : Nat := 3149286225404017509631373

theorem tailTrace_6133213 : CollatzResearch.WordTrace tailWord_6133213 prefixEnd_6133213 3149286225404017509631373 := by
  unfold tailWord_6133213
  simp only [CollatzResearch.WordTrace]
  refine ⟨223696655529424245232212293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149131103686282830154808195 223696655529424245232212293)
  ·
    refine ⟨41943122911767045981039805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223696655529424245232212293 41943122911767045981039805)
    ·
      refine ⟨15728671091912642242889927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41943122911767045981039805 15728671091912642242889927)
      ·
        refine ⟨23593006637868963364334891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15728671091912642242889927 23593006637868963364334891)
        ·
          refine ⟨35389509956803445046502337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23593006637868963364334891 35389509956803445046502337)
          ·
            refine ⟨26542132467602583784876753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35389509956803445046502337 26542132467602583784876753)
            ·
              refine ⟨19906599350701937838657565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26542132467602583784876753 19906599350701937838657565)
              ·
                refine ⟨7464974756513226689496587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19906599350701937838657565 7464974756513226689496587)
                ·
                  refine ⟨11197462134769840034244881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7464974756513226689496587 11197462134769840034244881)
                  ·
                    refine ⟨8398096601077380025683661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11197462134769840034244881 8398096601077380025683661)
                    ·
                      refine ⟨3149286225404017509631373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8398096601077380025683661 3149286225404017509631373)
                      ·
                        rfl

theorem cell23_6133213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_6133213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133213 prefixEnd_6133213 := by exact prefixLift 6133213
  have htrace : WordTrace (prefixWord ++ tailWord_6133213) baseStart_6133213 baseEnd_6133213 := by
    simpa [prefixWord, tailWord_6133213, baseEnd_6133213] using wordTrace_append hprefix tailTrace_6133213
  have hstable : (prefixWord ++ tailWord_6133213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133213).length < 2 ^ (prefixWord ++ tailWord_6133213).sum := by decide
  have hdescent : baseEnd_6133213 < baseStart_6133213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133237 : List Nat := [1, 3, 5, 1, 1, 3, 2, 1, 2, 4]
def baseStart_6133237 : Nat := 118140960795 + 6133237 * 2 ^ 59
def prefixEnd_6133237 : Nat := 4983230072969 + 3 ^ 40 * 6133237 * 2
def baseEnd_6133237 : Nat := 1049766182979908471910421

theorem tailTrace_6133237 : CollatzResearch.WordTrace tailWord_6133237 prefixEnd_6133237 1049766182979908471910421 := by
  unfold tailWord_6133237
  simp only [CollatzResearch.WordTrace]
  refine ⟨223697530881337297331085965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149131687254224864887390643 223697530881337297331085965)
  ·
    refine ⟨83886574080501486499157237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223697530881337297331085965 83886574080501486499157237)
    ·
      refine ⟨7864366320047014359295991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83886574080501486499157237 7864366320047014359295991)
      ·
        refine ⟨11796549480070521538943987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7864366320047014359295991 11796549480070521538943987)
        ·
          refine ⟨17694824220105782308415981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11796549480070521538943987 17694824220105782308415981)
          ·
            refine ⟨6635559082539668365655993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17694824220105782308415981 6635559082539668365655993)
            ·
              refine ⟨4976669311904751274241995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6635559082539668365655993 4976669311904751274241995)
              ·
                refine ⟨7465003967857126911362993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4976669311904751274241995 7465003967857126911362993)
                ·
                  refine ⟨5598752975892845183522245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7465003967857126911362993 5598752975892845183522245)
                  ·
                    refine ⟨1049766182979908471910421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5598752975892845183522245 1049766182979908471910421)
                    ·
                      rfl

theorem cell23_6133237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_6133237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133237 prefixEnd_6133237 := by exact prefixLift 6133237
  have htrace : WordTrace (prefixWord ++ tailWord_6133237) baseStart_6133237 baseEnd_6133237 := by
    simpa [prefixWord, tailWord_6133237, baseEnd_6133237] using wordTrace_append hprefix tailTrace_6133237
  have hstable : (prefixWord ++ tailWord_6133237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133237).length < 2 ^ (prefixWord ++ tailWord_6133237).sum := by decide
  have hdescent : baseEnd_6133237 < baseStart_6133237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133278 : List Nat := [4, 3, 3, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_6133278 : Nat := 118140960795 + 6133278 * 2 ^ 59
def prefixEnd_6133278 : Nat := 4983230072969 + 3 ^ 40 * 6133278 * 2
def baseEnd_6133278 : Nat := 3149319601646559755318575

theorem tailTrace_6133278 : CollatzResearch.WordTrace tailWord_6133278 prefixEnd_6133278 3149319601646559755318575 := by
  unfold tailWord_6133278
  simp only [CollatzResearch.WordTrace]
  refine ⟨27962378284273595166666061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149132684182792507555552325 27962378284273595166666061)
  ·
    refine ⟨10485891856602598187499773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27962378284273595166666061 10485891856602598187499773)
    ·
      refine ⟨3932209446225974320312415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10485891856602598187499773 3932209446225974320312415)
      ·
        refine ⟨5898314169338961480468623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3932209446225974320312415 5898314169338961480468623)
        ·
          refine ⟨8847471254008442220702935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5898314169338961480468623 8847471254008442220702935)
          ·
            refine ⟨13271206881012663331054403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8847471254008442220702935 13271206881012663331054403)
            ·
              refine ⟨19906810321518994996581605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13271206881012663331054403 19906810321518994996581605)
              ·
                refine ⟨3732526935284811561859051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19906810321518994996581605 3732526935284811561859051)
                ·
                  refine ⟨5598790402927217342788577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3732526935284811561859051 5598790402927217342788577)
                  ·
                    refine ⟨4199092802195413007091433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5598790402927217342788577 4199092802195413007091433)
                    ·
                      refine ⟨3149319601646559755318575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4199092802195413007091433 3149319601646559755318575)
                      ·
                        rfl

theorem cell23_6133278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_6133278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133278 prefixEnd_6133278 := by exact prefixLift 6133278
  have htrace : WordTrace (prefixWord ++ tailWord_6133278) baseStart_6133278 baseEnd_6133278 := by
    simpa [prefixWord, tailWord_6133278, baseEnd_6133278] using wordTrace_append hprefix tailTrace_6133278
  have hstable : (prefixWord ++ tailWord_6133278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133278).length < 2 ^ (prefixWord ++ tailWord_6133278).sum := by decide
  have hdescent : baseEnd_6133278 < baseStart_6133278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133376 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 3]
def baseStart_6133376 : Nat := 118140960795 + 6133376 * 2 ^ 59
def prefixEnd_6133376 : Nat := 4983230072969 + 3 ^ 40 * 6133376 * 2
def baseEnd_6133376 : Nat := 3149369922750700371893123

theorem tailTrace_6133376 : CollatzResearch.WordTrace tailWord_6133376 prefixEnd_6133376 3149369922750700371893123 := by
  unfold tailWord_6133376
  simp only [CollatzResearch.WordTrace]
  refine ⟨111851300313916862035197991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149135067085222482713597321 111851300313916862035197991)
  ·
    refine ⟨167776950470875293052796987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111851300313916862035197991 167776950470875293052796987)
    ·
      refine ⟨251665425706312939579195481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167776950470875293052796987 251665425706312939579195481)
      ·
        refine ⟨188749069279734704684396611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251665425706312939579195481 188749069279734704684396611)
        ·
          refine ⟨283123603919602057026594917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188749069279734704684396611 283123603919602057026594917)
          ·
            refine ⟨53085675734925385692486547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 283123603919602057026594917 53085675734925385692486547)
            ·
              refine ⟨79628513602388078538729821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53085675734925385692486547 79628513602388078538729821)
              ·
                refine ⟨29860692600895529452023683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79628513602388078538729821 29860692600895529452023683)
                ·
                  refine ⟨44791038901343294178035525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29860692600895529452023683 44791038901343294178035525)
                  ·
                    refine ⟨8398319794001867658381661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44791038901343294178035525 8398319794001867658381661)
                    ·
                      refine ⟨3149369922750700371893123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8398319794001867658381661 3149369922750700371893123)
                      ·
                        rfl

theorem cell23_6133376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_6133376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133376 prefixEnd_6133376 := by exact prefixLift 6133376
  have htrace : WordTrace (prefixWord ++ tailWord_6133376) baseStart_6133376 baseEnd_6133376 := by
    simpa [prefixWord, tailWord_6133376, baseEnd_6133376] using wordTrace_append hprefix tailTrace_6133376
  have hstable : (prefixWord ++ tailWord_6133376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133376).length < 2 ^ (prefixWord ++ tailWord_6133376).sum := by decide
  have hdescent : baseEnd_6133376 < baseStart_6133376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133400 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 3, 4]
def baseStart_6133400 : Nat := 118140960795 + 6133400 * 2 ^ 59
def prefixEnd_6133400 : Nat := 4983230072969 + 3 ^ 40 * 6133400 * 2
def baseEnd_6133400 : Nat := 1049794082095469425997671

theorem tailTrace_6133400 : CollatzResearch.WordTrace tailWord_6133400 prefixEnd_6133400 1049794082095469425997671 := by
  unfold tailWord_6133400
  simp only [CollatzResearch.WordTrace]
  refine ⟨111851737989873388084634827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149135650653164517446179769 111851737989873388084634827)
  ·
    refine ⟨167777606984810082126952241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111851737989873388084634827 167777606984810082126952241)
    ·
      refine ⟨125833205238607561595214181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167777606984810082126952241 125833205238607561595214181)
      ·
        refine ⟨23593725982238917799102659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125833205238607561595214181 23593725982238917799102659)
        ·
          refine ⟨35390588973358376698653989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23593725982238917799102659 35390588973358376698653989)
          ·
            refine ⟨6635735432504695630997623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35390588973358376698653989 6635735432504695630997623)
            ·
              refine ⟨9953603148757043446496435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6635735432504695630997623 9953603148757043446496435)
              ·
                refine ⟨14930404723135565169744653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9953603148757043446496435 14930404723135565169744653)
                ·
                  refine ⟨5598901771175836938654245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14930404723135565169744653 5598901771175836938654245)
                  ·
                    refine ⟨1049794082095469425997671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5598901771175836938654245 1049794082095469425997671)
                    ·
                      rfl

theorem cell23_6133400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_6133400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133400 prefixEnd_6133400 := by exact prefixLift 6133400
  have htrace : WordTrace (prefixWord ++ tailWord_6133400) baseStart_6133400 baseEnd_6133400 := by
    simpa [prefixWord, tailWord_6133400, baseEnd_6133400] using wordTrace_append hprefix tailTrace_6133400
  have hstable : (prefixWord ++ tailWord_6133400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133400).length < 2 ^ (prefixWord ++ tailWord_6133400).sum := by decide
  have hdescent : baseEnd_6133400 < baseStart_6133400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133413 : List Nat := [1, 3, 1, 2, 1, 2, 6, 1, 6]
def baseStart_6133413 : Nat := 118140960795 + 6133413 * 2 ^ 59
def prefixEnd_6133413 : Nat := 4983230072969 + 3 ^ 40 * 6133413 * 2
def baseEnd_6133413 : Nat := 349932102392768525236717

theorem tailTrace_6133413 : CollatzResearch.WordTrace tailWord_6133413 prefixEnd_6133413 349932102392768525236717 := by
  unfold tailWord_6133413
  simp only [CollatzResearch.WordTrace]
  refine ⟨223703950128699679389492893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149135966752466452926328595 223703950128699679389492893)
  ·
    refine ⟨83888981298262379771059835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223703950128699679389492893 83888981298262379771059835)
    ·
      refine ⟨125833471947393569656589753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83888981298262379771059835 125833471947393569656589753)
      ·
        refine ⟨94375103960545177242442315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125833471947393569656589753 94375103960545177242442315)
        ·
          refine ⟨141562655940817765863663473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94375103960545177242442315 141562655940817765863663473)
          ·
            refine ⟨106171991955613324397747605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141562655940817765863663473 106171991955613324397747605)
            ·
              refine ⟨4976812122919374581144419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106171991955613324397747605 4976812122919374581144419)
              ·
                refine ⟨7465218184379061871716629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4976812122919374581144419 7465218184379061871716629)
                ·
                  refine ⟨349932102392768525236717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7465218184379061871716629 349932102392768525236717)
                  ·
                    rfl

theorem cell23_6133413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 6].length) (baseStart_6133413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133413 prefixEnd_6133413 := by exact prefixLift 6133413
  have htrace : WordTrace (prefixWord ++ tailWord_6133413) baseStart_6133413 baseEnd_6133413 := by
    simpa [prefixWord, tailWord_6133413, baseEnd_6133413] using wordTrace_append hprefix tailTrace_6133413
  have hstable : (prefixWord ++ tailWord_6133413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133413).length < 2 ^ (prefixWord ++ tailWord_6133413).sum := by decide
  have hdescent : baseEnd_6133413 < baseStart_6133413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133423 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 5, 1, 3]
def baseStart_6133423 : Nat := 118140960795 + 6133423 * 2 ^ 59
def prefixEnd_6133423 : Nat := 4983230072969 + 3 ^ 40 * 6133423 * 2
def baseEnd_6133423 : Nat := 3149394056341461688005407

theorem tailTrace_6133423 : CollatzResearch.WordTrace tailWord_6133423 prefixEnd_6133423 3149394056341461688005407 := by
  unfold tailWord_6133423
  simp only [CollatzResearch.WordTrace]
  refine ⟨223704314858663451097356923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149136209905775634064904615 223704314858663451097356923)
  ·
    refine ⟨335556472287995176646035385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223704314858663451097356923 335556472287995176646035385)
    ·
      refine ⟨251667354215996382484526539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335556472287995176646035385 251667354215996382484526539)
      ·
        refine ⟨377501031323994573726789809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251667354215996382484526539 377501031323994573726789809)
        ·
          refine ⟨283125773492995930295092357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377501031323994573726789809 283125773492995930295092357)
          ·
            refine ⟨53086082529936736930329817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 283125773492995930295092357 53086082529936736930329817)
            ·
              refine ⟨39814561897452552697747363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53086082529936736930329817 39814561897452552697747363)
              ·
                refine ⟨59721842846178829046621045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39814561897452552697747363 59721842846178829046621045)
                ·
                  refine ⟨5598922766829265223120723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59721842846178829046621045 5598922766829265223120723)
                  ·
                    refine ⟨8398384150243897834681085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5598922766829265223120723 8398384150243897834681085)
                    ·
                      refine ⟨3149394056341461688005407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8398384150243897834681085 3149394056341461688005407)
                      ·
                        rfl

theorem cell23_6133423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 1, 3].length) (baseStart_6133423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133423 prefixEnd_6133423 := by exact prefixLift 6133423
  have htrace : WordTrace (prefixWord ++ tailWord_6133423) baseStart_6133423 baseEnd_6133423 := by
    simpa [prefixWord, tailWord_6133423, baseEnd_6133423] using wordTrace_append hprefix tailTrace_6133423
  have hstable : (prefixWord ++ tailWord_6133423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133423).length < 2 ^ (prefixWord ++ tailWord_6133423).sum := by decide
  have hdescent : baseEnd_6133423 < baseStart_6133423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133433 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 1, 5, 2]
def baseStart_6133433 : Nat := 118140960795 + 6133433 * 2 ^ 59
def prefixEnd_6133433 : Nat := 4983230072969 + 3 ^ 40 * 6133433 * 2
def baseEnd_6133433 : Nat := 3149399191148006648880361

theorem tailTrace_6133433 : CollatzResearch.WordTrace tailWord_6133433 prefixEnd_6133433 3149399191148006648880361 := by
  unfold tailWord_6133433
  simp only [CollatzResearch.WordTrace]
  refine ⟨223704679588627222805220953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149136453059084815203480635 223704679588627222805220953)
  ·
    refine ⟨167778509691470417103915715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223704679588627222805220953 167778509691470417103915715)
    ·
      refine ⟨251667764537205625655873573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167778509691470417103915715 251667764537205625655873573)
      ·
        refine ⟨47187705850726054810476295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251667764537205625655873573 47187705850726054810476295)
        ·
          refine ⟨70781558776089082215714443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47187705850726054810476295 70781558776089082215714443)
          ·
            refine ⟨106172338164133623323571665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70781558776089082215714443 106172338164133623323571665)
            ·
              refine ⟨79629253623100217492678749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106172338164133623323571665 79629253623100217492678749)
              ·
                refine ⟨29860970108662581559754531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79629253623100217492678749 29860970108662581559754531)
                ·
                  refine ⟨44791455162993872339631797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29860970108662581559754531 44791455162993872339631797)
                  ·
                    refine ⟨4199198921530675531840481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44791455162993872339631797 4199198921530675531840481)
                    ·
                      refine ⟨3149399191148006648880361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4199198921530675531840481 3149399191148006648880361)
                      ·
                        rfl

theorem cell23_6133433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_6133433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133433 prefixEnd_6133433 := by exact prefixLift 6133433
  have htrace : WordTrace (prefixWord ++ tailWord_6133433) baseStart_6133433 baseEnd_6133433 := by
    simpa [prefixWord, tailWord_6133433, baseEnd_6133433] using wordTrace_append hprefix tailTrace_6133433
  have hstable : (prefixWord ++ tailWord_6133433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133433).length < 2 ^ (prefixWord ++ tailWord_6133433).sum := by decide
  have hdescent : baseEnd_6133433 < baseStart_6133433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133457 : List Nat := [1, 2, 2, 1, 2, 5, 1, 4, 1, 1, 3]
def baseStart_6133457 : Nat := 118140960795 + 6133457 * 2 ^ 59
def prefixEnd_6133457 : Nat := 4983230072969 + 3 ^ 40 * 6133457 * 2
def baseEnd_6133457 : Nat := 3149411514683714554980251

theorem tailTrace_6133457 : CollatzResearch.WordTrace tailWord_6133457 prefixEnd_6133457 3149411514683714554980251 := by
  unfold tailWord_6133457
  simp only [CollatzResearch.WordTrace]
  refine ⟨223705554940540274904094625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149137036627026849936063083 223705554940540274904094625)
  ·
    refine ⟨167779166205405206178070969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223705554940540274904094625 167779166205405206178070969)
    ·
      refine ⟨125834374654053904633553227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167779166205405206178070969 125834374654053904633553227)
      ·
        refine ⟨188751561981080856950329841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125834374654053904633553227 188751561981080856950329841)
        ·
          refine ⟨141563671485810642712747381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188751561981080856950329841 141563671485810642712747381)
          ·
            refine ⟨13271594201794747754320067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141563671485810642712747381 13271594201794747754320067)
            ·
              refine ⟨19907391302692121631480101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13271594201794747754320067 19907391302692121631480101)
              ·
                refine ⟨3732635869254772805902519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19907391302692121631480101 3732635869254772805902519)
                ·
                  refine ⟨5598953803882159208853779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3732635869254772805902519 5598953803882159208853779)
                  ·
                    refine ⟨8398430705823238813280669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5598953803882159208853779 8398430705823238813280669)
                    ·
                      refine ⟨3149411514683714554980251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8398430705823238813280669 3149411514683714554980251)
                      ·
                        rfl

theorem cell23_6133457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 1, 1, 3].length) (baseStart_6133457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133457 prefixEnd_6133457 := by exact prefixLift 6133457
  have htrace : WordTrace (prefixWord ++ tailWord_6133457) baseStart_6133457 baseEnd_6133457 := by
    simpa [prefixWord, tailWord_6133457, baseEnd_6133457] using wordTrace_append hprefix tailTrace_6133457
  have hstable : (prefixWord ++ tailWord_6133457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133457).length < 2 ^ (prefixWord ++ tailWord_6133457).sum := by decide
  have hdescent : baseEnd_6133457 < baseStart_6133457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133483 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 3]
def baseStart_6133483 : Nat := 118140960795 + 6133483 * 2 ^ 59
def prefixEnd_6133483 : Nat := 4983230072969 + 3 ^ 40 * 6133483 * 2
def baseEnd_6133483 : Nat := 3149424865180731453255131

theorem tailTrace_6133483 : CollatzResearch.WordTrace tailWord_6133483 prefixEnd_6133483 3149424865180731453255131 := by
  unfold tailWord_6133483
  simp only [CollatzResearch.WordTrace]
  refine ⟨223706503238446081344541103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149137668825630720896360735 223706503238446081344541103)
  ·
    refine ⟨335559754857669122016811655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223706503238446081344541103 335559754857669122016811655)
    ·
      refine ⟨503339632286503683025217483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335559754857669122016811655 503339632286503683025217483)
      ·
        refine ⟨755009448429755524537826225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503339632286503683025217483 755009448429755524537826225)
        ·
          refine ⟨566257086322316643403369669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755009448429755524537826225 566257086322316643403369669)
          ·
            refine ⟨106173203685434370638131813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 566257086322316643403369669 106173203685434370638131813)
            ·
              refine ⟨19907475691018944494649715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106173203685434370638131813 19907475691018944494649715)
              ·
                refine ⟨29861213536528416741974573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19907475691018944494649715 29861213536528416741974573)
                ·
                  refine ⟨11197955076198156278240465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29861213536528416741974573 11197955076198156278240465)
                  ·
                    refine ⟨8398466307148617208680349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11197955076198156278240465 8398466307148617208680349)
                    ·
                      refine ⟨3149424865180731453255131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8398466307148617208680349 3149424865180731453255131)
                      ·
                        rfl

theorem cell23_6133483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 3].length) (baseStart_6133483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133483 prefixEnd_6133483 := by exact prefixLift 6133483
  have htrace : WordTrace (prefixWord ++ tailWord_6133483) baseStart_6133483 baseEnd_6133483 := by
    simpa [prefixWord, tailWord_6133483, baseEnd_6133483] using wordTrace_append hprefix tailTrace_6133483
  have hstable : (prefixWord ++ tailWord_6133483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133483).length < 2 ^ (prefixWord ++ tailWord_6133483).sum := by decide
  have hdescent : baseEnd_6133483 < baseStart_6133483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133500 : List Nat := [2, 2, 2, 1, 3, 1, 3, 3, 1, 2, 3]
def baseStart_6133500 : Nat := 118140960795 + 6133500 * 2 ^ 59
def prefixEnd_6133500 : Nat := 4983230072969 + 3 ^ 40 * 6133500 * 2
def baseEnd_6133500 : Nat := 3149433594351857886742553

theorem tailTrace_6133500 : CollatzResearch.WordTrace tailWord_6133500 prefixEnd_6133500 3149433594351857886742553 := by
  unfold tailWord_6133500
  simp only [CollatzResearch.WordTrace]
  refine ⟨111853561639692246623954977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149138082186256328831939969 111853561639692246623954977)
  ·
    refine ⟨83890171229769184967966233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111853561639692246623954977 83890171229769184967966233)
    ·
      refine ⟨62917628422326888725974675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83890171229769184967966233 62917628422326888725974675)
      ·
        refine ⟨94376442633490333088962013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62917628422326888725974675 94376442633490333088962013)
        ·
          refine ⟨35391165987558874908360755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94376442633490333088962013 35391165987558874908360755)
          ·
            refine ⟨53086748981338312362541133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35391165987558874908360755 53086748981338312362541133)
            ·
              refine ⟨19907530868001867135952925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53086748981338312362541133 19907530868001867135952925)
              ·
                refine ⟨7465324075500700175982347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19907530868001867135952925 7465324075500700175982347)
                ·
                  refine ⟨11197986113251050263973521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7465324075500700175982347 11197986113251050263973521)
                  ·
                    refine ⟨8398489584938287697980141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11197986113251050263973521 8398489584938287697980141)
                    ·
                      refine ⟨3149433594351857886742553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8398489584938287697980141 3149433594351857886742553)
                      ·
                        rfl

theorem cell23_6133500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_6133500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133500 prefixEnd_6133500 := by exact prefixLift 6133500
  have htrace : WordTrace (prefixWord ++ tailWord_6133500) baseStart_6133500 baseEnd_6133500 := by
    simpa [prefixWord, tailWord_6133500, baseEnd_6133500] using wordTrace_append hprefix tailTrace_6133500
  have hstable : (prefixWord ++ tailWord_6133500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133500).length < 2 ^ (prefixWord ++ tailWord_6133500).sum := by decide
  have hdescent : baseEnd_6133500 < baseStart_6133500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133514 : List Nat := [3, 1, 2, 2, 1, 3, 2, 4, 1, 2, 2]
def baseStart_6133514 : Nat := 118140960795 + 6133514 * 2 ^ 59
def prefixEnd_6133514 : Nat := 4983230072969 + 3 ^ 40 * 6133514 * 2
def baseEnd_6133514 : Nat := 3149440783081020831967489

theorem tailTrace_6133514 : CollatzResearch.WordTrace tailWord_6133514 prefixEnd_6133514 3149440783081020831967489 := by
  unfold tailWord_6133514
  simp only [CollatzResearch.WordTrace]
  refine ⟨55926908475333443409729899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149138422600889182425946397 55926908475333443409729899)
  ·
    refine ⟨83890362713000165114594849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55926908475333443409729899 83890362713000165114594849)
    ·
      refine ⟨62917772034750123835946137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83890362713000165114594849 62917772034750123835946137)
      ·
        refine ⟨47188329026062592876959603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62917772034750123835946137 47188329026062592876959603)
        ·
          refine ⟨70782493539093889315439405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47188329026062592876959603 70782493539093889315439405)
          ·
            refine ⟨26543435077160208493289777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70782493539093889315439405 26543435077160208493289777)
            ·
              refine ⟨19907576307870156369967333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26543435077160208493289777 19907576307870156369967333)
              ·
                refine ⟨3732670557725654319368875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19907576307870156369967333 3732670557725654319368875)
                ·
                  refine ⟨5599005836588481479053313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3732670557725654319368875 5599005836588481479053313)
                  ·
                    refine ⟨4199254377441361109289985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5599005836588481479053313 4199254377441361109289985)
                    ·
                      refine ⟨3149440783081020831967489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4199254377441361109289985 3149440783081020831967489)
                      ·
                        rfl

theorem cell23_6133514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_6133514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133514 prefixEnd_6133514 := by exact prefixLift 6133514
  have htrace : WordTrace (prefixWord ++ tailWord_6133514) baseStart_6133514 baseEnd_6133514 := by
    simpa [prefixWord, tailWord_6133514, baseEnd_6133514] using wordTrace_append hprefix tailTrace_6133514
  have hstable : (prefixWord ++ tailWord_6133514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133514).length < 2 ^ (prefixWord ++ tailWord_6133514).sum := by decide
  have hdescent : baseEnd_6133514 < baseStart_6133514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133516 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 1, 9]
def baseStart_6133516 : Nat := 118140960795 + 6133516 * 2 ^ 59
def prefixEnd_6133516 : Nat := 4983230072969 + 3 ^ 40 * 6133516 * 2
def baseEnd_6133516 : Nat := 1049813936680776608047493

theorem tailTrace_6133516 : CollatzResearch.WordTrace tailWord_6133516 prefixEnd_6133516 1049813936680776608047493 := by
  unfold tailWord_6133516
  simp only [CollatzResearch.WordTrace]
  refine ⟨111853853423663263990246201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149138471231551018653661601 111853853423663263990246201)
  ·
    refine ⟨83890390067747447992684651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111853853423663263990246201 83890390067747447992684651)
    ·
      refine ⟨125835585101621171989026977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83890390067747447992684651 125835585101621171989026977)
      ·
        refine ⟨94376688826215878991770233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125835585101621171989026977 94376688826215878991770233)
        ·
          refine ⟨70782516619661909243827675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94376688826215878991770233 70782516619661909243827675)
          ·
            refine ⟨106173774929492863865741513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70782516619661909243827675 106173774929492863865741513)
            ·
              refine ⟨79630331197119647899306135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106173774929492863865741513 79630331197119647899306135)
              ·
                refine ⟨119445496795679471848959203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79630331197119647899306135 119445496795679471848959203)
                ·
                  refine ⟨179168245193519207773438805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119445496795679471848959203 179168245193519207773438805)
                  ·
                    refine ⟨1049813936680776608047493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 179168245193519207773438805 1049813936680776608047493)
                    ·
                      rfl

theorem cell23_6133516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_6133516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133516 prefixEnd_6133516 := by exact prefixLift 6133516
  have htrace : WordTrace (prefixWord ++ tailWord_6133516) baseStart_6133516 baseEnd_6133516 := by
    simpa [prefixWord, tailWord_6133516, baseEnd_6133516] using wordTrace_append hprefix tailTrace_6133516
  have hstable : (prefixWord ++ tailWord_6133516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133516).length < 2 ^ (prefixWord ++ tailWord_6133516).sum := by decide
  have hdescent : baseEnd_6133516 < baseStart_6133516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
