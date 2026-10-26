import V185TrunkScan23Chunk0101

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_603752 : List Nat := [2, 1, 4, 3, 1, 1, 3, 8]
def baseStart_603752 : Nat := 118140960795 + 603752 * 2 ^ 59
def prefixEnd_603752 : Nat := 4983230072969 + 3 ^ 40 * 603752 * 2
def baseEnd_603752 : Nat := 11482036004201001897163

theorem tailTrace_603752 : CollatzResearch.WordTrace tailWord_603752 prefixEnd_603752 11482036004201001897163 := by
  unfold tailWord_603752
  simp only [CollatzResearch.WordTrace]
  refine ⟨11010322254358545738746755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14680429672478060984995673 11010322254358545738746755)
  ·
    refine ⟨16515483381537818608120133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11010322254358545738746755 16515483381537818608120133)
    ·
      refine ⟨3096653134038340989022525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16515483381537818608120133 3096653134038340989022525)
      ·
        refine ⟨1161244925264377870883447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3096653134038340989022525 1161244925264377870883447)
        ·
          refine ⟨1741867387896566806325171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1161244925264377870883447 1741867387896566806325171)
          ·
            refine ⟨2612801081844850209487757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1741867387896566806325171 2612801081844850209487757)
            ·
              refine ⟨979800405691818828557909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2612801081844850209487757 979800405691818828557909)
              ·
                refine ⟨11482036004201001897163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 979800405691818828557909 11482036004201001897163)
                ·
                  rfl

theorem cell23_603752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 8].length) (baseStart_603752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603752 prefixEnd_603752 := by exact prefixLift 603752
  have htrace : WordTrace (prefixWord ++ tailWord_603752) baseStart_603752 baseEnd_603752 := by
    simpa [prefixWord, tailWord_603752, baseEnd_603752] using wordTrace_append hprefix tailTrace_603752
  have hstable : (prefixWord ++ tailWord_603752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603752).length < 2 ^ (prefixWord ++ tailWord_603752).sum := by decide
  have hdescent : baseEnd_603752 < baseStart_603752 := by decide
  rcases family_descends (prefixWord ++ tailWord_603752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603780 : List Nat := [2, 3, 2, 1, 4, 1, 2, 3, 1, 2, 2]
def baseStart_603780 : Nat := 118140960795 + 603780 * 2 ^ 59
def prefixEnd_603780 : Nat := 4983230072969 + 3 ^ 40 * 603780 * 2
def baseEnd_603780 : Nat := 310029349571752941673273

theorem tailTrace_603780 : CollatzResearch.WordTrace tailWord_603780 prefixEnd_603780 310029349571752941673273 := by
  unfold tailWord_603780
  simp only [CollatzResearch.WordTrace]
  refine ⟨11010832876307826129756397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14681110501743768173008529 11010832876307826129756397)
  ·
    refine ⟨4129062328615434798658649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11010832876307826129756397 4129062328615434798658649)
    ·
      refine ⟨3096796746461576098993987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4129062328615434798658649 3096796746461576098993987)
      ·
        refine ⟨4645195119692364148490981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3096796746461576098993987 4645195119692364148490981)
        ·
          refine ⟨870974084942318277842059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4645195119692364148490981 870974084942318277842059)
          ·
            refine ⟨1306461127413477416763089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870974084942318277842059 1306461127413477416763089)
            ·
              refine ⟨979845845560108062572317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1306461127413477416763089 979845845560108062572317)
              ·
                refine ⟨367442192085040523464619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 979845845560108062572317 367442192085040523464619)
                ·
                  refine ⟨551163288127560785196929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367442192085040523464619 551163288127560785196929)
                  ·
                    refine ⟨413372466095670588897697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 551163288127560785196929 413372466095670588897697)
                    ·
                      refine ⟨310029349571752941673273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 413372466095670588897697 310029349571752941673273)
                      ·
                        rfl

theorem cell23_603780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_603780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603780 prefixEnd_603780 := by exact prefixLift 603780
  have htrace : WordTrace (prefixWord ++ tailWord_603780) baseStart_603780 baseEnd_603780 := by
    simpa [prefixWord, tailWord_603780, baseEnd_603780] using wordTrace_append hprefix tailTrace_603780
  have hstable : (prefixWord ++ tailWord_603780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603780).length < 2 ^ (prefixWord ++ tailWord_603780).sum := by decide
  have hdescent : baseEnd_603780 < baseStart_603780 := by decide
  rcases family_descends (prefixWord ++ tailWord_603780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603812 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 2, 6]
def baseStart_603812 : Nat := 118140960795 + 603812 * 2 ^ 59
def prefixEnd_603812 : Nat := 4983230072969 + 3 ^ 40 * 603812 * 2
def baseEnd_603812 : Nat := 103348593650898938824375

theorem tailTrace_603812 : CollatzResearch.WordTrace tailWord_603812 prefixEnd_603812 103348593650898938824375 := by
  unfold tailWord_603812
  simp only [CollatzResearch.WordTrace]
  refine ⟨11011416444249860862338845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14681888592333147816451793 11011416444249860862338845)
  ·
    refine ⟨4129281166593697823377067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11011416444249860862338845 4129281166593697823377067)
    ·
      refine ⟨6193921749890546735065601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4129281166593697823377067 6193921749890546735065601)
      ·
        refine ⟨4645441312417910051299201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6193921749890546735065601 4645441312417910051299201)
        ·
          refine ⟨3484080984313432538474401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4645441312417910051299201 3484080984313432538474401)
          ·
            refine ⟨2613060738235074403855801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3484080984313432538474401 2613060738235074403855801)
            ·
              refine ⟨1959795553676305802891851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2613060738235074403855801 1959795553676305802891851)
              ·
                refine ⟨2939693330514458704337777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1959795553676305802891851 2939693330514458704337777)
                ·
                  refine ⟨2204769997885844028253333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2939693330514458704337777 2204769997885844028253333)
                  ·
                    refine ⟨103348593650898938824375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2204769997885844028253333 103348593650898938824375)
                    ·
                      rfl

theorem cell23_603812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_603812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603812 prefixEnd_603812 := by exact prefixLift 603812
  have htrace : WordTrace (prefixWord ++ tailWord_603812) baseStart_603812 baseEnd_603812 := by
    simpa [prefixWord, tailWord_603812, baseEnd_603812] using wordTrace_append hprefix tailTrace_603812
  have hstable : (prefixWord ++ tailWord_603812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603812).length < 2 ^ (prefixWord ++ tailWord_603812).sum := by decide
  have hdescent : baseEnd_603812 < baseStart_603812 := by decide
  rcases family_descends (prefixWord ++ tailWord_603812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603836 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 4, 2, 2]
def baseStart_603836 : Nat := 118140960795 + 603836 * 2 ^ 59
def prefixEnd_603836 : Nat := 4983230072969 + 3 ^ 40 * 603836 * 2
def baseEnd_603836 : Nat := 310058104488404722573015

theorem tailTrace_603836 : CollatzResearch.WordTrace tailWord_603836 prefixEnd_603836 310058104488404722573015 := by
  unfold tailWord_603836
  simp only [CollatzResearch.WordTrace]
  refine ⟨11011854120206386911775681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14682472160275182549034241 11011854120206386911775681)
  ·
    refine ⟨8258890590154790183831761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11011854120206386911775681 8258890590154790183831761)
    ·
      refine ⟨6194167942616092637873821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8258890590154790183831761 6194167942616092637873821)
      ·
        refine ⟨2322812978481034739202683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6194167942616092637873821 2322812978481034739202683)
        ·
          refine ⟨3484219467721552108804025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2322812978481034739202683 3484219467721552108804025)
          ·
            refine ⟨2613164600791164081603019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3484219467721552108804025 2613164600791164081603019)
            ·
              refine ⟨3919746901186746122404529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2613164600791164081603019 3919746901186746122404529)
              ·
                refine ⟨2939810175890059591803397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3919746901186746122404529 2939810175890059591803397)
                ·
                  refine ⟨551214407979386173463137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2939810175890059591803397 551214407979386173463137)
                  ·
                    refine ⟨413410805984539630097353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 551214407979386173463137 413410805984539630097353)
                    ·
                      refine ⟨310058104488404722573015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 413410805984539630097353 310058104488404722573015)
                      ·
                        rfl

theorem cell23_603836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_603836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603836 prefixEnd_603836 := by exact prefixLift 603836
  have htrace : WordTrace (prefixWord ++ tailWord_603836) baseStart_603836 baseEnd_603836 := by
    simpa [prefixWord, tailWord_603836, baseEnd_603836] using wordTrace_append hprefix tailTrace_603836
  have hstable : (prefixWord ++ tailWord_603836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603836).length < 2 ^ (prefixWord ++ tailWord_603836).sum := by decide
  have hdescent : baseEnd_603836 < baseStart_603836 := by decide
  rcases family_descends (prefixWord ++ tailWord_603836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603889 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 2, 5]
def baseStart_603889 : Nat := 118140960795 + 603889 * 2 ^ 59
def prefixEnd_603889 : Nat := 4983230072969 + 3 ^ 40 * 603889 * 2
def baseEnd_603889 : Nat := 103361772987697671736757

theorem tailTrace_603889 : CollatzResearch.WordTrace tailWord_603889 prefixEnd_603889 103361772987697671736757 := by
  unfold tailWord_603889
  simp only [CollatzResearch.WordTrace]
  refine ⟨22025641309220763875230721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14683760872813842583487147 22025641309220763875230721)
  ·
    refine ⟨16519230981915572906423041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22025641309220763875230721 16519230981915572906423041)
    ·
      refine ⟨12389423236436679679817281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16519230981915572906423041 12389423236436679679817281)
      ·
        refine ⟨9292067427327509759862961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12389423236436679679817281 9292067427327509759862961)
        ·
          refine ⟨6969050570495632319897221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9292067427327509759862961 6969050570495632319897221)
          ·
            refine ⟨1306696981967931059980729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6969050570495632319897221 1306696981967931059980729)
            ·
              refine ⟨980022736475948294985547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1306696981967931059980729 980022736475948294985547)
              ·
                refine ⟨1470034104713922442478321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 980022736475948294985547 1470034104713922442478321)
                ·
                  refine ⟨1102525578535441831858741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1470034104713922442478321 1102525578535441831858741)
                  ·
                    refine ⟨103361772987697671736757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1102525578535441831858741 103361772987697671736757)
                    ·
                      rfl

theorem cell23_603889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_603889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603889 prefixEnd_603889 := by exact prefixLift 603889
  have htrace : WordTrace (prefixWord ++ tailWord_603889) baseStart_603889 baseEnd_603889 := by
    simpa [prefixWord, tailWord_603889, baseEnd_603889] using wordTrace_append hprefix tailTrace_603889
  have hstable : (prefixWord ++ tailWord_603889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603889).length < 2 ^ (prefixWord ++ tailWord_603889).sum := by decide
  have hdescent : baseEnd_603889 < baseStart_603889 := by decide
  rcases family_descends (prefixWord ++ tailWord_603889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603912 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_603912 : Nat := 118140960795 + 603912 * 2 ^ 59
def prefixEnd_603912 : Nat := 4983230072969 + 3 ^ 40 * 603912 * 2
def baseEnd_603912 : Nat := 310097129018146425222665

theorem tailTrace_603912 : CollatzResearch.WordTrace tailWord_603912 prefixEnd_603912 310097129018146425222665 := by
  unfold tailWord_603912
  simp only [CollatzResearch.WordTrace]
  refine ⟨11013240094068719401658995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14684320125424959202211993 11013240094068719401658995)
  ·
    refine ⟨16519860141103079102488493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11013240094068719401658995 16519860141103079102488493)
    ·
      refine ⟨6194947552913654663433185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16519860141103079102488493 6194947552913654663433185)
      ·
        refine ⟨4646210664685240997574889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6194947552913654663433185 4646210664685240997574889)
        ·
          refine ⟨3484657998513930748181167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4646210664685240997574889 3484657998513930748181167)
          ·
            refine ⟨5226986997770896122271751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3484657998513930748181167 5226986997770896122271751)
            ·
              refine ⟨7840480496656344183407627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5226986997770896122271751 7840480496656344183407627)
              ·
                refine ⟨11760720744984516275111441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7840480496656344183407627 11760720744984516275111441)
                ·
                  refine ⟨8820540558738387206333581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11760720744984516275111441 8820540558738387206333581)
                  ·
                    refine ⟨3307702709526895202375093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8820540558738387206333581 3307702709526895202375093)
                    ·
                      refine ⟨310097129018146425222665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3307702709526895202375093 310097129018146425222665)
                      ·
                        rfl

theorem cell23_603912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_603912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603912 prefixEnd_603912 := by exact prefixLift 603912
  have htrace : WordTrace (prefixWord ++ tailWord_603912) baseStart_603912 baseEnd_603912 := by
    simpa [prefixWord, tailWord_603912, baseEnd_603912] using wordTrace_append hprefix tailTrace_603912
  have hstable : (prefixWord ++ tailWord_603912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603912).length < 2 ^ (prefixWord ++ tailWord_603912).sum := by decide
  have hdescent : baseEnd_603912 < baseStart_603912 := by decide
  rcases family_descends (prefixWord ++ tailWord_603912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603953 : List Nat := [1, 2, 2, 3, 2, 3, 2, 3, 1, 4]
def baseStart_603953 : Nat := 118140960795 + 603953 * 2 ^ 59
def prefixEnd_603953 : Nat := 4983230072969 + 3 ^ 40 * 603953 * 2
def baseEnd_603953 : Nat := 103372727241660254936659

theorem tailTrace_603953 : CollatzResearch.WordTrace tailWord_603953 prefixEnd_603953 103372727241660254936659 := by
  unfold tailWord_603953
  simp only [CollatzResearch.WordTrace]
  refine ⟨22027975580988902805560513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14685317053992601870373675 22027975580988902805560513)
  ·
    refine ⟨16520981685741677104170385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22027975580988902805560513 16520981685741677104170385)
    ·
      refine ⟨12390736264306257828127789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16520981685741677104170385 12390736264306257828127789)
      ·
        refine ⟨4646526099114846685547921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12390736264306257828127789 4646526099114846685547921)
        ·
          refine ⟨3484894574336135014160941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4646526099114846685547921 3484894574336135014160941)
          ·
            refine ⟨1306835465376050630310353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3484894574336135014160941 1306835465376050630310353)
            ·
              refine ⟨980126599032037972732765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1306835465376050630310353 980126599032037972732765)
              ·
                refine ⟨367547474637014239774787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 980126599032037972732765 367547474637014239774787)
                ·
                  refine ⟨551321211955521359662181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367547474637014239774787 551321211955521359662181)
                  ·
                    refine ⟨103372727241660254936659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 551321211955521359662181 103372727241660254936659)
                    ·
                      rfl

theorem cell23_603953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 1, 4].length) (baseStart_603953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603953 prefixEnd_603953 := by exact prefixLift 603953
  have htrace : WordTrace (prefixWord ++ tailWord_603953) baseStart_603953 baseEnd_603953 := by
    simpa [prefixWord, tailWord_603953, baseEnd_603953] using wordTrace_append hprefix tailTrace_603953
  have hstable : (prefixWord ++ tailWord_603953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603953).length < 2 ^ (prefixWord ++ tailWord_603953).sum := by decide
  have hdescent : baseEnd_603953 < baseStart_603953 := by decide
  rcases family_descends (prefixWord ++ tailWord_603953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603966 : List Nat := [4, 2, 1, 2, 2, 1, 3, 2, 6]
def baseStart_603966 : Nat := 118140960795 + 603966 * 2 ^ 59
def prefixEnd_603966 : Nat := 4983230072969 + 3 ^ 40 * 603966 * 2
def baseEnd_603966 : Nat := 34458317441498801549713

theorem tailTrace_603966 : CollatzResearch.WordTrace tailWord_603966 prefixEnd_603966 34458317441498801549713 := by
  unfold tailWord_603966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2753556216242725753222969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14685633153294537350522501 2753556216242725753222969)
  ·
    refine ⟨2065167162182044314917227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2753556216242725753222969 2065167162182044314917227)
    ·
      refine ⟨3097750743273066472375841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2065167162182044314917227 3097750743273066472375841)
      ·
        refine ⟨2323313057454799854281881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3097750743273066472375841 2323313057454799854281881)
        ·
          refine ⟨1742484793091099890711411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2323313057454799854281881 1742484793091099890711411)
          ·
            refine ⟨2613727189636649836067117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1742484793091099890711411 2613727189636649836067117)
            ·
              refine ⟨980147696113743688525169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2613727189636649836067117 980147696113743688525169)
              ·
                refine ⟨735110772085307766393877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 980147696113743688525169 735110772085307766393877)
                ·
                  refine ⟨34458317441498801549713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 735110772085307766393877 34458317441498801549713)
                  ·
                    rfl

theorem cell23_603966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_603966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603966 prefixEnd_603966 := by exact prefixLift 603966
  have htrace : WordTrace (prefixWord ++ tailWord_603966) baseStart_603966 baseEnd_603966 := by
    simpa [prefixWord, tailWord_603966, baseEnd_603966] using wordTrace_append hprefix tailTrace_603966
  have hstable : (prefixWord ++ tailWord_603966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603966).length < 2 ^ (prefixWord ++ tailWord_603966).sum := by decide
  have hdescent : baseEnd_603966 < baseStart_603966 := by decide
  rcases family_descends (prefixWord ++ tailWord_603966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603976 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 3, 1, 3]
def baseStart_603976 : Nat := 118140960795 + 603976 * 2 ^ 59
def prefixEnd_603976 : Nat := 4983230072969 + 3 ^ 40 * 603976 * 2
def baseEnd_603976 : Nat := 310129991780034174822371

theorem tailTrace_603976 : CollatzResearch.WordTrace tailWord_603976 prefixEnd_603976 310129991780034174822371 := by
  unfold tailWord_603976
  simp only [CollatzResearch.WordTrace]
  refine ⟨11014407229952788866823891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14685876306603718489098521 11014407229952788866823891)
  ·
    refine ⟨16521610844929183300235837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11014407229952788866823891 16521610844929183300235837)
    ·
      refine ⟨6195604066848443737588439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16521610844929183300235837 6195604066848443737588439)
      ·
        refine ⟨9293406100272665606382659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6195604066848443737588439 9293406100272665606382659)
        ·
          refine ⟨13940109150408998409573989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9293406100272665606382659 13940109150408998409573989)
          ·
            refine ⟨2613770465701687201795123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13940109150408998409573989 2613770465701687201795123)
            ·
              refine ⟨3920655698552530802692685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2613770465701687201795123 3920655698552530802692685)
              ·
                refine ⟨1470245886957199051009757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3920655698552530802692685 1470245886957199051009757)
                ·
                  refine ⟨551342207608949644128659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1470245886957199051009757 551342207608949644128659)
                  ·
                    refine ⟨827013311413424466192989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 551342207608949644128659 827013311413424466192989)
                    ·
                      refine ⟨310129991780034174822371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 827013311413424466192989 310129991780034174822371)
                      ·
                        rfl

theorem cell23_603976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_603976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603976 prefixEnd_603976 := by exact prefixLift 603976
  have htrace : WordTrace (prefixWord ++ tailWord_603976) baseStart_603976 baseEnd_603976 := by
    simpa [prefixWord, tailWord_603976, baseEnd_603976] using wordTrace_append hprefix tailTrace_603976
  have hstable : (prefixWord ++ tailWord_603976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603976).length < 2 ^ (prefixWord ++ tailWord_603976).sum := by decide
  have hdescent : baseEnd_603976 < baseStart_603976 := by decide
  rcases family_descends (prefixWord ++ tailWord_603976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603986 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2]
def baseStart_603986 : Nat := 118140960795 + 603986 * 2 ^ 59
def prefixEnd_603986 : Nat := 4983230072969 + 3 ^ 40 * 603986 * 2
def baseEnd_603986 : Nat := 310135126586579135697325

theorem tailTrace_603986 : CollatzResearch.WordTrace tailWord_603986 prefixEnd_603986 310135126586579135697325 := by
  unfold tailWord_603986
  simp only [CollatzResearch.WordTrace]
  refine ⟨5507294797467337360377953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14686119459912899627674541 5507294797467337360377953)
  ·
    refine ⟨4130471098100503020283465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5507294797467337360377953 4130471098100503020283465)
    ·
      refine ⟨3097853323575377265212599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4130471098100503020283465 3097853323575377265212599)
      ·
        refine ⟨4646779985363065897818899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3097853323575377265212599 4646779985363065897818899)
        ·
          refine ⟨6970169978044598846728349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4646779985363065897818899 6970169978044598846728349)
          ·
            refine ⟨2613813741766724567523131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6970169978044598846728349 2613813741766724567523131)
            ·
              refine ⟨3920720612650086851284697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2613813741766724567523131 3920720612650086851284697)
              ·
                refine ⟨2940540459487565138463523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3920720612650086851284697 2940540459487565138463523)
                ·
                  refine ⟨4410810689231347707695285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940540459487565138463523 4410810689231347707695285)
                  ·
                    refine ⟨413513502115438847596433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4410810689231347707695285 413513502115438847596433)
                    ·
                      refine ⟨310135126586579135697325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 413513502115438847596433 310135126586579135697325)
                      ·
                        rfl

theorem cell23_603986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_603986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603986 prefixEnd_603986 := by exact prefixLift 603986
  have htrace : WordTrace (prefixWord ++ tailWord_603986) baseStart_603986 baseEnd_603986 := by
    simpa [prefixWord, tailWord_603986, baseEnd_603986] using wordTrace_append hprefix tailTrace_603986
  have hstable : (prefixWord ++ tailWord_603986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603986).length < 2 ^ (prefixWord ++ tailWord_603986).sum := by decide
  have hdescent : baseEnd_603986 < baseStart_603986 := by decide
  rcases family_descends (prefixWord ++ tailWord_603986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604019 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 3]
def baseStart_604019 : Nat := 118140960795 + 604019 * 2 ^ 59
def prefixEnd_604019 : Nat := 4983230072969 + 3 ^ 40 * 604019 * 2
def baseEnd_604019 : Nat := 310152071448177506584673

theorem tailTrace_604019 : CollatzResearch.WordTrace tailWord_604019 prefixEnd_604019 310152071448177506584673 := by
  unfold tailWord_604019
  simp only [CollatzResearch.WordTrace]
  refine ⟨22030382798749796077463111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14686921865833197384975407 22030382798749796077463111)
  ·
    refine ⟨33045574198124694116194667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22030382798749796077463111 33045574198124694116194667)
    ·
      refine ⟨49568361297187041174292001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33045574198124694116194667 49568361297187041174292001)
      ·
        refine ⟨37176270972890280880719001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49568361297187041174292001 37176270972890280880719001)
        ·
          refine ⟨27882203229667710660539251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37176270972890280880719001 27882203229667710660539251)
          ·
            refine ⟨41823304844501565990808877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27882203229667710660539251 41823304844501565990808877)
            ·
              refine ⟨15683739316688087246553329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41823304844501565990808877 15683739316688087246553329)
              ·
                refine ⟨11762804487516065434914997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15683739316688087246553329 11762804487516065434914997)
                ·
                  refine ⟨1102762920704631134523281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11762804487516065434914997 1102762920704631134523281)
                  ·
                    refine ⟨827072190528473350892461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1102762920704631134523281 827072190528473350892461)
                    ·
                      refine ⟨310152071448177506584673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 827072190528473350892461 310152071448177506584673)
                      ·
                        rfl

theorem cell23_604019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 3].length) (baseStart_604019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604019 prefixEnd_604019 := by exact prefixLift 604019
  have htrace : WordTrace (prefixWord ++ tailWord_604019) baseStart_604019 baseEnd_604019 := by
    simpa [prefixWord, tailWord_604019, baseEnd_604019] using wordTrace_append hprefix tailTrace_604019
  have hstable : (prefixWord ++ tailWord_604019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604019).length < 2 ^ (prefixWord ++ tailWord_604019).sum := by decide
  have hdescent : baseEnd_604019 < baseStart_604019 := by decide
  rcases family_descends (prefixWord ++ tailWord_604019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604050 : List Nat := [3, 2, 3, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_604050 : Nat := 118140960795 + 604050 * 2 ^ 59
def prefixEnd_604050 : Nat := 4983230072969 + 3 ^ 40 * 604050 * 2
def baseEnd_604050 : Nat := 310167989348466885297031

theorem tailTrace_604050 : CollatzResearch.WordTrace tailWord_604050 prefixEnd_604050 310167989348466885297031 := by
  unfold tailWord_604050
  simp only [CollatzResearch.WordTrace]
  refine ⟨5507878365409372092960401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14687675641091658914561069 5507878365409372092960401)
  ·
    refine ⟨4130908774057029069720301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5507878365409372092960401 4130908774057029069720301)
    ·
      refine ⟨1549090790271385901145113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4130908774057029069720301 1549090790271385901145113)
      ·
        refine ⟨1161818092703539425858835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1549090790271385901145113 1161818092703539425858835)
        ·
          refine ⟨1742727139055309138788253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1161818092703539425858835 1742727139055309138788253)
          ·
            refine ⟨653522677145740927045595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1742727139055309138788253 653522677145740927045595)
            ·
              refine ⟨980284015718611390568393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653522677145740927045595 980284015718611390568393)
              ·
                refine ⟨735213011788958542926295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 980284015718611390568393 735213011788958542926295)
                ·
                  refine ⟨1102819517683437814389443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735213011788958542926295 1102819517683437814389443)
                  ·
                    refine ⟨1654229276525156721584165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1102819517683437814389443 1654229276525156721584165)
                    ·
                      refine ⟨310167989348466885297031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1654229276525156721584165 310167989348466885297031)
                      ·
                        rfl

theorem cell23_604050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_604050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604050 prefixEnd_604050 := by exact prefixLift 604050
  have htrace : WordTrace (prefixWord ++ tailWord_604050) baseStart_604050 baseEnd_604050 := by
    simpa [prefixWord, tailWord_604050, baseEnd_604050] using wordTrace_append hprefix tailTrace_604050
  have hstable : (prefixWord ++ tailWord_604050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604050).length < 2 ^ (prefixWord ++ tailWord_604050).sum := by decide
  have hdescent : baseEnd_604050 < baseStart_604050 := by decide
  rcases family_descends (prefixWord ++ tailWord_604050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604054 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_604054 : Nat := 118140960795 + 604054 * 2 ^ 59
def prefixEnd_604054 : Nat := 4983230072969 + 3 ^ 40 * 604054 * 2
def baseEnd_604054 : Nat := 310170043271084869647013

theorem tailTrace_604054 : CollatzResearch.WordTrace tailWord_604054 prefixEnd_604054 310170043271084869647013 := by
  unfold tailWord_604054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1376978709601437315936701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14687772902415331369991477 1376978709601437315936701)
  ·
    refine ⟨516367016100538993476263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1376978709601437315936701 516367016100538993476263)
    ·
      refine ⟨774550524150808490214395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 516367016100538993476263 774550524150808490214395)
      ·
        refine ⟨1161825786226212735321593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774550524150808490214395 1161825786226212735321593)
        ·
          refine ⟨871369339669659551491195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1161825786226212735321593 871369339669659551491195)
          ·
            refine ⟨1307054009504489327236793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871369339669659551491195 1307054009504489327236793)
            ·
              refine ⟨980290507128366995427595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1307054009504489327236793 980290507128366995427595)
              ·
                refine ⟨1470435760692550493141393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 980290507128366995427595 1470435760692550493141393)
                ·
                  refine ⟨1102826820519412869856045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1470435760692550493141393 1102826820519412869856045)
                  ·
                    refine ⟨413560057694779826196017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1102826820519412869856045 413560057694779826196017)
                    ·
                      refine ⟨310170043271084869647013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 413560057694779826196017 310170043271084869647013)
                      ·
                        rfl

theorem cell23_604054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_604054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604054 prefixEnd_604054 := by exact prefixLift 604054
  have htrace : WordTrace (prefixWord ++ tailWord_604054) baseStart_604054 baseEnd_604054 := by
    simpa [prefixWord, tailWord_604054, baseEnd_604054] using wordTrace_append hprefix tailTrace_604054
  have hstable : (prefixWord ++ tailWord_604054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604054).length < 2 ^ (prefixWord ++ tailWord_604054).sum := by decide
  have hdescent : baseEnd_604054 < baseStart_604054 := by decide
  rcases family_descends (prefixWord ++ tailWord_604054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604076 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 7, 3, 2]
def baseStart_604076 : Nat := 118140960795 + 604076 * 2 ^ 59
def prefixEnd_604076 : Nat := 4983230072969 + 3 ^ 40 * 604076 * 2
def baseEnd_604076 : Nat := 310181339845483783571911

theorem tailTrace_604076 : CollatzResearch.WordTrace tailWord_604076 prefixEnd_604076 310181339845483783571911 := by
  unfold tailWord_604076
  simp only [CollatzResearch.WordTrace]
  refine ⟨11016230879771647406144041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14688307839695529874858721 11016230879771647406144041)
  ·
    refine ⟨8262173159828735554608031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11016230879771647406144041 8262173159828735554608031)
    ·
      refine ⟨12393259739743103331912047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8262173159828735554608031 12393259739743103331912047)
      ·
        refine ⟨18589889609614654997868071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12393259739743103331912047 18589889609614654997868071)
        ·
          refine ⟨27884834414421982496802107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18589889609614654997868071 27884834414421982496802107)
          ·
            refine ⟨41827251621632973745203161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27884834414421982496802107 41827251621632973745203161)
            ·
              refine ⟨31370438716224730308902371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41827251621632973745203161 31370438716224730308902371)
              ·
                refine ⟨47055658074337095463353557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31370438716224730308902371 47055658074337095463353557)
                ·
                  refine ⟨1102866986117275674922349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 47055658074337095463353557 1102866986117275674922349)
                  ·
                    refine ⟨413575119793978378095881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1102866986117275674922349 413575119793978378095881)
                    ·
                      refine ⟨310181339845483783571911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 413575119793978378095881 310181339845483783571911)
                      ·
                        rfl

theorem cell23_604076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 3, 2].length) (baseStart_604076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604076 prefixEnd_604076 := by exact prefixLift 604076
  have htrace : WordTrace (prefixWord ++ tailWord_604076) baseStart_604076 baseEnd_604076 := by
    simpa [prefixWord, tailWord_604076, baseEnd_604076] using wordTrace_append hprefix tailTrace_604076
  have hstable : (prefixWord ++ tailWord_604076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604076).length < 2 ^ (prefixWord ++ tailWord_604076).sum := by decide
  have hdescent : baseEnd_604076 < baseStart_604076 := by decide
  rcases family_descends (prefixWord ++ tailWord_604076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604078 : List Nat := [4, 1, 5, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_604078 : Nat := 118140960795 + 604078 * 2 ^ 59
def prefixEnd_604078 : Nat := 4983230072969 + 3 ^ 40 * 604078 * 2
def baseEnd_604078 : Nat := 310182366806792775746903

theorem tailTrace_604078 : CollatzResearch.WordTrace tailWord_604078 prefixEnd_604078 310182366806792775746903 := by
  unfold tailWord_604078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2754066838192006144232611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14688356470357366102573925 2754066838192006144232611)
  ·
    refine ⟨4131100257288009216348917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2754066838192006144232611 4131100257288009216348917)
    ·
      refine ⟨387290649120750864032711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4131100257288009216348917 387290649120750864032711)
      ·
        refine ⟨580935973681126296049067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387290649120750864032711 580935973681126296049067)
        ·
          refine ⟨871403960521689444073601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580935973681126296049067 871403960521689444073601)
          ·
            refine ⟨653552970391267083055201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 871403960521689444073601 653552970391267083055201)
            ·
              refine ⟨490164727793450312291401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653552970391267083055201 490164727793450312291401)
              ·
                refine ⟨367623545845087734218551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490164727793450312291401 367623545845087734218551)
                ·
                  refine ⟨551435318767631601327827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367623545845087734218551 551435318767631601327827)
                  ·
                    refine ⟨827152978151447401991741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 551435318767631601327827 827152978151447401991741)
                    ·
                      refine ⟨310182366806792775746903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 827152978151447401991741 310182366806792775746903)
                      ·
                        rfl

theorem cell23_604078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_604078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604078 prefixEnd_604078 := by exact prefixLift 604078
  have htrace : WordTrace (prefixWord ++ tailWord_604078) baseStart_604078 baseEnd_604078 := by
    simpa [prefixWord, tailWord_604078, baseEnd_604078] using wordTrace_append hprefix tailTrace_604078
  have hstable : (prefixWord ++ tailWord_604078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604078).length < 2 ^ (prefixWord ++ tailWord_604078).sum := by decide
  have hdescent : baseEnd_604078 < baseStart_604078 := by decide
  rcases family_descends (prefixWord ++ tailWord_604078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604083 : List Nat := [1, 1, 1, 2, 3, 1, 6, 2, 2, 1, 3]
def baseStart_604083 : Nat := 118140960795 + 604083 * 2 ^ 59
def prefixEnd_604083 : Nat := 4983230072969 + 3 ^ 40 * 604083 * 2
def baseEnd_604083 : Nat := 310184934210065256184379

theorem tailTrace_604083 : CollatzResearch.WordTrace tailWord_604083 prefixEnd_604083 310184934210065256184379 := by
  unfold tailWord_604083
  simp only [CollatzResearch.WordTrace]
  refine ⟨22032717070517935007792903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14688478047011956671861935 22032717070517935007792903)
  ·
    refine ⟨33049075605776902511689355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22032717070517935007792903 33049075605776902511689355)
    ·
      refine ⟨49573613408665353767534033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33049075605776902511689355 49573613408665353767534033)
      ·
        refine ⟨37180210056499015325650525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49573613408665353767534033 37180210056499015325650525)
        ·
          refine ⟨13942578771187130747118947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37180210056499015325650525 13942578771187130747118947)
          ·
            refine ⟨20913868156780696120678421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13942578771187130747118947 20913868156780696120678421)
            ·
              refine ⟨980337569849095130656801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20913868156780696120678421 980337569849095130656801)
              ·
                refine ⟨735253177386821347992601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 980337569849095130656801 735253177386821347992601)
                ·
                  refine ⟨551439883040116010994451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 735253177386821347992601 551439883040116010994451)
                  ·
                    refine ⟨827159824560174016491677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 551439883040116010994451 827159824560174016491677)
                    ·
                      refine ⟨310184934210065256184379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 827159824560174016491677 310184934210065256184379)
                      ·
                        rfl

theorem cell23_604083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 1, 3].length) (baseStart_604083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604083 prefixEnd_604083 := by exact prefixLift 604083
  have htrace : WordTrace (prefixWord ++ tailWord_604083) baseStart_604083 baseEnd_604083 := by
    simpa [prefixWord, tailWord_604083, baseEnd_604083] using wordTrace_append hprefix tailTrace_604083
  have hstable : (prefixWord ++ tailWord_604083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604083).length < 2 ^ (prefixWord ++ tailWord_604083).sum := by decide
  have hdescent : baseEnd_604083 < baseStart_604083 := by decide
  rcases family_descends (prefixWord ++ tailWord_604083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604089 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 1, 5, 4]
def baseStart_604089 : Nat := 118140960795 + 604089 * 2 ^ 59
def prefixEnd_604089 : Nat := 4983230072969 + 3 ^ 40 * 604089 * 2
def baseEnd_604089 : Nat := 310188015093992232709351

theorem tailTrace_604089 : CollatzResearch.WordTrace tailWord_604089 prefixEnd_604089 310188015093992232709351 := by
  unfold tailWord_604089
  simp only [CollatzResearch.WordTrace]
  refine ⟨22032935908496198032511321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14688623938997465355007547 22032935908496198032511321)
  ·
    refine ⟨16524701931372148524383491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22032935908496198032511321 16524701931372148524383491)
    ·
      refine ⟨24787052897058222786575237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16524701931372148524383491 24787052897058222786575237)
      ·
        refine ⟨4647572418198416772482857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24787052897058222786575237 4647572418198416772482857)
        ·
          refine ⟨3485679313648812579362143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4647572418198416772482857 3485679313648812579362143)
          ·
            refine ⟨5228518970473218869043215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3485679313648812579362143 5228518970473218869043215)
            ·
              refine ⟨7842778455709828303564823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5228518970473218869043215 7842778455709828303564823)
              ·
                refine ⟨11764167683564742455347235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7842778455709828303564823 11764167683564742455347235)
                ·
                  refine ⟨17646251525347113683020853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11764167683564742455347235 17646251525347113683020853)
                  ·
                    refine ⟨1654336080501291907783205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17646251525347113683020853 1654336080501291907783205)
                    ·
                      refine ⟨310188015093992232709351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1654336080501291907783205 310188015093992232709351)
                      ·
                        rfl

theorem cell23_604089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_604089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604089 prefixEnd_604089 := by exact prefixLift 604089
  have htrace : WordTrace (prefixWord ++ tailWord_604089) baseStart_604089 baseEnd_604089 := by
    simpa [prefixWord, tailWord_604089, baseEnd_604089] using wordTrace_append hprefix tailTrace_604089
  have hstable : (prefixWord ++ tailWord_604089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604089).length < 2 ^ (prefixWord ++ tailWord_604089).sum := by decide
  have hdescent : baseEnd_604089 < baseStart_604089 := by decide
  rcases family_descends (prefixWord ++ tailWord_604089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604093 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 3, 3, 2]
def baseStart_604093 : Nat := 118140960795 + 604093 * 2 ^ 59
def prefixEnd_604093 : Nat := 4983230072969 + 3 ^ 40 * 604093 * 2
def baseEnd_604093 : Nat := 310190069016610217059333

theorem tailTrace_604093 : CollatzResearch.WordTrace tailWord_604093 prefixEnd_604093 310190069016610217059333 := by
  unfold tailWord_604093
  simp only [CollatzResearch.WordTrace]
  refine ⟨22033081800481706715656933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14688721200321137810437955 22033081800481706715656933)
  ·
    refine ⟨4131202837590320009185675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22033081800481706715656933 4131202837590320009185675)
    ·
      refine ⟨6196804256385480013778513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4131202837590320009185675 6196804256385480013778513)
      ·
        refine ⟨4647603192289110010333885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6196804256385480013778513 4647603192289110010333885)
        ·
          refine ⟨1742851197108416253875207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4647603192289110010333885 1742851197108416253875207)
          ·
            refine ⟨2614276795662624380812811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1742851197108416253875207 2614276795662624380812811)
            ·
              refine ⟨3921415193493936571219217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2614276795662624380812811 3921415193493936571219217)
              ·
                refine ⟨2941061395120452428414413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3921415193493936571219217 2941061395120452428414413)
                ·
                  refine ⟨1102898023170169660655405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2941061395120452428414413 1102898023170169660655405)
                  ·
                    refine ⟨413586758688813622745777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1102898023170169660655405 413586758688813622745777)
                    ·
                      refine ⟨310190069016610217059333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 413586758688813622745777 310190069016610217059333)
                      ·
                        rfl

theorem cell23_604093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_604093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604093 prefixEnd_604093 := by exact prefixLift 604093
  have htrace : WordTrace (prefixWord ++ tailWord_604093) baseStart_604093 baseEnd_604093 := by
    simpa [prefixWord, tailWord_604093, baseEnd_604093] using wordTrace_append hprefix tailTrace_604093
  have hstable : (prefixWord ++ tailWord_604093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604093).length < 2 ^ (prefixWord ++ tailWord_604093).sum := by decide
  have hdescent : baseEnd_604093 < baseStart_604093 := by decide
  rcases family_descends (prefixWord ++ tailWord_604093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604119 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 4]
def baseStart_604119 : Nat := 118140960795 + 604119 * 2 ^ 59
def prefixEnd_604119 : Nat := 4983230072969 + 3 ^ 40 * 604119 * 2
def baseEnd_604119 : Nat := 310203419513627115334213

theorem tailTrace_604119 : CollatzResearch.WordTrace tailWord_604119 prefixEnd_604119 310203419513627115334213 := by
  unfold tailWord_604119
  simp only [CollatzResearch.WordTrace]
  refine ⟨22034030098387513156103411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14689353398925008770735607 22034030098387513156103411)
  ·
    refine ⟨33051045147581269734155117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22034030098387513156103411 33051045147581269734155117)
    ·
      refine ⟨12394141930342976150308169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33051045147581269734155117 12394141930342976150308169)
      ·
        refine ⟨9295606447757232112731127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12394141930342976150308169 9295606447757232112731127)
        ·
          refine ⟨13943409671635848169096691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9295606447757232112731127 13943409671635848169096691)
          ·
            refine ⟨20915114507453772253645037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13943409671635848169096691 20915114507453772253645037)
            ·
              refine ⟨7843167940295164595116889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20915114507453772253645037 7843167940295164595116889)
              ·
                refine ⟨5882375955221373446337667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7843167940295164595116889 5882375955221373446337667)
                ·
                  refine ⟨8823563932832060169506501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5882375955221373446337667 8823563932832060169506501)
                  ·
                    refine ⟨1654418237406011281782469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8823563932832060169506501 1654418237406011281782469)
                    ·
                      refine ⟨310203419513627115334213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1654418237406011281782469 310203419513627115334213)
                      ·
                        rfl

theorem cell23_604119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_604119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604119 prefixEnd_604119 := by exact prefixLift 604119
  have htrace : WordTrace (prefixWord ++ tailWord_604119) baseStart_604119 baseEnd_604119 := by
    simpa [prefixWord, tailWord_604119, baseEnd_604119] using wordTrace_append hprefix tailTrace_604119
  have hstable : (prefixWord ++ tailWord_604119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604119).length < 2 ^ (prefixWord ++ tailWord_604119).sum := by decide
  have hdescent : baseEnd_604119 < baseStart_604119 := by decide
  rcases family_descends (prefixWord ++ tailWord_604119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604127 : List Nat := [1, 1, 2, 3, 4, 3, 2, 1, 1, 3, 2]
def baseStart_604127 : Nat := 118140960795 + 604127 * 2 ^ 59
def prefixEnd_604127 : Nat := 4983230072969 + 3 ^ 40 * 604127 * 2
def baseEnd_604127 : Nat := 310207527358863084034177

theorem tailTrace_604127 : CollatzResearch.WordTrace tailWord_604127 prefixEnd_604127 310207527358863084034177 := by
  unfold tailWord_604127
  simp only [CollatzResearch.WordTrace]
  refine ⟨22034321882358530522394635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14689547921572353681596423 22034321882358530522394635)
  ·
    refine ⟨33051482823537795783591953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22034321882358530522394635 33051482823537795783591953)
    ·
      refine ⟨24788612117653346837693965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33051482823537795783591953 24788612117653346837693965)
      ·
        refine ⟨9295729544120005064135237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24788612117653346837693965 9295729544120005064135237)
        ·
          refine ⟨1742949289522500949525357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9295729544120005064135237 1742949289522500949525357)
          ·
            refine ⟨653605983570937856072009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1742949289522500949525357 653605983570937856072009)
            ·
              refine ⟨490204487678203392054007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653605983570937856072009 490204487678203392054007)
              ·
                refine ⟨735306731517305088081011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490204487678203392054007 735306731517305088081011)
                ·
                  refine ⟨1102960097275957632121517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735306731517305088081011 1102960097275957632121517)
                  ·
                    refine ⟨413610036478484112045569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1102960097275957632121517 413610036478484112045569)
                    ·
                      refine ⟨310207527358863084034177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 413610036478484112045569 310207527358863084034177)
                      ·
                        rfl

theorem cell23_604127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_604127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604127 prefixEnd_604127 := by exact prefixLift 604127
  have htrace : WordTrace (prefixWord ++ tailWord_604127) baseStart_604127 baseEnd_604127 := by
    simpa [prefixWord, tailWord_604127, baseEnd_604127] using wordTrace_append hprefix tailTrace_604127
  have hstable : (prefixWord ++ tailWord_604127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604127).length < 2 ^ (prefixWord ++ tailWord_604127).sum := by decide
  have hdescent : baseEnd_604127 < baseStart_604127 := by decide
  rcases family_descends (prefixWord ++ tailWord_604127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604156 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 2, 3, 3]
def baseStart_604156 : Nat := 118140960795 + 604156 * 2 ^ 59
def prefixEnd_604156 : Nat := 4983230072969 + 3 ^ 40 * 604156 * 2
def baseEnd_604156 : Nat := 310222418297843470571543

theorem tailTrace_604156 : CollatzResearch.WordTrace tailWord_604156 prefixEnd_604156 310222418297843470571543 := by
  unfold tailWord_604156
  simp only [CollatzResearch.WordTrace]
  refine ⟨11017689799626734237600161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14690253066168978983466881 11017689799626734237600161)
  ·
    refine ⟨8263267349720050678200121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11017689799626734237600161 8263267349720050678200121)
    ·
      refine ⟨6197450512290038008650091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8263267349720050678200121 6197450512290038008650091)
      ·
        refine ⟨9296175768435057012975137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6197450512290038008650091 9296175768435057012975137)
        ·
          refine ⟨6972131826326292759731353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9296175768435057012975137 6972131826326292759731353)
          ·
            refine ⟨5229098869744719569798515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6972131826326292759731353 5229098869744719569798515)
            ·
              refine ⟨7843648304617079354697773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5229098869744719569798515 7843648304617079354697773)
              ·
                refine ⟨2941368114231404758011665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7843648304617079354697773 2941368114231404758011665)
                ·
                  refine ⟨2206026085673553568508749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2941368114231404758011665 2206026085673553568508749)
                  ·
                    refine ⟨827259782127582588190781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2206026085673553568508749 827259782127582588190781)
                    ·
                      refine ⟨310222418297843470571543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 827259782127582588190781 310222418297843470571543)
                      ·
                        rfl

theorem cell23_604156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_604156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604156 prefixEnd_604156 := by exact prefixLift 604156
  have htrace : WordTrace (prefixWord ++ tailWord_604156) baseStart_604156 baseEnd_604156 := by
    simpa [prefixWord, tailWord_604156, baseEnd_604156] using wordTrace_append hprefix tailTrace_604156
  have hstable : (prefixWord ++ tailWord_604156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604156).length < 2 ^ (prefixWord ++ tailWord_604156).sum := by decide
  have hdescent : baseEnd_604156 < baseStart_604156 := by decide
  rcases family_descends (prefixWord ++ tailWord_604156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604169 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 5, 2, 5]
def baseStart_604169 : Nat := 118140960795 + 604169 * 2 ^ 59
def prefixEnd_604169 : Nat := 4983230072969 + 3 ^ 40 * 604169 * 2
def baseEnd_604169 : Nat := 310229093546351919708983

theorem tailTrace_604169 : CollatzResearch.WordTrace tailWord_604169 prefixEnd_604169 310229093546351919708983 := by
  unfold tailWord_604169
  simp only [CollatzResearch.WordTrace]
  refine ⟨22035853748206371695423561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14690569165470914463615707 22035853748206371695423561)
  ·
    refine ⟨16526890311154778771567671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22035853748206371695423561 16526890311154778771567671)
    ·
      refine ⟨24790335466732168157351507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16526890311154778771567671 24790335466732168157351507)
      ·
        refine ⟨37185503200098252236027261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24790335466732168157351507 37185503200098252236027261)
        ·
          refine ⟨13944563700036844588510223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37185503200098252236027261 13944563700036844588510223)
          ·
            refine ⟨20916845550055266882765335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13944563700036844588510223 20916845550055266882765335)
            ·
              refine ⟨31375268325082900324148003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20916845550055266882765335 31375268325082900324148003)
              ·
                refine ⟨47062902487624350486222005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31375268325082900324148003 47062902487624350486222005)
                ·
                  refine ⟨4412147108214782858083313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47062902487624350486222005 4412147108214782858083313)
                  ·
                    refine ⟨3309110331161087143562485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4412147108214782858083313 3309110331161087143562485)
                    ·
                      refine ⟨310229093546351919708983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3309110331161087143562485 310229093546351919708983)
                      ·
                        rfl

theorem cell23_604169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_604169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604169 prefixEnd_604169 := by exact prefixLift 604169
  have htrace : WordTrace (prefixWord ++ tailWord_604169) baseStart_604169 baseEnd_604169 := by
    simpa [prefixWord, tailWord_604169, baseEnd_604169] using wordTrace_append hprefix tailTrace_604169
  have hstable : (prefixWord ++ tailWord_604169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604169).length < 2 ^ (prefixWord ++ tailWord_604169).sum := by decide
  have hdescent : baseEnd_604169 < baseStart_604169 := by decide
  rcases family_descends (prefixWord ++ tailWord_604169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604193 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 2, 5]
def baseStart_604193 : Nat := 118140960795 + 604193 * 2 ^ 59
def prefixEnd_604193 : Nat := 4983230072969 + 3 ^ 40 * 604193 * 2
def baseEnd_604193 : Nat := 103413805694019941936291

theorem tailTrace_604193 : CollatzResearch.WordTrace tailWord_604193 prefixEnd_604193 103413805694019941936291 := by
  unfold tailWord_604193
  simp only [CollatzResearch.WordTrace]
  refine ⟨22036729100119423794297233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14691152733412949196198155 22036729100119423794297233)
  ·
    refine ⟨16527546825089567845722925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22036729100119423794297233 16527546825089567845722925)
    ·
      refine ⟨6197830059408587942146097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16527546825089567845722925 6197830059408587942146097)
      ·
        refine ⟨4648372544556440956609573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6197830059408587942146097 4648372544556440956609573)
        ·
          refine ⟨871569852104332679364295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4648372544556440956609573 871569852104332679364295)
          ·
            refine ⟨1307354778156499019046443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871569852104332679364295 1307354778156499019046443)
            ·
              refine ⟨1961032167234748528569665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307354778156499019046443 1961032167234748528569665)
              ·
                refine ⟨1470774125426061396427249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1961032167234748528569665 1470774125426061396427249)
                ·
                  refine ⟨1103080594069546047320437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1470774125426061396427249 1103080594069546047320437)
                  ·
                    refine ⟨103413805694019941936291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1103080594069546047320437 103413805694019941936291)
                    ·
                      rfl

theorem cell23_604193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_604193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604193 prefixEnd_604193 := by exact prefixLift 604193
  have htrace : WordTrace (prefixWord ++ tailWord_604193) baseStart_604193 baseEnd_604193 := by
    simpa [prefixWord, tailWord_604193, baseEnd_604193] using wordTrace_append hprefix tailTrace_604193
  have hstable : (prefixWord ++ tailWord_604193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604193).length < 2 ^ (prefixWord ++ tailWord_604193).sum := by decide
  have hdescent : baseEnd_604193 < baseStart_604193 := by decide
  rcases family_descends (prefixWord ++ tailWord_604193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604213 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 2, 4, 2]
def baseStart_604213 : Nat := 118140960795 + 604213 * 2 ^ 59
def prefixEnd_604213 : Nat := 4983230072969 + 3 ^ 40 * 604213 * 2
def baseEnd_604213 : Nat := 310251686695149747558781

theorem tailTrace_604213 : CollatzResearch.WordTrace tailWord_604213 prefixEnd_604213 310251686695149747558781 := by
  unfold tailWord_604213
  simp only [CollatzResearch.WordTrace]
  refine ⟨22037458560046967210025293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14691639040031311473350195 22037458560046967210025293)
  ·
    refine ⟨8264046960017612703759485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22037458560046967210025293 8264046960017612703759485)
    ·
      refine ⟨3099017610006604763909807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8264046960017612703759485 3099017610006604763909807)
      ·
        refine ⟨4648526415009907145864711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3099017610006604763909807 4648526415009907145864711)
        ·
          refine ⟨6972789622514860718797067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4648526415009907145864711 6972789622514860718797067)
          ·
            refine ⟨10459184433772291078195601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6972789622514860718797067 10459184433772291078195601)
            ·
              refine ⟨7844388325329218308646701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10459184433772291078195601 7844388325329218308646701)
              ·
                refine ⟨2941645621998456865742513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7844388325329218308646701 2941645621998456865742513)
                ·
                  refine ⟨2206234216498842649306885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2941645621998456865742513 2206234216498842649306885)
                  ·
                    refine ⟨413668915593532996745041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2206234216498842649306885 413668915593532996745041)
                    ·
                      refine ⟨310251686695149747558781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 413668915593532996745041 310251686695149747558781)
                      ·
                        rfl

theorem cell23_604213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_604213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604213 prefixEnd_604213 := by exact prefixLift 604213
  have htrace : WordTrace (prefixWord ++ tailWord_604213) baseStart_604213 baseEnd_604213 := by
    simpa [prefixWord, tailWord_604213, baseEnd_604213] using wordTrace_append hprefix tailTrace_604213
  have hstable : (prefixWord ++ tailWord_604213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604213).length < 2 ^ (prefixWord ++ tailWord_604213).sum := by decide
  have hdescent : baseEnd_604213 < baseStart_604213 := by decide
  rcases family_descends (prefixWord ++ tailWord_604213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604233 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 2, 2, 3]
def baseStart_604233 : Nat := 118140960795 + 604233 * 2 ^ 59
def prefixEnd_604233 : Nat := 4983230072969 + 3 ^ 40 * 604233 * 2
def baseEnd_604233 : Nat := 310261956308239669308689

theorem tailTrace_604233 : CollatzResearch.WordTrace tailWord_604233 prefixEnd_604233 310261956308239669308689 := by
  unfold tailWord_604233
  simp only [CollatzResearch.WordTrace]
  refine ⟨22038188019974510625753353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14692125346649673750502235 22038188019974510625753353)
  ·
    refine ⟨16528641014980882969315015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22038188019974510625753353 16528641014980882969315015)
    ·
      refine ⟨24792961522471324453972523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16528641014980882969315015 24792961522471324453972523)
      ·
        refine ⟨37189442283706986680958785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24792961522471324453972523 37189442283706986680958785)
        ·
          refine ⟨27892081712780240010719089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37189442283706986680958785 27892081712780240010719089)
          ·
            refine ⟨20919061284585180008039317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27892081712780240010719089 20919061284585180008039317)
            ·
              refine ⟨980580997714930312876843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20919061284585180008039317 980580997714930312876843)
              ·
                refine ⟨1470871496572395469315265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 980580997714930312876843 1470871496572395469315265)
                ·
                  refine ⟨1103153622429296601986449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1470871496572395469315265 1103153622429296601986449)
                  ·
                    refine ⟨827365216821972451489837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1103153622429296601986449 827365216821972451489837)
                    ·
                      refine ⟨310261956308239669308689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 827365216821972451489837 310261956308239669308689)
                      ·
                        rfl

theorem cell23_604233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 2, 3].length) (baseStart_604233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604233 prefixEnd_604233 := by exact prefixLift 604233
  have htrace : WordTrace (prefixWord ++ tailWord_604233) baseStart_604233 baseEnd_604233 := by
    simpa [prefixWord, tailWord_604233, baseEnd_604233] using wordTrace_append hprefix tailTrace_604233
  have hstable : (prefixWord ++ tailWord_604233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604233).length < 2 ^ (prefixWord ++ tailWord_604233).sum := by decide
  have hdescent : baseEnd_604233 < baseStart_604233 := by decide
  rcases family_descends (prefixWord ++ tailWord_604233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604273 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 1, 5, 2]
def baseStart_604273 : Nat := 118140960795 + 604273 * 2 ^ 59
def prefixEnd_604273 : Nat := 4983230072969 + 3 ^ 40 * 604273 * 2
def baseEnd_604273 : Nat := 310282495534419512808505

theorem tailTrace_604273 : CollatzResearch.WordTrace tailWord_604273 prefixEnd_604273 310282495534419512808505 := by
  unfold tailWord_604273
  simp only [CollatzResearch.WordTrace]
  refine ⟨22039646939829597457209473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14693097959886398304806315 22039646939829597457209473)
  ·
    refine ⟨16529735204872198092907105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22039646939829597457209473 16529735204872198092907105)
    ·
      refine ⟨12397301403654148569680329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16529735204872198092907105 12397301403654148569680329)
      ·
        refine ⟨9297976052740611427260247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12397301403654148569680329 9297976052740611427260247)
        ·
          refine ⟨13946964079110917140890371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9297976052740611427260247 13946964079110917140890371)
          ·
            refine ⟨20920446118666375711335557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13946964079110917140890371 20920446118666375711335557)
            ·
              refine ⟨3922583647249945445875417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20920446118666375711335557 3922583647249945445875417)
              ·
                refine ⟨2941937735437459084406563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3922583647249945445875417 2941937735437459084406563)
                ·
                  refine ⟨4412906603156188626609845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2941937735437459084406563 4412906603156188626609845)
                  ·
                    refine ⟨413709994045892683744673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4412906603156188626609845 413709994045892683744673)
                    ·
                      refine ⟨310282495534419512808505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 413709994045892683744673 310282495534419512808505)
                      ·
                        rfl

theorem cell23_604273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_604273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604273 prefixEnd_604273 := by exact prefixLift 604273
  have htrace : WordTrace (prefixWord ++ tailWord_604273) baseStart_604273 baseEnd_604273 := by
    simpa [prefixWord, tailWord_604273, baseEnd_604273] using wordTrace_append hprefix tailTrace_604273
  have hstable : (prefixWord ++ tailWord_604273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604273).length < 2 ^ (prefixWord ++ tailWord_604273).sum := by decide
  have hdescent : baseEnd_604273 < baseStart_604273 := by decide
  rcases family_descends (prefixWord ++ tailWord_604273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604297 : List Nat := [1, 2, 1, 1, 4, 2, 4, 3, 1, 1, 3]
def baseStart_604297 : Nat := 118140960795 + 604297 * 2 ^ 59
def prefixEnd_604297 : Nat := 4983230072969 + 3 ^ 40 * 604297 * 2
def baseEnd_604297 : Nat := 310294819070127418908395

theorem tailTrace_604297 : CollatzResearch.WordTrace tailWord_604297 prefixEnd_604297 310294819070127418908395 := by
  unfold tailWord_604297
  simp only [CollatzResearch.WordTrace]
  refine ⟨22040522291742649556083145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14693681527828433037388763 22040522291742649556083145)
  ·
    refine ⟨16530391718806987167062359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22040522291742649556083145 16530391718806987167062359)
    ·
      refine ⟨24795587578210480750593539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16530391718806987167062359 24795587578210480750593539)
      ·
        refine ⟨37193381367315721125890309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24795587578210480750593539 37193381367315721125890309)
        ·
          refine ⟨6973759006371697711104433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37193381367315721125890309 6973759006371697711104433)
          ·
            refine ⟨5230319254778773283328325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6973759006371697711104433 5230319254778773283328325)
            ·
              refine ⟨980684860271019990624061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5230319254778773283328325 980684860271019990624061)
              ·
                refine ⟨367756822601632496484023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 980684860271019990624061 367756822601632496484023)
                ·
                  refine ⟨551635233902448744726035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367756822601632496484023 551635233902448744726035)
                  ·
                    refine ⟨827452850853673117089053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 551635233902448744726035 827452850853673117089053)
                    ·
                      refine ⟨310294819070127418908395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 827452850853673117089053 310294819070127418908395)
                      ·
                        rfl

theorem cell23_604297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 1, 1, 3].length) (baseStart_604297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604297 prefixEnd_604297 := by exact prefixLift 604297
  have htrace : WordTrace (prefixWord ++ tailWord_604297) baseStart_604297 baseEnd_604297 := by
    simpa [prefixWord, tailWord_604297, baseEnd_604297] using wordTrace_append hprefix tailTrace_604297
  have hstable : (prefixWord ++ tailWord_604297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604297).length < 2 ^ (prefixWord ++ tailWord_604297).sum := by decide
  have hdescent : baseEnd_604297 < baseStart_604297 := by decide
  rcases family_descends (prefixWord ++ tailWord_604297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604334 : List Nat := [4, 1, 4, 2, 1, 1, 2, 2, 1, 5]
def baseStart_604334 : Nat := 118140960795 + 604334 * 2 ^ 59
def prefixEnd_604334 : Nat := 4983230072969 + 3 ^ 40 * 604334 * 2
def baseEnd_604334 : Nat := 103437939284781258048575

theorem tailTrace_604334 : CollatzResearch.WordTrace tailWord_604334 prefixEnd_604334 103437939284781258048575 := by
  unfold tailWord_604334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2755233974076075609397507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14694581195072403250120037 2755233974076075609397507)
  ·
    refine ⟨4132850961114113414096261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2755233974076075609397507 4132850961114113414096261)
    ·
      refine ⟨774909555208896265143049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4132850961114113414096261 774909555208896265143049)
      ·
        refine ⟨581182166406672198857287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 774909555208896265143049 581182166406672198857287)
        ·
          refine ⟨871773249610008298285931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581182166406672198857287 871773249610008298285931)
          ·
            refine ⟨1307659874415012447428897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871773249610008298285931 1307659874415012447428897)
            ·
              refine ⟨980744905811259335571673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1307659874415012447428897 980744905811259335571673)
              ·
                refine ⟨735558679358444501678755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 980744905811259335571673 735558679358444501678755)
                ·
                  refine ⟨1103338019037666752518133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735558679358444501678755 1103338019037666752518133)
                  ·
                    refine ⟨103437939284781258048575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1103338019037666752518133 103437939284781258048575)
                    ·
                      rfl

theorem cell23_604334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_604334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604334 prefixEnd_604334 := by exact prefixLift 604334
  have htrace : WordTrace (prefixWord ++ tailWord_604334) baseStart_604334 baseEnd_604334 := by
    simpa [prefixWord, tailWord_604334, baseEnd_604334] using wordTrace_append hprefix tailTrace_604334
  have hstable : (prefixWord ++ tailWord_604334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604334).length < 2 ^ (prefixWord ++ tailWord_604334).sum := by decide
  have hdescent : baseEnd_604334 < baseStart_604334 := by decide
  rcases family_descends (prefixWord ++ tailWord_604334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604337 : List Nat := [1, 2, 2, 5, 2, 1, 2, 2, 1, 1, 4]
def baseStart_604337 : Nat := 118140960795 + 604337 * 2 ^ 59
def prefixEnd_604337 : Nat := 4983230072969 + 3 ^ 40 * 604337 * 2
def baseEnd_604337 : Nat := 310315358296307262408211

theorem tailTrace_604337 : CollatzResearch.WordTrace tailWord_604337 prefixEnd_604337 310315358296307262408211 := by
  unfold tailWord_604337
  simp only [CollatzResearch.WordTrace]
  refine ⟨22041981211597736387539265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14694654141065157591692843 22041981211597736387539265)
  ·
    refine ⟨16531485908698302290654449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22041981211597736387539265 16531485908698302290654449)
    ·
      refine ⟨12398614431523726717990837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16531485908698302290654449 12398614431523726717990837)
      ·
        refine ⟨1162370102955349379811641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12398614431523726717990837 1162370102955349379811641)
        ·
          refine ⟨871777577216512034858731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1162370102955349379811641 871777577216512034858731)
          ·
            refine ⟨1307666365824768052288097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871777577216512034858731 1307666365824768052288097)
            ·
              refine ⟨980749774368576039216073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1307666365824768052288097 980749774368576039216073)
              ·
                refine ⟨735562330776432029412055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 980749774368576039216073 735562330776432029412055)
                ·
                  refine ⟨1103343496164648044118083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735562330776432029412055 1103343496164648044118083)
                  ·
                    refine ⟨1655015244246972066177125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1103343496164648044118083 1655015244246972066177125)
                    ·
                      refine ⟨310315358296307262408211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1655015244246972066177125 310315358296307262408211)
                      ·
                        rfl

theorem cell23_604337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_604337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604337 prefixEnd_604337 := by exact prefixLift 604337
  have htrace : WordTrace (prefixWord ++ tailWord_604337) baseStart_604337 baseEnd_604337 := by
    simpa [prefixWord, tailWord_604337, baseEnd_604337] using wordTrace_append hprefix tailTrace_604337
  have hstable : (prefixWord ++ tailWord_604337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604337).length < 2 ^ (prefixWord ++ tailWord_604337).sum := by decide
  have hdescent : baseEnd_604337 < baseStart_604337 := by decide
  rcases family_descends (prefixWord ++ tailWord_604337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604343 : List Nat := [1, 1, 3, 1, 4, 2, 4, 7]
def baseStart_604343 : Nat := 118140960795 + 604343 * 2 ^ 59
def prefixEnd_604343 : Nat := 4983230072969 + 3 ^ 40 * 604343 * 2
def baseEnd_604343 : Nat := 11493275525193860701229

theorem tailTrace_604343 : CollatzResearch.WordTrace tailWord_604343 prefixEnd_604343 11493275525193860701229 := by
  unfold tailWord_604343
  simp only [CollatzResearch.WordTrace]
  refine ⟨22042200049575999412257683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14694800033050666274838455 22042200049575999412257683)
  ·
    refine ⟨33063300074363999118386525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22042200049575999412257683 33063300074363999118386525)
    ·
      refine ⟨12398737527886499669394947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33063300074363999118386525 12398737527886499669394947)
      ·
        refine ⟨18598106291829749504092421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12398737527886499669394947 18598106291829749504092421)
        ·
          refine ⟨3487144929718078032017329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18598106291829749504092421 3487144929718078032017329)
          ·
            refine ⟨2615358697288558524012997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3487144929718078032017329 2615358697288558524012997)
            ·
              refine ⟨490379755741604723252437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2615358697288558524012997 490379755741604723252437)
              ·
                refine ⟨11493275525193860701229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 490379755741604723252437 11493275525193860701229)
                ·
                  rfl

theorem cell23_604343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 7].length) (baseStart_604343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604343 prefixEnd_604343 := by exact prefixLift 604343
  have htrace : WordTrace (prefixWord ++ tailWord_604343) baseStart_604343 baseEnd_604343 := by
    simpa [prefixWord, tailWord_604343, baseEnd_604343] using wordTrace_append hprefix tailTrace_604343
  have hstable : (prefixWord ++ tailWord_604343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604343).length < 2 ^ (prefixWord ++ tailWord_604343).sum := by decide
  have hdescent : baseEnd_604343 < baseStart_604343 := by decide
  rcases family_descends (prefixWord ++ tailWord_604343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604354 : List Nat := [3, 5, 1, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_604354 : Nat := 118140960795 + 604354 * 2 ^ 59
def prefixEnd_604354 : Nat := 4983230072969 + 3 ^ 40 * 604354 * 2
def baseEnd_604354 : Nat := 310324087467433695895633

theorem tailTrace_604354 : CollatzResearch.WordTrace tailWord_604354 prefixEnd_604354 310324087467433695895633 := by
  unfold tailWord_604354
  simp only [CollatzResearch.WordTrace]
  refine ⟨5510650313134037072727029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14695067501690765527272077 5510650313134037072727029)
  ·
    refine ⟨516623466856315975568159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5510650313134037072727029 516623466856315975568159)
    ·
      refine ⟨774935200284473963352239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 516623466856315975568159 774935200284473963352239)
      ·
        refine ⟨1162402800426710945028359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774935200284473963352239 1162402800426710945028359)
        ·
          refine ⟨1743604200640066417542539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162402800426710945028359 1743604200640066417542539)
          ·
            refine ⟨2615406300960099626313809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1743604200640066417542539 2615406300960099626313809)
            ·
              refine ⟨1961554725720074719735357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2615406300960099626313809 1961554725720074719735357)
              ·
                refine ⟨735583022145028019900759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1961554725720074719735357 735583022145028019900759)
                ·
                  refine ⟨1103374533217542029851139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735583022145028019900759 1103374533217542029851139)
                  ·
                    refine ⟨1655061799826313044776709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1103374533217542029851139 1655061799826313044776709)
                    ·
                      refine ⟨310324087467433695895633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1655061799826313044776709 310324087467433695895633)
                      ·
                        rfl

theorem cell23_604354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_604354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604354 prefixEnd_604354 := by exact prefixLift 604354
  have htrace : WordTrace (prefixWord ++ tailWord_604354) baseStart_604354 baseEnd_604354 := by
    simpa [prefixWord, tailWord_604354, baseEnd_604354] using wordTrace_append hprefix tailTrace_604354
  have hstable : (prefixWord ++ tailWord_604354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604354).length < 2 ^ (prefixWord ++ tailWord_604354).sum := by decide
  have hdescent : baseEnd_604354 < baseStart_604354 := by decide
  rcases family_descends (prefixWord ++ tailWord_604354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604410 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2]
def baseStart_604410 : Nat := 118140960795 + 604410 * 2 ^ 59
def prefixEnd_604410 : Nat := 4983230072969 + 3 ^ 40 * 604410 * 2
def baseEnd_604410 : Nat := 310352842384085476795375

theorem tailTrace_604410 : CollatzResearch.WordTrace tailWord_604410 prefixEnd_604410 310352842384085476795375 := by
  unfold tailWord_604410
  simp only [CollatzResearch.WordTrace]
  refine ⟨5511160935083317463736671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14696429160222179903297789 5511160935083317463736671)
  ·
    refine ⟨8266741402624976195605007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5511160935083317463736671 8266741402624976195605007)
    ·
      refine ⟨12400112103937464293407511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8266741402624976195605007 12400112103937464293407511)
      ·
        refine ⟨18600168155906196440111267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12400112103937464293407511 18600168155906196440111267)
        ·
          refine ⟨27900252233859294660166901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18600168155906196440111267 27900252233859294660166901)
          ·
            refine ⟨2615648646924308874390647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27900252233859294660166901 2615648646924308874390647)
            ·
              refine ⟨3923472970386463311585971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2615648646924308874390647 3923472970386463311585971)
              ·
                refine ⟨5885209455579694967378957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3923472970386463311585971 5885209455579694967378957)
                ·
                  refine ⟨2206953545842385612767109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5885209455579694967378957 2206953545842385612767109)
                  ·
                    refine ⟨413803789845447302393833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2206953545842385612767109 413803789845447302393833)
                    ·
                      refine ⟨310352842384085476795375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 413803789845447302393833 310352842384085476795375)
                      ·
                        rfl

theorem cell23_604410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2].length) (baseStart_604410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604410 prefixEnd_604410 := by exact prefixLift 604410
  have htrace : WordTrace (prefixWord ++ tailWord_604410) baseStart_604410 baseEnd_604410 := by
    simpa [prefixWord, tailWord_604410, baseEnd_604410] using wordTrace_append hprefix tailTrace_604410
  have hstable : (prefixWord ++ tailWord_604410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604410).length < 2 ^ (prefixWord ++ tailWord_604410).sum := by decide
  have hdescent : baseEnd_604410 < baseStart_604410 := by decide
  rcases family_descends (prefixWord ++ tailWord_604410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604413 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 4, 4, 3]
def baseStart_604413 : Nat := 118140960795 + 604413 * 2 ^ 59
def prefixEnd_604413 : Nat := 4983230072969 + 3 ^ 40 * 604413 * 2
def baseEnd_604413 : Nat := 310354382826048965057861

theorem tailTrace_604413 : CollatzResearch.WordTrace tailWord_604413 prefixEnd_604413 310354382826048965057861 := by
  unfold tailWord_604413
  simp only [CollatzResearch.WordTrace]
  refine ⟨22044753159322401367305893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14696502106214934244870595 22044753159322401367305893)
  ·
    refine ⟨4133391217372950256369855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22044753159322401367305893 4133391217372950256369855)
    ·
      refine ⟨6200086826059425384554783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4133391217372950256369855 6200086826059425384554783)
      ·
        refine ⟨9300130239089138076832175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6200086826059425384554783 9300130239089138076832175)
        ·
          refine ⟨13950195358633707115248263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9300130239089138076832175 13950195358633707115248263)
          ·
            refine ⟨20925293037950560672872395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13950195358633707115248263 20925293037950560672872395)
            ·
              refine ⟨31387939556925841009308593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20925293037950560672872395 31387939556925841009308593)
              ·
                refine ⟨23540954667694380756981445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31387939556925841009308593 23540954667694380756981445)
                ·
                  refine ⟨4413929000192696391934021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23540954667694380756981445 4413929000192696391934021)
                  ·
                    refine ⟨827611687536130573487629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4413929000192696391934021 827611687536130573487629)
                    ·
                      refine ⟨310354382826048965057861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 827611687536130573487629 310354382826048965057861)
                      ·
                        rfl

theorem cell23_604413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_604413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604413 prefixEnd_604413 := by exact prefixLift 604413
  have htrace : WordTrace (prefixWord ++ tailWord_604413) baseStart_604413 baseEnd_604413 := by
    simpa [prefixWord, tailWord_604413, baseEnd_604413] using wordTrace_append hprefix tailTrace_604413
  have hstable : (prefixWord ++ tailWord_604413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604413).length < 2 ^ (prefixWord ++ tailWord_604413).sum := by decide
  have hdescent : baseEnd_604413 < baseStart_604413 := by decide
  rcases family_descends (prefixWord ++ tailWord_604413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604443 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 3]
def baseStart_604443 : Nat := 118140960795 + 604443 * 2 ^ 59
def prefixEnd_604443 : Nat := 4983230072969 + 3 ^ 40 * 604443 * 2
def baseEnd_604443 : Nat := 310369787245683847682723

theorem tailTrace_604443 : CollatzResearch.WordTrace tailWord_604443 prefixEnd_604443 310369787245683847682723 := by
  unfold tailWord_604443
  simp only [CollatzResearch.WordTrace]
  refine ⟨22045847349213716490897983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14697231566142477660598655 22045847349213716490897983)
  ·
    refine ⟨33068771023820574736346975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22045847349213716490897983 33068771023820574736346975)
    ·
      refine ⟨49603156535730862104520463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33068771023820574736346975 49603156535730862104520463)
      ·
        refine ⟨74404734803596293156780695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49603156535730862104520463 74404734803596293156780695)
        ·
          refine ⟨111607102205394439735171043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74404734803596293156780695 111607102205394439735171043)
          ·
            refine ⟨167410653308091659602756565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111607102205394439735171043 167410653308091659602756565)
            ·
              refine ⟨3923687186908398271939607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 167410653308091659602756565 3923687186908398271939607)
              ·
                refine ⟨5885530780362597407909411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3923687186908398271939607 5885530780362597407909411)
                ·
                  refine ⟨8828296170543896111864117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5885530780362597407909411 8828296170543896111864117)
                  ·
                    refine ⟨827652765988490260487261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8828296170543896111864117 827652765988490260487261)
                    ·
                      refine ⟨310369787245683847682723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 827652765988490260487261 310369787245683847682723)
                      ·
                        rfl

theorem cell23_604443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 3].length) (baseStart_604443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604443 prefixEnd_604443 := by exact prefixLift 604443
  have htrace : WordTrace (prefixWord ++ tailWord_604443) baseStart_604443 baseEnd_604443 := by
    simpa [prefixWord, tailWord_604443, baseEnd_604443] using wordTrace_append hprefix tailTrace_604443
  have hstable : (prefixWord ++ tailWord_604443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604443).length < 2 ^ (prefixWord ++ tailWord_604443).sum := by decide
  have hdescent : baseEnd_604443 < baseStart_604443 := by decide
  rcases family_descends (prefixWord ++ tailWord_604443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604450 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 7]
def baseStart_604450 : Nat := 118140960795 + 604450 * 2 ^ 59
def prefixEnd_604450 : Nat := 4983230072969 + 3 ^ 40 * 604450 * 2
def baseEnd_604450 : Nat := 34485931290029480032799

theorem tailTrace_604450 : CollatzResearch.WordTrace tailWord_604450 prefixEnd_604450 34485931290029480032799 := by
  unfold tailWord_604450
  simp only [CollatzResearch.WordTrace]
  refine ⟨5511525665047089171600701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14697401773458904457601869 5511525665047089171600701)
  ·
    refine ⟨2066822124392658439350263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5511525665047089171600701 2066822124392658439350263)
    ·
      refine ⟨3100233186588987659025395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2066822124392658439350263 3100233186588987659025395)
      ·
        refine ⟨4650349779883481488538093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3100233186588987659025395 4650349779883481488538093)
        ·
          refine ⟨1743881167456305558201785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4650349779883481488538093 1743881167456305558201785)
          ·
            refine ⟨1307910875592229168651339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1743881167456305558201785 1307910875592229168651339)
            ·
              refine ⟨1961866313388343752977009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307910875592229168651339 1961866313388343752977009)
              ·
                refine ⟨1471399735041257814732757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1961866313388343752977009 1471399735041257814732757)
                ·
                  refine ⟨34485931290029480032799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1471399735041257814732757 34485931290029480032799)
                  ·
                    rfl

theorem cell23_604450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_604450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604450 prefixEnd_604450 := by exact prefixLift 604450
  have htrace : WordTrace (prefixWord ++ tailWord_604450) baseStart_604450 baseEnd_604450 := by
    simpa [prefixWord, tailWord_604450, baseEnd_604450] using wordTrace_append hprefix tailTrace_604450
  have hstable : (prefixWord ++ tailWord_604450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604450).length < 2 ^ (prefixWord ++ tailWord_604450).sum := by decide
  have hdescent : baseEnd_604450 < baseStart_604450 := by decide
  rcases family_descends (prefixWord ++ tailWord_604450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604500 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_604500 : Nat := 118140960795 + 604500 * 2 ^ 59
def prefixEnd_604500 : Nat := 4983230072969 + 3 ^ 40 * 604500 * 2
def baseEnd_604500 : Nat := 310399055642990124669961

theorem tailTrace_604500 : CollatzResearch.WordTrace tailWord_604500 prefixEnd_604500 310399055642990124669961 := by
  unfold tailWord_604500
  simp only [CollatzResearch.WordTrace]
  refine ⟨11023963155003607612861477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14698617540004810150481969 11023963155003607612861477)
  ·
    refine ⟨2066993091563176427411527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11023963155003607612861477 2066993091563176427411527)
    ·
      refine ⟨3100489637344764641117291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2066993091563176427411527 3100489637344764641117291)
      ·
        refine ⟨4650734456017146961675937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3100489637344764641117291 4650734456017146961675937)
        ·
          refine ⟨3488050842012860221256953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4650734456017146961675937 3488050842012860221256953)
          ·
            refine ⟨2616038131509645165942715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3488050842012860221256953 2616038131509645165942715)
            ·
              refine ⟨3924057197264467748914073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2616038131509645165942715 3924057197264467748914073)
              ·
                refine ⟨2943042897948350811685555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3924057197264467748914073 2943042897948350811685555)
                ·
                  refine ⟨4414564346922526217528333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2943042897948350811685555 4414564346922526217528333)
                  ·
                    refine ⟨1655461630095947331573125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4414564346922526217528333 1655461630095947331573125)
                    ·
                      refine ⟨310399055642990124669961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1655461630095947331573125 310399055642990124669961)
                      ·
                        rfl

theorem cell23_604500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_604500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604500 prefixEnd_604500 := by exact prefixLift 604500
  have htrace : WordTrace (prefixWord ++ tailWord_604500) baseStart_604500 baseEnd_604500 := by
    simpa [prefixWord, tailWord_604500, baseEnd_604500] using wordTrace_append hprefix tailTrace_604500
  have hstable : (prefixWord ++ tailWord_604500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604500).length < 2 ^ (prefixWord ++ tailWord_604500).sum := by decide
  have hdescent : baseEnd_604500 < baseStart_604500 := by decide
  rcases family_descends (prefixWord ++ tailWord_604500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604527 : List Nat := [1, 1, 2, 1, 3, 1, 2, 7, 1, 4]
def baseStart_604527 : Nat := 118140960795 + 604527 * 2 ^ 59
def prefixEnd_604527 : Nat := 4983230072969 + 3 ^ 40 * 604527 * 2
def baseEnd_604527 : Nat := 103470973206887173010779

theorem tailTrace_604527 : CollatzResearch.WordTrace tailWord_604527 prefixEnd_604527 103470973206887173010779 := by
  unfold tailWord_604527
  simp only [CollatzResearch.WordTrace]
  refine ⟨22048911080909398836955835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14699274053939599224637223 22048911080909398836955835)
  ·
    refine ⟨33073366621364098255433753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22048911080909398836955835 33073366621364098255433753)
    ·
      refine ⟨24805024966023073691575315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33073366621364098255433753 24805024966023073691575315)
      ·
        refine ⟨37207537449034610537362973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24805024966023073691575315 37207537449034610537362973)
        ·
          refine ⟨13952826543387978951511115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37207537449034610537362973 13952826543387978951511115)
          ·
            refine ⟨20929239815081968427266673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13952826543387978951511115 20929239815081968427266673)
            ·
              refine ⟨15696929861311476320450005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20929239815081968427266673 15696929861311476320450005)
              ·
                refine ⟨367896793624487726260547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15696929861311476320450005 367896793624487726260547)
                ·
                  refine ⟨551845190436731589390821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367896793624487726260547 551845190436731589390821)
                  ·
                    refine ⟨103470973206887173010779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 551845190436731589390821 103470973206887173010779)
                    ·
                      rfl

theorem cell23_604527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 1, 4].length) (baseStart_604527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604527 prefixEnd_604527 := by exact prefixLift 604527
  have htrace : WordTrace (prefixWord ++ tailWord_604527) baseStart_604527 baseEnd_604527 := by
    simpa [prefixWord, tailWord_604527, baseEnd_604527] using wordTrace_append hprefix tailTrace_604527
  have hstable : (prefixWord ++ tailWord_604527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604527).length < 2 ^ (prefixWord ++ tailWord_604527).sum := by decide
  have hdescent : baseEnd_604527 < baseStart_604527 := by decide
  rcases family_descends (prefixWord ++ tailWord_604527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604567 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 3, 1, 3]
def baseStart_604567 : Nat := 118140960795 + 604567 * 2 ^ 59
def prefixEnd_604567 : Nat := 4983230072969 + 3 ^ 40 * 604567 * 2
def baseEnd_604567 : Nat := 310433458846841362532153

theorem tailTrace_604567 : CollatzResearch.WordTrace tailWord_604567 prefixEnd_604567 310433458846841362532153 := by
  unfold tailWord_604567
  simp only [CollatzResearch.WordTrace]
  refine ⟨22050370000764485668411955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14700246667176323778941303 22050370000764485668411955)
  ·
    refine ⟨33075555001146728502617933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22050370000764485668411955 33075555001146728502617933)
    ·
      refine ⟨12403333125430023188481725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33075555001146728502617933 12403333125430023188481725)
      ·
        refine ⟨4651249922036258695680647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12403333125430023188481725 4651249922036258695680647)
        ·
          refine ⟨6976874883054388043520971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4651249922036258695680647 6976874883054388043520971)
          ·
            refine ⟨10465312324581582065281457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6976874883054388043520971 10465312324581582065281457)
            ·
              refine ⟨7848984243436186548961093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10465312324581582065281457 7848984243436186548961093)
              ·
                refine ⟨1471684545644284977930205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7848984243436186548961093 1471684545644284977930205)
                ·
                  refine ⟨551881704616606866723827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1471684545644284977930205 551881704616606866723827)
                  ·
                    refine ⟨827822556924910300085741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 551881704616606866723827 827822556924910300085741)
                    ·
                      refine ⟨310433458846841362532153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 827822556924910300085741 310433458846841362532153)
                      ·
                        rfl

theorem cell23_604567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_604567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604567 prefixEnd_604567 := by exact prefixLift 604567
  have htrace : WordTrace (prefixWord ++ tailWord_604567) baseStart_604567 baseEnd_604567 := by
    simpa [prefixWord, tailWord_604567, baseEnd_604567] using wordTrace_append hprefix tailTrace_604567
  have hstable : (prefixWord ++ tailWord_604567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604567).length < 2 ^ (prefixWord ++ tailWord_604567).sum := by decide
  have hdescent : baseEnd_604567 < baseStart_604567 := by decide
  rcases family_descends (prefixWord ++ tailWord_604567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604601 : List Nat := [1, 2, 1, 4, 3, 2, 1, 4, 1, 1, 3]
def baseStart_604601 : Nat := 118140960795 + 604601 * 2 ^ 59
def prefixEnd_604601 : Nat := 4983230072969 + 3 ^ 40 * 604601 * 2
def baseEnd_604601 : Nat := 310450917189094229506997

theorem tailTrace_604601 : CollatzResearch.WordTrace tailWord_604601 prefixEnd_604601 310450917189094229506997 := by
  unfold tailWord_604601
  simp only [CollatzResearch.WordTrace]
  refine ⟨22051610082641309475149657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14701073388427539650099771 22051610082641309475149657)
  ·
    refine ⟨16538707561980982106362243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22051610082641309475149657 16538707561980982106362243)
    ·
      refine ⟨24808061342971473159543365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16538707561980982106362243 24808061342971473159543365)
      ·
        refine ⟨4651511501807151217414381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24808061342971473159543365 4651511501807151217414381)
        ·
          refine ⟨1744316813177681706530393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4651511501807151217414381 1744316813177681706530393)
          ·
            refine ⟨1308237609883261279897795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1744316813177681706530393 1308237609883261279897795)
            ·
              refine ⟨1962356414824891919846693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1308237609883261279897795 1962356414824891919846693)
              ·
                refine ⟨367941827779667234971255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1962356414824891919846693 367941827779667234971255)
                ·
                  refine ⟨551912741669500852456883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367941827779667234971255 551912741669500852456883)
                  ·
                    refine ⟨827869112504251278685325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 551912741669500852456883 827869112504251278685325)
                    ·
                      refine ⟨310450917189094229506997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 827869112504251278685325 310450917189094229506997)
                      ·
                        rfl

theorem cell23_604601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_604601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604601 prefixEnd_604601 := by exact prefixLift 604601
  have htrace : WordTrace (prefixWord ++ tailWord_604601) baseStart_604601 baseEnd_604601 := by
    simpa [prefixWord, tailWord_604601, baseEnd_604601] using wordTrace_append hprefix tailTrace_604601
  have hstable : (prefixWord ++ tailWord_604601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604601).length < 2 ^ (prefixWord ++ tailWord_604601).sum := by decide
  have hdescent : baseEnd_604601 < baseStart_604601 := by decide
  rcases family_descends (prefixWord ++ tailWord_604601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604617 : List Nat := [1, 2, 1, 1, 2, 1, 6, 3, 2, 4]
def baseStart_604617 : Nat := 118140960795 + 604617 * 2 ^ 59
def prefixEnd_604617 : Nat := 4983230072969 + 3 ^ 40 * 604617 * 2
def baseEnd_604617 : Nat := 103486377626522055635641

theorem tailTrace_604617 : CollatzResearch.WordTrace tailWord_604617 prefixEnd_604617 103486377626522055635641 := by
  unfold tailWord_604617
  simp only [CollatzResearch.WordTrace]
  refine ⟨22052193650583344207732105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14701462433722229471821403 22052193650583344207732105)
  ·
    refine ⟨16539145237937508155799079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22052193650583344207732105 16539145237937508155799079)
    ·
      refine ⟨24808717856906262233698619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16539145237937508155799079 24808717856906262233698619)
      ·
        refine ⟨37213076785359393350547929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24808717856906262233698619 37213076785359393350547929)
        ·
          refine ⟨27909807589019545012910947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37213076785359393350547929 27909807589019545012910947)
          ·
            refine ⟨41864711383529317519366421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27909807589019545012910947 41864711383529317519366421)
            ·
              refine ⟨1962408346102936758720301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41864711383529317519366421 1962408346102936758720301)
              ·
                refine ⟨735903129788601284520113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1962408346102936758720301 735903129788601284520113)
                ·
                  refine ⟨551927347341450963390085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 735903129788601284520113 551927347341450963390085)
                  ·
                    refine ⟨103486377626522055635641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 551927347341450963390085 103486377626522055635641)
                    ·
                      rfl

theorem cell23_604617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 4].length) (baseStart_604617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604617 prefixEnd_604617 := by exact prefixLift 604617
  have htrace : WordTrace (prefixWord ++ tailWord_604617) baseStart_604617 baseEnd_604617 := by
    simpa [prefixWord, tailWord_604617, baseEnd_604617] using wordTrace_append hprefix tailTrace_604617
  have hstable : (prefixWord ++ tailWord_604617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604617).length < 2 ^ (prefixWord ++ tailWord_604617).sum := by decide
  have hdescent : baseEnd_604617 < baseStart_604617 := by decide
  rcases family_descends (prefixWord ++ tailWord_604617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604637 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_604637 : Nat := 118140960795 + 604637 * 2 ^ 59
def prefixEnd_604637 : Nat := 4983230072969 + 3 ^ 40 * 604637 * 2
def baseEnd_604637 : Nat := 310469402492656088656831

theorem tailTrace_604637 : CollatzResearch.WordTrace tailWord_604637 prefixEnd_604637 310469402492656088656831 := by
  unfold tailWord_604637
  simp only [CollatzResearch.WordTrace]
  refine ⟨22052923110510887623460165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14701948740340591748973443 22052923110510887623460165)
  ·
    refine ⟨4134923083220791429398781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22052923110510887623460165 4134923083220791429398781)
    ·
      refine ⟨1550596156207796786024543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4134923083220791429398781 1550596156207796786024543)
      ·
        refine ⟨2325894234311695179036815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550596156207796786024543 2325894234311695179036815)
        ·
          refine ⟨3488841351467542768555223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2325894234311695179036815 3488841351467542768555223)
          ·
            refine ⟨5233262027201314152832835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3488841351467542768555223 5233262027201314152832835)
            ·
              refine ⟨7849893040801971229249253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5233262027201314152832835 7849893040801971229249253)
              ·
                refine ⟨1471854945150369605484235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7849893040801971229249253 1471854945150369605484235)
                ·
                  refine ⟨2207782417725554408226353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471854945150369605484235 2207782417725554408226353)
                  ·
                    refine ⟨1655836813294165806169765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2207782417725554408226353 1655836813294165806169765)
                    ·
                      refine ⟨310469402492656088656831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1655836813294165806169765 310469402492656088656831)
                      ·
                        rfl

theorem cell23_604637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_604637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604637 prefixEnd_604637 := by exact prefixLift 604637
  have htrace : WordTrace (prefixWord ++ tailWord_604637) baseStart_604637 baseEnd_604637 := by
    simpa [prefixWord, tailWord_604637, baseEnd_604637] using wordTrace_append hprefix tailTrace_604637
  have hstable : (prefixWord ++ tailWord_604637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604637).length < 2 ^ (prefixWord ++ tailWord_604637).sum := by decide
  have hdescent : baseEnd_604637 < baseStart_604637 := by decide
  rcases family_descends (prefixWord ++ tailWord_604637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604658 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 3, 2, 2]
def baseStart_604658 : Nat := 118140960795 + 604658 * 2 ^ 59
def prefixEnd_604658 : Nat := 4983230072969 + 3 ^ 40 * 604658 * 2
def baseEnd_604658 : Nat := 310480185586400506494235

theorem tailTrace_604658 : CollatzResearch.WordTrace tailWord_604658 prefixEnd_604658 310480185586400506494235 := by
  unfold tailWord_604658
  simp only [CollatzResearch.WordTrace]
  refine ⟨5513422260858702052493657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14702459362289872139983085 5513422260858702052493657)
  ·
    refine ⟨4135066695644026539370243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5513422260858702052493657 4135066695644026539370243)
    ·
      refine ⟨6202600043466039809055365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4135066695644026539370243 6202600043466039809055365)
      ·
        refine ⟨1162987508149882464197881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6202600043466039809055365 1162987508149882464197881)
        ·
          refine ⟨872240631112411848148411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1162987508149882464197881 872240631112411848148411)
          ·
            refine ⟨1308360946668617772222617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872240631112411848148411 1308360946668617772222617)
            ·
              refine ⟨981270710001463329166963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1308360946668617772222617 981270710001463329166963)
              ·
                refine ⟨1471906065002194993750445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981270710001463329166963 1471906065002194993750445)
                ·
                  refine ⟨551964774375823122656417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1471906065002194993750445 551964774375823122656417)
                  ·
                    refine ⟨413973580781867341992313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 551964774375823122656417 413973580781867341992313)
                    ·
                      refine ⟨310480185586400506494235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 413973580781867341992313 310480185586400506494235)
                      ·
                        rfl

theorem cell23_604658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_604658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604658 prefixEnd_604658 := by exact prefixLift 604658
  have htrace : WordTrace (prefixWord ++ tailWord_604658) baseStart_604658 baseEnd_604658 := by
    simpa [prefixWord, tailWord_604658, baseEnd_604658] using wordTrace_append hprefix tailTrace_604658
  have hstable : (prefixWord ++ tailWord_604658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604658).length < 2 ^ (prefixWord ++ tailWord_604658).sum := by decide
  have hdescent : baseEnd_604658 < baseStart_604658 := by decide
  rcases family_descends (prefixWord ++ tailWord_604658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604692 : List Nat := [2, 4, 3, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_604692 : Nat := 118140960795 + 604692 * 2 ^ 59
def prefixEnd_604692 : Nat := 4983230072969 + 3 ^ 40 * 604692 * 2
def baseEnd_604692 : Nat := 310497643928653373469079

theorem tailTrace_604692 : CollatzResearch.WordTrace tailWord_604692 prefixEnd_604692 310497643928653373469079 := by
  unfold tailWord_604692
  simp only [CollatzResearch.WordTrace]
  refine ⟨11027464562655816008356165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14703286083541088011141553 11027464562655816008356165)
  ·
    refine ⟨2067649605497965501566781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11027464562655816008356165 2067649605497965501566781)
    ·
      refine ⟨775368602061737063087543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2067649605497965501566781 775368602061737063087543)
      ·
        refine ⟨1163052903092605594631315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 775368602061737063087543 1163052903092605594631315)
        ·
          refine ⟨1744579354638908391946973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1163052903092605594631315 1744579354638908391946973)
          ·
            refine ⟨654217257989590646980115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1744579354638908391946973 654217257989590646980115)
            ·
              refine ⟨981325886984385970470173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654217257989590646980115 981325886984385970470173)
              ·
                refine ⟨367997207619144738926315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 981325886984385970470173 367997207619144738926315)
                ·
                  refine ⟨551995811428717108389473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367997207619144738926315 551995811428717108389473)
                  ·
                    refine ⟨413996858571537831292105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 551995811428717108389473 413996858571537831292105)
                    ·
                      refine ⟨310497643928653373469079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 413996858571537831292105 310497643928653373469079)
                      ·
                        rfl

theorem cell23_604692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_604692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604692 prefixEnd_604692 := by exact prefixLift 604692
  have htrace : WordTrace (prefixWord ++ tailWord_604692) baseStart_604692 baseEnd_604692 := by
    simpa [prefixWord, tailWord_604692, baseEnd_604692] using wordTrace_append hprefix tailTrace_604692
  have hstable : (prefixWord ++ tailWord_604692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604692).length < 2 ^ (prefixWord ++ tailWord_604692).sum := by decide
  have hdescent : baseEnd_604692 < baseStart_604692 := by decide
  rcases family_descends (prefixWord ++ tailWord_604692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604701 : List Nat := [1, 4, 2, 2, 1, 2, 2, 3, 1, 3, 2]
def baseStart_604701 : Nat := 118140960795 + 604701 * 2 ^ 59
def prefixEnd_604701 : Nat := 4983230072969 + 3 ^ 40 * 604701 * 2
def baseEnd_604701 : Nat := 310502265254543838256537

theorem tailTrace_604701 : CollatzResearch.WordTrace tailWord_604701 prefixEnd_604701 310502265254543838256537 := by
  unfold tailWord_604701
  simp only [CollatzResearch.WordTrace]
  refine ⟨22055257382279026553789957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14703504921519351035859971 22055257382279026553789957)
  ·
    refine ⟨4135360759177317478835617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22055257382279026553789957 4135360759177317478835617)
    ·
      refine ⟨3101520569382988109126713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4135360759177317478835617 3101520569382988109126713)
      ·
        refine ⟨2326140427037241081845035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3101520569382988109126713 2326140427037241081845035)
        ·
          refine ⟨3489210640555861622767553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326140427037241081845035 3489210640555861622767553)
          ·
            refine ⟨2616907980416896217075665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3489210640555861622767553 2616907980416896217075665)
            ·
              refine ⟨1962680985312672162806749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2616907980416896217075665 1962680985312672162806749)
              ·
                refine ⟨736005369492252061052531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1962680985312672162806749 736005369492252061052531)
                ·
                  refine ⟨1104008054238378091578797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 736005369492252061052531 1104008054238378091578797)
                  ·
                    refine ⟨414003020339391784342049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1104008054238378091578797 414003020339391784342049)
                    ·
                      refine ⟨310502265254543838256537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 414003020339391784342049 310502265254543838256537)
                      ·
                        rfl

theorem cell23_604701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_604701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604701 prefixEnd_604701 := by exact prefixLift 604701
  have htrace : WordTrace (prefixWord ++ tailWord_604701) baseStart_604701 baseEnd_604701 := by
    simpa [prefixWord, tailWord_604701, baseEnd_604701] using wordTrace_append hprefix tailTrace_604701
  have hstable : (prefixWord ++ tailWord_604701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604701).length < 2 ^ (prefixWord ++ tailWord_604701).sum := by decide
  have hdescent : baseEnd_604701 < baseStart_604701 := by decide
  rcases family_descends (prefixWord ++ tailWord_604701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604754 : List Nat := [3, 2, 2, 1, 2, 1, 2, 5, 5]
def baseStart_604754 : Nat := 118140960795 + 604754 * 2 ^ 59
def prefixEnd_604754 : Nat := 4983230072969 + 3 ^ 40 * 604754 * 2
def baseEnd_604754 : Nat := 34503275525470236765977

theorem tailTrace_604754 : CollatzResearch.WordTrace tailWord_604754 prefixEnd_604754 34503275525470236765977 := by
  unfold tailWord_604754
  simp only [CollatzResearch.WordTrace]
  refine ⟨5514297612771754151367329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14704793634058011070312877 5514297612771754151367329)
  ·
    refine ⟨4135723209578815613525497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5514297612771754151367329 4135723209578815613525497)
    ·
      refine ⟨3101792407184111710144123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4135723209578815613525497 3101792407184111710144123)
      ·
        refine ⟨4652688610776167565216185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3101792407184111710144123 4652688610776167565216185)
        ·
          refine ⟨3489516458082125673912139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4652688610776167565216185 3489516458082125673912139)
          ·
            refine ⟨5234274687123188510868209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3489516458082125673912139 5234274687123188510868209)
            ·
              refine ⟨3925706015342391383151157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5234274687123188510868209 3925706015342391383151157)
              ·
                refine ⟨368034938938349192170421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3925706015342391383151157 368034938938349192170421)
                ·
                  refine ⟨34503275525470236765977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 368034938938349192170421 34503275525470236765977)
                  ·
                    rfl

theorem cell23_604754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_604754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604754 prefixEnd_604754 := by exact prefixLift 604754
  have htrace : WordTrace (prefixWord ++ tailWord_604754) baseStart_604754 baseEnd_604754 := by
    simpa [prefixWord, tailWord_604754, baseEnd_604754] using wordTrace_append hprefix tailTrace_604754
  have hstable : (prefixWord ++ tailWord_604754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604754).length < 2 ^ (prefixWord ++ tailWord_604754).sum := by decide
  have hdescent : baseEnd_604754 < baseStart_604754 := by decide
  rcases family_descends (prefixWord ++ tailWord_604754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604804 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_604804 : Nat := 118140960795 + 604804 * 2 ^ 59
def prefixEnd_604804 : Nat := 4983230072969 + 3 ^ 40 * 604804 * 2
def baseEnd_604804 : Nat := 310555153761956935268563

theorem tailTrace_604804 : CollatzResearch.WordTrace tailWord_604804 prefixEnd_604804 310555153761956935268563 := by
  unfold tailWord_604804
  simp only [CollatzResearch.WordTrace]
  refine ⟨11029507050452937572394733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14706009400603916763192977 11029507050452937572394733)
  ·
    refine ⟨4136065143919851589648025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11029507050452937572394733 4136065143919851589648025)
    ·
      refine ⟨3102048857939888692236019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4136065143919851589648025 3102048857939888692236019)
      ·
        refine ⟨4653073286909833038354029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3102048857939888692236019 4653073286909833038354029)
        ·
          refine ⟨1744902482591187389382761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4653073286909833038354029 1744902482591187389382761)
          ·
            refine ⟨1308676861943390542037071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1744902482591187389382761 1308676861943390542037071)
            ·
              refine ⟨1963015292915085813055607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1308676861943390542037071 1963015292915085813055607)
              ·
                refine ⟨2944522939372628719583411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1963015292915085813055607 2944522939372628719583411)
                ·
                  refine ⟨4416784409058943079375117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2944522939372628719583411 4416784409058943079375117)
                  ·
                    refine ⟨1656294153397103654765669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4416784409058943079375117 1656294153397103654765669)
                    ·
                      refine ⟨310555153761956935268563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1656294153397103654765669 310555153761956935268563)
                      ·
                        rfl

theorem cell23_604804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_604804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604804 prefixEnd_604804 := by exact prefixLift 604804
  have htrace : WordTrace (prefixWord ++ tailWord_604804) baseStart_604804 baseEnd_604804 := by
    simpa [prefixWord, tailWord_604804, baseEnd_604804] using wordTrace_append hprefix tailTrace_604804
  have hstable : (prefixWord ++ tailWord_604804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604804).length < 2 ^ (prefixWord ++ tailWord_604804).sum := by decide
  have hdescent : baseEnd_604804 < baseStart_604804 := by decide
  rcases family_descends (prefixWord ++ tailWord_604804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604814 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 5, 4]
def baseStart_604814 : Nat := 118140960795 + 604814 * 2 ^ 59
def prefixEnd_604814 : Nat := 4983230072969 + 3 ^ 40 * 604814 * 2
def baseEnd_604814 : Nat := 103520096189500632047839

theorem tailTrace_604814 : CollatzResearch.WordTrace tailWord_604814 prefixEnd_604814 103520096189500632047839 := by
  unfold tailWord_604814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2757422353858705856581687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14706252553913097901768997 2757422353858705856581687)
  ·
    refine ⟨4136133530788058784872531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2757422353858705856581687 4136133530788058784872531)
    ·
      refine ⟨6204200296182088177308797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4136133530788058784872531 6204200296182088177308797)
      ·
        refine ⟨2326575111068283066490799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6204200296182088177308797 2326575111068283066490799)
        ·
          refine ⟨3489862666602424599736199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326575111068283066490799 3489862666602424599736199)
          ·
            refine ⟨5234793999903636899604299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3489862666602424599736199 5234793999903636899604299)
            ·
              refine ⟨7852190999855455349406449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5234793999903636899604299 7852190999855455349406449)
              ·
                refine ⟨5889143249891591512054837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7852190999855455349406449 5889143249891591512054837)
                ·
                  refine ⟨552107179677336704255141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5889143249891591512054837 552107179677336704255141)
                  ·
                    refine ⟨103520096189500632047839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 552107179677336704255141 103520096189500632047839)
                    ·
                      rfl

theorem cell23_604814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_604814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604814 prefixEnd_604814 := by exact prefixLift 604814
  have htrace : WordTrace (prefixWord ++ tailWord_604814) baseStart_604814 baseEnd_604814 := by
    simpa [prefixWord, tailWord_604814, baseEnd_604814] using wordTrace_append hprefix tailTrace_604814
  have hstable : (prefixWord ++ tailWord_604814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604814).length < 2 ^ (prefixWord ++ tailWord_604814).sum := by decide
  have hdescent : baseEnd_604814 < baseStart_604814 := by decide
  rcases family_descends (prefixWord ++ tailWord_604814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604824 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 4, 2, 3]
def baseStart_604824 : Nat := 118140960795 + 604824 * 2 ^ 59
def prefixEnd_604824 : Nat := 4983230072969 + 3 ^ 40 * 604824 * 2
def baseEnd_604824 : Nat := 310565423375046857018471

theorem tailTrace_604824 : CollatzResearch.WordTrace tailWord_604824 prefixEnd_604824 310565423375046857018471 := by
  unfold tailWord_604824
  simp only [CollatzResearch.WordTrace]
  refine ⟨11029871780416709280258763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14706495707222279040345017 11029871780416709280258763)
  ·
    refine ⟨16544807670625063920388145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11029871780416709280258763 16544807670625063920388145)
    ·
      refine ⟨12408605752968797940291109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16544807670625063920388145 12408605752968797940291109)
      ·
        refine ⟨2326613578681649613804583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12408605752968797940291109 2326613578681649613804583)
        ·
          refine ⟨3489920368022474420706875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326613578681649613804583 3489920368022474420706875)
          ·
            refine ⟨5234880552033711631060313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3489920368022474420706875 5234880552033711631060313)
            ·
              refine ⟨3926160414025283723295235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5234880552033711631060313 3926160414025283723295235)
              ·
                refine ⟨5889240621037925584942853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3926160414025283723295235 5889240621037925584942853)
                ·
                  refine ⟨1104232616444611047176785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5889240621037925584942853 1104232616444611047176785)
                  ·
                    refine ⟨828174462333458285382589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1104232616444611047176785 828174462333458285382589)
                    ·
                      refine ⟨310565423375046857018471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 828174462333458285382589 310565423375046857018471)
                      ·
                        rfl

theorem cell23_604824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_604824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604824 prefixEnd_604824 := by exact prefixLift 604824
  have htrace : WordTrace (prefixWord ++ tailWord_604824) baseStart_604824 baseEnd_604824 := by
    simpa [prefixWord, tailWord_604824, baseEnd_604824] using wordTrace_append hprefix tailTrace_604824
  have hstable : (prefixWord ++ tailWord_604824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604824).length < 2 ^ (prefixWord ++ tailWord_604824).sum := by decide
  have hdescent : baseEnd_604824 < baseStart_604824 := by decide
  rcases family_descends (prefixWord ++ tailWord_604824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604881 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 2, 3, 2]
def baseStart_604881 : Nat := 118140960795 + 604881 * 2 ^ 59
def prefixEnd_604881 : Nat := 4983230072969 + 3 ^ 40 * 604881 * 2
def baseEnd_604881 : Nat := 310594691772353134005709

theorem tailTrace_604881 : CollatzResearch.WordTrace tailWord_604881 prefixEnd_604881 310594691772353134005709 := by
  unfold tailWord_604881
  simp only [CollatzResearch.WordTrace]
  refine ⟨22061822521626917295342497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14707881681084611530228331 22061822521626917295342497)
  ·
    refine ⟨16546366891220187971506873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22061822521626917295342497 16546366891220187971506873)
    ·
      refine ⟨12409775168415140978630155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16546366891220187971506873 12409775168415140978630155)
      ·
        refine ⟨18614662752622711467945233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12409775168415140978630155 18614662752622711467945233)
        ·
          refine ⟨13960997064467033600958925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18614662752622711467945233 13960997064467033600958925)
          ·
            refine ⟨5235373899175137600359597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13960997064467033600958925 5235373899175137600359597)
            ·
              refine ⟨1963265212190676600134849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5235373899175137600359597 1963265212190676600134849)
              ·
                refine ⟨1472448909143007450101137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1963265212190676600134849 1472448909143007450101137)
                ·
                  refine ⟨1104336681857255587575853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1472448909143007450101137 1104336681857255587575853)
                  ·
                    refine ⟨414126255696470845340945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1104336681857255587575853 414126255696470845340945)
                    ·
                      refine ⟨310594691772353134005709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 414126255696470845340945 310594691772353134005709)
                      ·
                        rfl

theorem cell23_604881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 3, 2].length) (baseStart_604881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604881 prefixEnd_604881 := by exact prefixLift 604881
  have htrace : WordTrace (prefixWord ++ tailWord_604881) baseStart_604881 baseEnd_604881 := by
    simpa [prefixWord, tailWord_604881, baseEnd_604881] using wordTrace_append hprefix tailTrace_604881
  have hstable : (prefixWord ++ tailWord_604881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604881).length < 2 ^ (prefixWord ++ tailWord_604881).sum := by decide
  have hdescent : baseEnd_604881 < baseStart_604881 := by decide
  rcases family_descends (prefixWord ++ tailWord_604881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604888 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 3, 1, 3]
def baseStart_604888 : Nat := 118140960795 + 604888 * 2 ^ 59
def prefixEnd_604888 : Nat := 4983230072969 + 3 ^ 40 * 604888 * 2
def baseEnd_604888 : Nat := 310598286136934606618177

theorem tailTrace_604888 : CollatzResearch.WordTrace tailWord_604888 prefixEnd_604888 310598286136934606618177 := by
  unfold tailWord_604888
  simp only [CollatzResearch.WordTrace]
  refine ⟨11031038916300778745423659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14708051888401038327231545 11031038916300778745423659)
  ·
    refine ⟨16546558374451168118135489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11031038916300778745423659 16546558374451168118135489)
    ·
      refine ⟨12409918780838376088601617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16546558374451168118135489 12409918780838376088601617)
      ·
        refine ⟨9307439085628782066451213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12409918780838376088601617 9307439085628782066451213)
        ·
          refine ⟨3490289657110793274919205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9307439085628782066451213 3490289657110793274919205)
          ·
            refine ⟨654429310708273739047351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3490289657110793274919205 654429310708273739047351)
            ·
              refine ⟨981643966062410608571027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654429310708273739047351 981643966062410608571027)
              ·
                refine ⟨1472465949093615912856541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981643966062410608571027 1472465949093615912856541)
                ·
                  refine ⟨552174730910105967321203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1472465949093615912856541 552174730910105967321203)
                  ·
                    refine ⟨828262096365158950981805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 552174730910105967321203 828262096365158950981805)
                    ·
                      refine ⟨310598286136934606618177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 828262096365158950981805 310598286136934606618177)
                      ·
                        rfl

theorem cell23_604888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_604888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604888 prefixEnd_604888 := by exact prefixLift 604888
  have htrace : WordTrace (prefixWord ++ tailWord_604888) baseStart_604888 baseEnd_604888 := by
    simpa [prefixWord, tailWord_604888, baseEnd_604888] using wordTrace_append hprefix tailTrace_604888
  have hstable : (prefixWord ++ tailWord_604888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604888).length < 2 ^ (prefixWord ++ tailWord_604888).sum := by decide
  have hdescent : baseEnd_604888 < baseStart_604888 := by decide
  rcases family_descends (prefixWord ++ tailWord_604888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604911 : List Nat := [1, 1, 2, 1, 5, 2, 3, 2, 1, 1, 4]
def baseStart_604911 : Nat := 118140960795 + 604911 * 2 ^ 59
def prefixEnd_604911 : Nat := 4983230072969 + 3 ^ 40 * 604911 * 2
def baseEnd_604911 : Nat := 310610096191988016630571

theorem tailTrace_604911 : CollatzResearch.WordTrace tailWord_604911 prefixEnd_604911 310610096191988016630571 := by
  unfold tailWord_604911
  simp only [CollatzResearch.WordTrace]
  refine ⟨22062916711518232418934587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14708611141012154945956391 22062916711518232418934587)
  ·
    refine ⟨33094375067277348628401881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22062916711518232418934587 33094375067277348628401881)
    ·
      refine ⟨24820781300458011471301411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33094375067277348628401881 24820781300458011471301411)
      ·
        refine ⟨37231171950687017206952117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24820781300458011471301411 37231171950687017206952117)
        ·
          refine ⟨3490422370376907863151761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37231171950687017206952117 3490422370376907863151761)
          ·
            refine ⟨2617816777782680897363821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3490422370376907863151761 2617816777782680897363821)
            ·
              refine ⟨981681291668505336511433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2617816777782680897363821 981681291668505336511433)
              ·
                refine ⟨736260968751379002383575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 981681291668505336511433 736260968751379002383575)
                ·
                  refine ⟨1104391453127068503575363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 736260968751379002383575 1104391453127068503575363)
                  ·
                    refine ⟨1656587179690602755363045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1104391453127068503575363 1656587179690602755363045)
                    ·
                      refine ⟨310610096191988016630571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1656587179690602755363045 310610096191988016630571)
                      ·
                        rfl

theorem cell23_604911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 1, 4].length) (baseStart_604911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604911 prefixEnd_604911 := by exact prefixLift 604911
  have htrace : WordTrace (prefixWord ++ tailWord_604911) baseStart_604911 baseEnd_604911 := by
    simpa [prefixWord, tailWord_604911, baseEnd_604911] using wordTrace_append hprefix tailTrace_604911
  have hstable : (prefixWord ++ tailWord_604911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604911).length < 2 ^ (prefixWord ++ tailWord_604911).sum := by decide
  have hdescent : baseEnd_604911 < baseStart_604911 := by decide
  rcases family_descends (prefixWord ++ tailWord_604911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604924 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_604924 : Nat := 118140960795 + 604924 * 2 ^ 59
def prefixEnd_604924 : Nat := 4983230072969 + 3 ^ 40 * 604924 * 2
def baseEnd_604924 : Nat := 310616771440496465768011

theorem tailTrace_604924 : CollatzResearch.WordTrace tailWord_604924 prefixEnd_604924 310616771440496465768011 := by
  unfold tailWord_604924
  simp only [CollatzResearch.WordTrace]
  refine ⟨11031695430235567819578913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14708927240314090426105217 11031695430235567819578913)
  ·
    refine ⟨8273771572676675864684185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11031695430235567819578913 8273771572676675864684185)
    ·
      refine ⟨6205328679507506898513139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8273771572676675864684185 6205328679507506898513139)
      ·
        refine ⟨9307993019261260347769709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6205328679507506898513139 9307993019261260347769709)
        ·
          refine ⟨3490497382222972630413641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9307993019261260347769709 3490497382222972630413641)
          ·
            refine ⟨2617873036667229472810231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3490497382222972630413641 2617873036667229472810231)
            ·
              refine ⟨3926809555000844209215347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2617873036667229472810231 3926809555000844209215347)
              ·
                refine ⟨5890214332501266313823021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3926809555000844209215347 5890214332501266313823021)
                ·
                  refine ⟨2208830374687974867683633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5890214332501266313823021 2208830374687974867683633)
                  ·
                    refine ⟨1656622781015981150762725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2208830374687974867683633 1656622781015981150762725)
                    ·
                      refine ⟨310616771440496465768011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1656622781015981150762725 310616771440496465768011)
                      ·
                        rfl

theorem cell23_604924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_604924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604924 prefixEnd_604924 := by exact prefixLift 604924
  have htrace : WordTrace (prefixWord ++ tailWord_604924) baseStart_604924 baseEnd_604924 := by
    simpa [prefixWord, tailWord_604924, baseEnd_604924] using wordTrace_append hprefix tailTrace_604924
  have hstable : (prefixWord ++ tailWord_604924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604924).length < 2 ^ (prefixWord ++ tailWord_604924).sum := by decide
  have hdescent : baseEnd_604924 < baseStart_604924 := by decide
  rcases family_descends (prefixWord ++ tailWord_604924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604947 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 1, 9]
def baseStart_604947 : Nat := 118140960795 + 604947 * 2 ^ 59
def prefixEnd_604947 : Nat := 4983230072969 + 3 ^ 40 * 604947 * 2
def baseEnd_604947 : Nat := 103542860498516625260135

theorem tailTrace_604947 : CollatzResearch.WordTrace tailWord_604947 prefixEnd_604947 103542860498516625260135 := by
  unfold tailWord_604947
  simp only [CollatzResearch.WordTrace]
  refine ⟨22064229739387810567245095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14709486492925207044830063 22064229739387810567245095)
  ·
    refine ⟨33096344609081715850867643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22064229739387810567245095 33096344609081715850867643)
    ·
      refine ⟨49644516913622573776301465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33096344609081715850867643 49644516913622573776301465)
      ·
        refine ⟨37233387685216930332226099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49644516913622573776301465 37233387685216930332226099)
        ·
          refine ⟨55850081527825395498339149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37233387685216930332226099 55850081527825395498339149)
          ·
            refine ⟨20943780572934523311877181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55850081527825395498339149 20943780572934523311877181)
            ·
              refine ⟨7853917714850446241953943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20943780572934523311877181 7853917714850446241953943)
              ·
                refine ⟨11780876572275669362930915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7853917714850446241953943 11780876572275669362930915)
                ·
                  refine ⟨17671314858413504044396373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11780876572275669362930915 17671314858413504044396373)
                  ·
                    refine ⟨103542860498516625260135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 17671314858413504044396373 103542860498516625260135)
                    ·
                      rfl

theorem cell23_604947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 9].length) (baseStart_604947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604947 prefixEnd_604947 := by exact prefixLift 604947
  have htrace : WordTrace (prefixWord ++ tailWord_604947) baseStart_604947 baseEnd_604947 := by
    simpa [prefixWord, tailWord_604947, baseEnd_604947] using wordTrace_append hprefix tailTrace_604947
  have hstable : (prefixWord ++ tailWord_604947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604947).length < 2 ^ (prefixWord ++ tailWord_604947).sum := by decide
  have hdescent : baseEnd_604947 < baseStart_604947 := by decide
  rcases family_descends (prefixWord ++ tailWord_604947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604951 : List Nat := [1, 1, 3, 4, 3, 2, 1, 8]
def baseStart_604951 : Nat := 118140960795 + 604951 * 2 ^ 59
def prefixEnd_604951 : Nat := 4983230072969 + 3 ^ 40 * 604951 * 2
def baseEnd_604951 : Nat := 11504838348821031856681

theorem tailTrace_604951 : CollatzResearch.WordTrace tailWord_604951 prefixEnd_604951 11504838348821031856681 := by
  unfold tailWord_604951
  simp only [CollatzResearch.WordTrace]
  refine ⟨22064375631373319250390707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14709583754248879500260471 22064375631373319250390707)
  ·
    refine ⟨33096563447059978875586061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22064375631373319250390707 33096563447059978875586061)
    ·
      refine ⟨12411211292647492078344773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33096563447059978875586061 12411211292647492078344773)
      ·
        refine ⟨2327102117371404764689645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12411211292647492078344773 2327102117371404764689645)
        ·
          refine ⟨872663294014276786758617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2327102117371404764689645 872663294014276786758617)
          ·
            refine ⟨654497470510707590068963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 872663294014276786758617 654497470510707590068963)
            ·
              refine ⟨981746205766061385103445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654497470510707590068963 981746205766061385103445)
              ·
                refine ⟨11504838348821031856681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 981746205766061385103445 11504838348821031856681)
                ·
                  rfl

theorem cell23_604951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 8].length) (baseStart_604951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604951 prefixEnd_604951 := by exact prefixLift 604951
  have htrace : WordTrace (prefixWord ++ tailWord_604951) baseStart_604951 baseEnd_604951 := by
    simpa [prefixWord, tailWord_604951, baseEnd_604951] using wordTrace_append hprefix tailTrace_604951
  have hstable : (prefixWord ++ tailWord_604951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604951).length < 2 ^ (prefixWord ++ tailWord_604951).sum := by decide
  have hdescent : baseEnd_604951 < baseStart_604951 := by decide
  rcases family_descends (prefixWord ++ tailWord_604951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604961 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 1, 3, 3]
def baseStart_604961 : Nat := 118140960795 + 604961 * 2 ^ 59
def prefixEnd_604961 : Nat := 4983230072969 + 3 ^ 40 * 604961 * 2
def baseEnd_604961 : Nat := 310635770224712821005341

theorem tailTrace_604961 : CollatzResearch.WordTrace tailWord_604961 prefixEnd_604961 310635770224712821005341 := by
  unfold tailWord_604961
  simp only [CollatzResearch.WordTrace]
  refine ⟨22064740361337090958254737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14709826907558060638836491 22064740361337090958254737)
  ·
    refine ⟨16548555271002818218691053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22064740361337090958254737 16548555271002818218691053)
    ·
      refine ⟨6205708226626056832009145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16548555271002818218691053 6205708226626056832009145)
      ·
        refine ⟨4654281169969542624006859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6205708226626056832009145 4654281169969542624006859)
        ·
          refine ⟨6981421754954313936010289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4654281169969542624006859 6981421754954313936010289)
          ·
            refine ⟨5236066316215735452007717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6981421754954313936010289 5236066316215735452007717)
            ·
              refine ⟨981762434290450397251447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5236066316215735452007717 981762434290450397251447)
              ·
                refine ⟨1472643651435675595877171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981762434290450397251447 1472643651435675595877171)
                ·
                  refine ⟨2208965477153513393815757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1472643651435675595877171 2208965477153513393815757)
                  ·
                    refine ⟨828362053932567522680909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2208965477153513393815757 828362053932567522680909)
                    ·
                      refine ⟨310635770224712821005341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 828362053932567522680909 310635770224712821005341)
                      ·
                        rfl

theorem cell23_604961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_604961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_604961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_604961 prefixEnd_604961 := by exact prefixLift 604961
  have htrace : WordTrace (prefixWord ++ tailWord_604961) baseStart_604961 baseEnd_604961 := by
    simpa [prefixWord, tailWord_604961, baseEnd_604961] using wordTrace_append hprefix tailTrace_604961
  have hstable : (prefixWord ++ tailWord_604961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604961).length < 2 ^ (prefixWord ++ tailWord_604961).sum := by decide
  have hdescent : baseEnd_604961 < baseStart_604961 := by decide
  rcases family_descends (prefixWord ++ tailWord_604961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605012 : List Nat := [2, 4, 1, 1, 4, 1, 3, 1, 2, 1, 3]
def baseStart_605012 : Nat := 118140960795 + 605012 * 2 ^ 59
def prefixEnd_605012 : Nat := 4983230072969 + 3 ^ 40 * 605012 * 2
def baseEnd_605012 : Nat := 310661957738092121467607

theorem tailTrace_605012 : CollatzResearch.WordTrace tailWord_605012 prefixEnd_605012 310661957738092121467607 := by
  unfold tailWord_605012
  simp only [CollatzResearch.WordTrace]
  refine ⟨11033300242076163334180645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14711066989434884445574193 11033300242076163334180645)
  ·
    refine ⟨2068743795389280625158871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11033300242076163334180645 2068743795389280625158871)
    ·
      refine ⟨3103115693083920937738307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2068743795389280625158871 3103115693083920937738307)
      ·
        refine ⟨4654673539625881406607461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3103115693083920937738307 4654673539625881406607461)
        ·
          refine ⟨872751288679852763738899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4654673539625881406607461 872751288679852763738899)
          ·
            refine ⟨1309126933019779145608349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872751288679852763738899 1309126933019779145608349)
            ·
              refine ⟨490922599882417179603131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1309126933019779145608349 490922599882417179603131)
              ·
                refine ⟨736383899823625769404697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490922599882417179603131 736383899823625769404697)
                ·
                  refine ⟨552287924867719327053523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 736383899823625769404697 552287924867719327053523)
                  ·
                    refine ⟨828431887301578990580285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 552287924867719327053523 828431887301578990580285)
                    ·
                      refine ⟨310661957738092121467607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 828431887301578990580285 310661957738092121467607)
                      ·
                        rfl

theorem cell23_605012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_605012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605012 prefixEnd_605012 := by exact prefixLift 605012
  have htrace : WordTrace (prefixWord ++ tailWord_605012) baseStart_605012 baseEnd_605012 := by
    simpa [prefixWord, tailWord_605012, baseEnd_605012] using wordTrace_append hprefix tailTrace_605012
  have hstable : (prefixWord ++ tailWord_605012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605012).length < 2 ^ (prefixWord ++ tailWord_605012).sum := by decide
  have hdescent : baseEnd_605012 < baseStart_605012 := by decide
  rcases family_descends (prefixWord ++ tailWord_605012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605018 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2]
def baseStart_605018 : Nat := 118140960795 + 605018 * 2 ^ 59
def prefixEnd_605018 : Nat := 4983230072969 + 3 ^ 40 * 605018 * 2
def baseEnd_605018 : Nat := 310665038622019097992579

theorem tailTrace_605018 : CollatzResearch.WordTrace tailWord_605018 prefixEnd_605018 310665038622019097992579 := by
  unfold tailWord_605018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5516704830532647423269927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14711212881420393128719805 5516704830532647423269927)
  ·
    refine ⟨8275057245798971134904891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5516704830532647423269927 8275057245798971134904891)
    ·
      refine ⟨12412585868698456702357337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8275057245798971134904891 12412585868698456702357337)
      ·
        refine ⟨9309439401523842526768003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12412585868698456702357337 9309439401523842526768003)
        ·
          refine ⟨13964159102285763790152005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9309439401523842526768003 13964159102285763790152005)
          ·
            refine ⟨2618279831678580710653501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13964159102285763790152005 2618279831678580710653501)
            ·
              refine ⟨981854936879467766495063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2618279831678580710653501 981854936879467766495063)
              ·
                refine ⟨1472782405319201649742595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981854936879467766495063 1472782405319201649742595)
                ·
                  refine ⟨2209173607978802474613893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1472782405319201649742595 2209173607978802474613893)
                  ·
                    refine ⟨414220051496025463990105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2209173607978802474613893 414220051496025463990105)
                    ·
                      refine ⟨310665038622019097992579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 414220051496025463990105 310665038622019097992579)
                      ·
                        rfl

theorem cell23_605018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_605018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605018 prefixEnd_605018 := by exact prefixLift 605018
  have htrace : WordTrace (prefixWord ++ tailWord_605018) baseStart_605018 baseEnd_605018 := by
    simpa [prefixWord, tailWord_605018, baseEnd_605018] using wordTrace_append hprefix tailTrace_605018
  have hstable : (prefixWord ++ tailWord_605018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605018).length < 2 ^ (prefixWord ++ tailWord_605018).sum := by decide
  have hdescent : baseEnd_605018 < baseStart_605018 := by decide
  rcases family_descends (prefixWord ++ tailWord_605018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605024 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 7]
def baseStart_605024 : Nat := 118140960795 + 605024 * 2 ^ 59
def prefixEnd_605024 : Nat := 4983230072969 + 3 ^ 40 * 605024 * 2
def baseEnd_605024 : Nat := 34518679945105119390839

theorem tailTrace_605024 : CollatzResearch.WordTrace tailWord_605024 prefixEnd_605024 34518679945105119390839 := by
  unfold tailWord_605024
  simp only [CollatzResearch.WordTrace]
  refine ⟨11033519080054426358899063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14711358773405901811865417 11033519080054426358899063)
  ·
    refine ⟨16550278620081639538348595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11033519080054426358899063 16550278620081639538348595)
    ·
      refine ⟨24825417930122459307522893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16550278620081639538348595 24825417930122459307522893)
      ·
        refine ⟨9309531723795922240321085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24825417930122459307522893 9309531723795922240321085)
        ·
          refine ⟨3491074396423470840120407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9309531723795922240321085 3491074396423470840120407)
          ·
            refine ⟨5236611594635206260180611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3491074396423470840120407 5236611594635206260180611)
            ·
              refine ⟨7854917391952809390270917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5236611594635206260180611 7854917391952809390270917)
              ·
                refine ⟨1472797010991151760675797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7854917391952809390270917 1472797010991151760675797)
                ·
                  refine ⟨34518679945105119390839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1472797010991151760675797 34518679945105119390839)
                  ·
                    rfl

theorem cell23_605024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 7].length) (baseStart_605024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605024 prefixEnd_605024 := by exact prefixLift 605024
  have htrace : WordTrace (prefixWord ++ tailWord_605024) baseStart_605024 baseEnd_605024 := by
    simpa [prefixWord, tailWord_605024, baseEnd_605024] using wordTrace_append hprefix tailTrace_605024
  have hstable : (prefixWord ++ tailWord_605024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605024).length < 2 ^ (prefixWord ++ tailWord_605024).sum := by decide
  have hdescent : baseEnd_605024 < baseStart_605024 := by decide
  rcases family_descends (prefixWord ++ tailWord_605024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605038 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_605038 : Nat := 118140960795 + 605038 * 2 ^ 59
def prefixEnd_605038 : Nat := 4983230072969 + 3 ^ 40 * 605038 * 2
def baseEnd_605038 : Nat := 310675308235109019742487

theorem tailTrace_605038 : CollatzResearch.WordTrace tailWord_605038 prefixEnd_605038 310675308235109019742487 := by
  unfold tailWord_605038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2758443597757266638600971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14711699188038755405871845 2758443597757266638600971)
  ·
    refine ⟨4137665396635899957901457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2758443597757266638600971 4137665396635899957901457)
    ·
      refine ⟨3103249047476924968426093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4137665396635899957901457 3103249047476924968426093)
      ·
        refine ⟨1163718392803846863159785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3103249047476924968426093 1163718392803846863159785)
        ·
          refine ⟨872788794602885147369839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1163718392803846863159785 872788794602885147369839)
          ·
            refine ⟨1309183191904327721054759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872788794602885147369839 1309183191904327721054759)
            ·
              refine ⟨1963774787856491581582139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1309183191904327721054759 1963774787856491581582139)
              ·
                refine ⟨2945662181784737372373209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1963774787856491581582139 2945662181784737372373209)
                ·
                  refine ⟨2209246636338553029279907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2945662181784737372373209 2209246636338553029279907)
                  ·
                    refine ⟨3313869954507829543919861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2209246636338553029279907 3313869954507829543919861)
                    ·
                      refine ⟨310675308235109019742487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3313869954507829543919861 310675308235109019742487)
                      ·
                        rfl

theorem cell23_605038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_605038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605038 prefixEnd_605038 := by exact prefixLift 605038
  have htrace : WordTrace (prefixWord ++ tailWord_605038) baseStart_605038 baseEnd_605038 := by
    simpa [prefixWord, tailWord_605038, baseEnd_605038] using wordTrace_append hprefix tailTrace_605038
  have hstable : (prefixWord ++ tailWord_605038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605038).length < 2 ^ (prefixWord ++ tailWord_605038).sum := by decide
  have hdescent : baseEnd_605038 < baseStart_605038 := by decide
  rcases family_descends (prefixWord ++ tailWord_605038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605091 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 4]
def baseStart_605091 : Nat := 118140960795 + 605091 * 2 ^ 59
def prefixEnd_605091 : Nat := 4983230072969 + 3 ^ 40 * 605091 * 2
def baseEnd_605091 : Nat := 310702522709797312379743

theorem tailTrace_605091 : CollatzResearch.WordTrace tailWord_605091 prefixEnd_605091 310702522709797312379743 := by
  unfold tailWord_605091
  simp only [CollatzResearch.WordTrace]
  refine ⟨22069481850866123160487127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14712987900577415440324751 22069481850866123160487127)
  ·
    refine ⟨33104222776299184740730691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22069481850866123160487127 33104222776299184740730691)
    ·
      refine ⟨49656334164448777111096037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33104222776299184740730691 49656334164448777111096037)
      ·
        refine ⟨9310562655834145708330507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49656334164448777111096037 9310562655834145708330507)
        ·
          refine ⟨13965843983751218562495761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9310562655834145708330507 13965843983751218562495761)
          ·
            refine ⟨10474382987813413921871821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13965843983751218562495761 10474382987813413921871821)
            ·
              refine ⟨3927893620430030220701933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10474382987813413921871821 3927893620430030220701933)
              ·
                refine ⟨1472960107661261332763225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3927893620430030220701933 1472960107661261332763225)
                ·
                  refine ⟨1104720080745945999572419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1472960107661261332763225 1104720080745945999572419)
                  ·
                    refine ⟨1657080121118918999358629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1104720080745945999572419 1657080121118918999358629)
                    ·
                      refine ⟨310702522709797312379743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1657080121118918999358629 310702522709797312379743)
                      ·
                        rfl

theorem cell23_605091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_605091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605091 prefixEnd_605091 := by exact prefixLift 605091
  have htrace : WordTrace (prefixWord ++ tailWord_605091) baseStart_605091 baseEnd_605091 := by
    simpa [prefixWord, tailWord_605091, baseEnd_605091] using wordTrace_append hprefix tailTrace_605091
  have hstable : (prefixWord ++ tailWord_605091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605091).length < 2 ^ (prefixWord ++ tailWord_605091).sum := by decide
  have hdescent : baseEnd_605091 < baseStart_605091 := by decide
  rcases family_descends (prefixWord ++ tailWord_605091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605118 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_605118 : Nat := 118140960795 + 605118 * 2 ^ 59
def prefixEnd_605118 : Nat := 4983230072969 + 3 ^ 40 * 605118 * 2
def baseEnd_605118 : Nat := 103572128895822902247373

theorem tailTrace_605118 : CollatzResearch.WordTrace tailWord_605118 prefixEnd_605118 103572128895822902247373 := by
  unfold tailWord_605118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2758808327721038346465001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14713644414512204514480005 2758808327721038346465001)
  ·
    refine ⟨2069106245790778759848751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2758808327721038346465001 2069106245790778759848751)
    ·
      refine ⟨3103659368686168139773127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2069106245790778759848751 3103659368686168139773127)
      ·
        refine ⟨4655489053029252209659691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3103659368686168139773127 4655489053029252209659691)
        ·
          refine ⟨6983233579543878314489537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4655489053029252209659691 6983233579543878314489537)
          ·
            refine ⟨5237425184657908735867153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6983233579543878314489537 5237425184657908735867153)
            ·
              refine ⟨3928068888493431551900365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5237425184657908735867153 3928068888493431551900365)
              ·
                refine ⟨1473025833185036831962637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3928068888493431551900365 1473025833185036831962637)
                ·
                  refine ⟨552384687444388811985989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1473025833185036831962637 552384687444388811985989)
                  ·
                    refine ⟨103572128895822902247373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 552384687444388811985989 103572128895822902247373)
                    ·
                      rfl

theorem cell23_605118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_605118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605118 prefixEnd_605118 := by exact prefixLift 605118
  have htrace : WordTrace (prefixWord ++ tailWord_605118) baseStart_605118 baseEnd_605118 := by
    simpa [prefixWord, tailWord_605118, baseEnd_605118] using wordTrace_append hprefix tailTrace_605118
  have hstable : (prefixWord ++ tailWord_605118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605118).length < 2 ^ (prefixWord ++ tailWord_605118).sum := by decide
  have hdescent : baseEnd_605118 < baseStart_605118 := by decide
  rcases family_descends (prefixWord ++ tailWord_605118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605131 : List Nat := [1, 1, 1, 1, 3, 5, 2, 3, 6]
def baseStart_605131 : Nat := 118140960795 + 605131 * 2 ^ 59
def prefixEnd_605131 : Nat := 4983230072969 + 3 ^ 40 * 605131 * 2
def baseEnd_605131 : Nat := 34524784659553017319951

theorem tailTrace_605131 : CollatzResearch.WordTrace tailWord_605131 prefixEnd_605131 34524784659553017319951 := by
  unfold tailWord_605131
  simp only [CollatzResearch.WordTrace]
  refine ⟨22070940770721209991943247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14713960513814139994628831 22070940770721209991943247)
  ·
    refine ⟨33106411156081814987914871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22070940770721209991943247 33106411156081814987914871)
    ·
      refine ⟨49659616734122722481872307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33106411156081814987914871 49659616734122722481872307)
      ·
        refine ⟨74489425101184083722808461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49659616734122722481872307 74489425101184083722808461)
        ·
          refine ⟨27933534412944031396053173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74489425101184083722808461 27933534412944031396053173)
          ·
            refine ⟨2618768851213502943379985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27933534412944031396053173 2618768851213502943379985)
            ·
              refine ⟨1964076638410127207534989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2618768851213502943379985 1964076638410127207534989)
              ·
                refine ⟨736528739403797702825621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1964076638410127207534989 736528739403797702825621)
                ·
                  refine ⟨34524784659553017319951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 736528739403797702825621 34524784659553017319951)
                  ·
                    rfl

theorem cell23_605131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 6].length) (baseStart_605131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605131 prefixEnd_605131 := by exact prefixLift 605131
  have htrace : WordTrace (prefixWord ++ tailWord_605131) baseStart_605131 baseEnd_605131 := by
    simpa [prefixWord, tailWord_605131, baseEnd_605131] using wordTrace_append hprefix tailTrace_605131
  have hstable : (prefixWord ++ tailWord_605131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605131).length < 2 ^ (prefixWord ++ tailWord_605131).sum := by decide
  have hdescent : baseEnd_605131 < baseStart_605131 := by decide
  rcases family_descends (prefixWord ++ tailWord_605131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605142 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_605142 : Nat := 118140960795 + 605142 * 2 ^ 59
def prefixEnd_605142 : Nat := 4983230072969 + 3 ^ 40 * 605142 * 2
def baseEnd_605142 : Nat := 310728710223176612842009

theorem tailTrace_605142 : CollatzResearch.WordTrace tailWord_605142 prefixEnd_605142 310728710223176612842009 := by
  unfold tailWord_605142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1379458873355084929412105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14714227982454239247062453 1379458873355084929412105)
  ·
    refine ⟨1034594155016313697059079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1379458873355084929412105 1034594155016313697059079)
    ·
      refine ⟨1551891232524470545588619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1034594155016313697059079 1551891232524470545588619)
      ·
        refine ⟨2327836848786705818382929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1551891232524470545588619 2327836848786705818382929)
        ·
          refine ⟨1745877636590029363787197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2327836848786705818382929 1745877636590029363787197)
          ·
            refine ⟨654704113721261011420199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1745877636590029363787197 654704113721261011420199)
            ·
              refine ⟨982056170581891517130299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654704113721261011420199 982056170581891517130299)
              ·
                refine ⟨1473084255872837275695449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982056170581891517130299 1473084255872837275695449)
                ·
                  refine ⟨1104813191904627956771587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1473084255872837275695449 1104813191904627956771587)
                  ·
                    refine ⟨1657219787856941935157381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1104813191904627956771587 1657219787856941935157381)
                    ·
                      refine ⟨310728710223176612842009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1657219787856941935157381 310728710223176612842009)
                      ·
                        rfl

theorem cell23_605142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_605142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605142 prefixEnd_605142 := by exact prefixLift 605142
  have htrace : WordTrace (prefixWord ++ tailWord_605142) baseStart_605142 baseEnd_605142 := by
    simpa [prefixWord, tailWord_605142, baseEnd_605142] using wordTrace_append hprefix tailTrace_605142
  have hstable : (prefixWord ++ tailWord_605142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605142).length < 2 ^ (prefixWord ++ tailWord_605142).sum := by decide
  have hdescent : baseEnd_605142 < baseStart_605142 := by decide
  rcases family_descends (prefixWord ++ tailWord_605142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605145 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 2, 2, 3]
def baseStart_605145 : Nat := 118140960795 + 605145 * 2 ^ 59
def prefixEnd_605145 : Nat := 4983230072969 + 3 ^ 40 * 605145 * 2
def baseEnd_605145 : Nat := 310730250665140101104495

theorem tailTrace_605145 : CollatzResearch.WordTrace tailWord_605145 prefixEnd_605145 310730250665140101104495 := by
  unfold tailWord_605145
  simp only [CollatzResearch.WordTrace]
  refine ⟨22071451392670490382952889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14714300928446993588635259 22071451392670490382952889)
  ·
    refine ⟨16553588544502867787214667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22071451392670490382952889 16553588544502867787214667)
    ·
      refine ⟨24830382816754301680822001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16553588544502867787214667 24830382816754301680822001)
      ·
        refine ⟨18622787112565726260616501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24830382816754301680822001 18622787112565726260616501)
        ·
          refine ⟨1745886291803036836932797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18622787112565726260616501 1745886291803036836932797)
          ·
            refine ⟨654707359426138813849799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1745886291803036836932797 654707359426138813849799)
            ·
              refine ⟨982061039139208220774699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654707359426138813849799 982061039139208220774699)
              ·
                refine ⟨1473091558708812331162049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982061039139208220774699 1473091558708812331162049)
                ·
                  refine ⟨1104818669031609248371537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1473091558708812331162049 1104818669031609248371537)
                  ·
                    refine ⟨828614001773706936278653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1104818669031609248371537 828614001773706936278653)
                    ·
                      refine ⟨310730250665140101104495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 828614001773706936278653 310730250665140101104495)
                      ·
                        rfl

theorem cell23_605145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_605145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605145 prefixEnd_605145 := by exact prefixLift 605145
  have htrace : WordTrace (prefixWord ++ tailWord_605145) baseStart_605145 baseEnd_605145 := by
    simpa [prefixWord, tailWord_605145, baseEnd_605145] using wordTrace_append hprefix tailTrace_605145
  have hstable : (prefixWord ++ tailWord_605145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605145).length < 2 ^ (prefixWord ++ tailWord_605145).sum := by decide
  have hdescent : baseEnd_605145 < baseStart_605145 := by decide
  rcases family_descends (prefixWord ++ tailWord_605145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605168 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 4, 3, 2]
def baseStart_605168 : Nat := 118140960795 + 605168 * 2 ^ 59
def prefixEnd_605168 : Nat := 4983230072969 + 3 ^ 40 * 605168 * 2
def baseEnd_605168 : Nat := 310742060720193511116889

theorem tailTrace_605168 : CollatzResearch.WordTrace tailWord_605168 prefixEnd_605168 310742060720193511116889 := by
  unfold tailWord_605168
  simp only [CollatzResearch.WordTrace]
  refine ⟨11036145135793582655520079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14714860181058110207360105 11036145135793582655520079)
  ·
    refine ⟨16554217703690373983280119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11036145135793582655520079 16554217703690373983280119)
    ·
      refine ⟨24831326555535560974920179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16554217703690373983280119 24831326555535560974920179)
      ·
        refine ⟨37246989833303341462380269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24831326555535560974920179 37246989833303341462380269)
        ·
          refine ⟨13967621187488753048392601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37246989833303341462380269 13967621187488753048392601)
          ·
            refine ⟨10475715890616564786294451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13967621187488753048392601 10475715890616564786294451)
            ·
              refine ⟨15713573835924847179441677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10475715890616564786294451 15713573835924847179441677)
              ·
                refine ⟨5892590188471817692290629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15713573835924847179441677 5892590188471817692290629)
                ·
                  refine ⟨1104860660338465817304493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5892590188471817692290629 1104860660338465817304493)
                  ·
                    refine ⟨414322747626924681489185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1104860660338465817304493 414322747626924681489185)
                    ·
                      refine ⟨310742060720193511116889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 414322747626924681489185 310742060720193511116889)
                      ·
                        rfl

theorem cell23_605168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 4, 3, 2].length) (baseStart_605168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605168 prefixEnd_605168 := by exact prefixLift 605168
  have htrace : WordTrace (prefixWord ++ tailWord_605168) baseStart_605168 baseEnd_605168 := by
    simpa [prefixWord, tailWord_605168, baseEnd_605168] using wordTrace_append hprefix tailTrace_605168
  have hstable : (prefixWord ++ tailWord_605168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605168).length < 2 ^ (prefixWord ++ tailWord_605168).sum := by decide
  have hdescent : baseEnd_605168 < baseStart_605168 := by decide
  rcases family_descends (prefixWord ++ tailWord_605168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605182 : List Nat := [4, 2, 2, 2, 2, 1, 3, 1, 6]
def baseStart_605182 : Nat := 118140960795 + 605182 * 2 ^ 59
def prefixEnd_605182 : Nat := 4983230072969 + 3 ^ 40 * 605182 * 2
def baseEnd_605182 : Nat := 34527694383261828482425

theorem tailTrace_605182 : CollatzResearch.WordTrace tailWord_605182 prefixEnd_605182 34527694383261828482425 := by
  unfold tailWord_605182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2759100111692055712756225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14715200595690963801366533 2759100111692055712756225)
  ·
    refine ⟨2069325083769041784567169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2759100111692055712756225 2069325083769041784567169)
    ·
      refine ⟨1551993812826781338425377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2069325083769041784567169 1551993812826781338425377)
      ·
        refine ⟨1163995359620086003819033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1551993812826781338425377 1163995359620086003819033)
        ·
          refine ⟨872996519715064502864275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1163995359620086003819033 872996519715064502864275)
          ·
            refine ⟨1309494779572596754296413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872996519715064502864275 1309494779572596754296413)
            ·
              refine ⟨491060542339723782861155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1309494779572596754296413 491060542339723782861155)
              ·
                refine ⟨736590813509585674291733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491060542339723782861155 736590813509585674291733)
                ·
                  refine ⟨34527694383261828482425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 736590813509585674291733 34527694383261828482425)
                  ·
                    rfl

theorem cell23_605182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_605182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605182 prefixEnd_605182 := by exact prefixLift 605182
  have htrace : WordTrace (prefixWord ++ tailWord_605182) baseStart_605182 baseEnd_605182 := by
    simpa [prefixWord, tailWord_605182, baseEnd_605182] using wordTrace_append hprefix tailTrace_605182
  have hstable : (prefixWord ++ tailWord_605182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605182).length < 2 ^ (prefixWord ++ tailWord_605182).sum := by decide
  have hdescent : baseEnd_605182 < baseStart_605182 := by decide
  rcases family_descends (prefixWord ++ tailWord_605182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605201 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 3]
def baseStart_605201 : Nat := 118140960795 + 605201 * 2 ^ 59
def prefixEnd_605201 : Nat := 4983230072969 + 3 ^ 40 * 605201 * 2
def baseEnd_605201 : Nat := 310759005581791882004237

theorem tailTrace_605201 : CollatzResearch.WordTrace tailWord_605201 prefixEnd_605201 310759005581791882004237 := by
  unfold tailWord_605201
  simp only [CollatzResearch.WordTrace]
  refine ⟨22073493880467611946991457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14715662586978407964660971 22073493880467611946991457)
  ·
    refine ⟨16555120410350708960243593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22073493880467611946991457 16555120410350708960243593)
    ·
      refine ⟨12416340307763031720182695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16555120410350708960243593 12416340307763031720182695)
      ·
        refine ⟨18624510461644547580274043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12416340307763031720182695 18624510461644547580274043)
        ·
          refine ⟨27936765692466821370411065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18624510461644547580274043 27936765692466821370411065)
          ·
            refine ⟨20952574269350116027808299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27936765692466821370411065 20952574269350116027808299)
            ·
              refine ⟨31428861404025174041712449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20952574269350116027808299 31428861404025174041712449)
              ·
                refine ⟨23571646053018880531284337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31428861404025174041712449 23571646053018880531284337)
                ·
                  refine ⟨17678734539764160398463253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23571646053018880531284337 17678734539764160398463253)
                  ·
                    refine ⟨828690681551445018677965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17678734539764160398463253 828690681551445018677965)
                    ·
                      refine ⟨310759005581791882004237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 828690681551445018677965 310759005581791882004237)
                      ·
                        rfl

theorem cell23_605201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_605201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605201 prefixEnd_605201 := by exact prefixLift 605201
  have htrace : WordTrace (prefixWord ++ tailWord_605201) baseStart_605201 baseEnd_605201 := by
    simpa [prefixWord, tailWord_605201, baseEnd_605201] using wordTrace_append hprefix tailTrace_605201
  have hstable : (prefixWord ++ tailWord_605201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605201).length < 2 ^ (prefixWord ++ tailWord_605201).sum := by decide
  have hdescent : baseEnd_605201 < baseStart_605201 := by decide
  rcases family_descends (prefixWord ++ tailWord_605201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605208 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 4, 4]
def baseStart_605208 : Nat := 118140960795 + 605208 * 2 ^ 59
def prefixEnd_605208 : Nat := 4983230072969 + 3 ^ 40 * 605208 * 2
def baseEnd_605208 : Nat := 103587533315457784872235

theorem tailTrace_605208 : CollatzResearch.WordTrace tailWord_605208 prefixEnd_605208 103587533315457784872235 := by
  unfold tailWord_605208
  simp only [CollatzResearch.WordTrace]
  refine ⟨11036874595721126071248139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14715832794294834761664185 11036874595721126071248139)
  ·
    refine ⟨16555311893581689106872209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11036874595721126071248139 16555311893581689106872209)
    ·
      refine ⟨12416483920186266830154157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16555311893581689106872209 12416483920186266830154157)
      ·
        refine ⟨4656181470069850061307809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12416483920186266830154157 4656181470069850061307809)
        ·
          refine ⟨3492136102552387545980857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4656181470069850061307809 3492136102552387545980857)
          ·
            refine ⟨2619102076914290659485643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3492136102552387545980857 2619102076914290659485643)
            ·
              refine ⟨3928653115371435989228465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2619102076914290659485643 3928653115371435989228465)
              ·
                refine ⟨2946489836528576991921349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3928653115371435989228465 2946489836528576991921349)
                ·
                  refine ⟨552466844349108185985253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2946489836528576991921349 552466844349108185985253)
                  ·
                    refine ⟨103587533315457784872235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 552466844349108185985253 103587533315457784872235)
                    ·
                      rfl

theorem cell23_605208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_605208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605208 prefixEnd_605208 := by exact prefixLift 605208
  have htrace : WordTrace (prefixWord ++ tailWord_605208) baseStart_605208 baseEnd_605208 := by
    simpa [prefixWord, tailWord_605208, baseEnd_605208] using wordTrace_append hprefix tailTrace_605208
  have hstable : (prefixWord ++ tailWord_605208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605208).length < 2 ^ (prefixWord ++ tailWord_605208).sum := by decide
  have hdescent : baseEnd_605208 < baseStart_605208 := by decide
  rcases family_descends (prefixWord ++ tailWord_605208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605218 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_605218 : Nat := 118140960795 + 605218 * 2 ^ 59
def prefixEnd_605218 : Nat := 4983230072969 + 3 ^ 40 * 605218 * 2
def baseEnd_605218 : Nat := 310767734752918315491659

theorem tailTrace_605218 : CollatzResearch.WordTrace tailWord_605218 prefixEnd_605218 310767734752918315491659 := by
  unfold tailWord_605218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5518528480351505962590077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14716075947604015900240205 5518528480351505962590077)
  ·
    refine ⟨2069448180131814735971279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5518528480351505962590077 2069448180131814735971279)
    ·
      refine ⟨3104172270197722103956919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2069448180131814735971279 3104172270197722103956919)
      ·
        refine ⟨4656258405296583155935379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3104172270197722103956919 4656258405296583155935379)
        ·
          refine ⟨6984387607944874733903069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4656258405296583155935379 6984387607944874733903069)
          ·
            refine ⟨2619145352979328025213651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6984387607944874733903069 2619145352979328025213651)
            ·
              refine ⟨3928718029468992037820477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2619145352979328025213651 3928718029468992037820477)
              ·
                refine ⟨1473269261050872014182679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3928718029468992037820477 1473269261050872014182679)
                ·
                  refine ⟨2209903891576308021274019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1473269261050872014182679 2209903891576308021274019)
                  ·
                    refine ⟨3314855837364462031911029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2209903891576308021274019 3314855837364462031911029)
                    ·
                      refine ⟨310767734752918315491659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3314855837364462031911029 310767734752918315491659)
                      ·
                        rfl

theorem cell23_605218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_605218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605218 prefixEnd_605218 := by exact prefixLift 605218
  have htrace : WordTrace (prefixWord ++ tailWord_605218) baseStart_605218 baseEnd_605218 := by
    simpa [prefixWord, tailWord_605218, baseEnd_605218] using wordTrace_append hprefix tailTrace_605218
  have hstable : (prefixWord ++ tailWord_605218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605218).length < 2 ^ (prefixWord ++ tailWord_605218).sum := by decide
  have hdescent : baseEnd_605218 < baseStart_605218 := by decide
  rcases family_descends (prefixWord ++ tailWord_605218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605226 : List Nat := [3, 1, 4, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_605226 : Nat := 118140960795 + 605226 * 2 ^ 59
def prefixEnd_605226 : Nat := 4983230072969 + 3 ^ 40 * 605226 * 2
def baseEnd_605226 : Nat := 310771842598154284191623

theorem tailTrace_605226 : CollatzResearch.WordTrace tailWord_605226 prefixEnd_605226 310771842598154284191623 := by
  unfold tailWord_605226
  simp only [CollatzResearch.WordTrace]
  refine ⟨5518601426344260304162883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14716270470251360811101021 5518601426344260304162883)
  ·
    refine ⟨8277902139516390456244325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5518601426344260304162883 8277902139516390456244325)
    ·
      refine ⟨1552106651159323210545811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8277902139516390456244325 1552106651159323210545811)
      ·
        refine ⟨2328159976738984815818717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1552106651159323210545811 2328159976738984815818717)
        ·
          refine ⟨873059991277119305932019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2328159976738984815818717 873059991277119305932019)
          ·
            refine ⟨1309589986915678958898029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873059991277119305932019 1309589986915678958898029)
            ·
              refine ⟨491096245093379609586761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1309589986915678958898029 491096245093379609586761)
              ·
                refine ⟨368322183820034707190071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491096245093379609586761 368322183820034707190071)
                ·
                  refine ⟨552483275730052060785107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368322183820034707190071 552483275730052060785107)
                  ·
                    refine ⟨828724913595078091177661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 552483275730052060785107 828724913595078091177661)
                    ·
                      refine ⟨310771842598154284191623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 828724913595078091177661 310771842598154284191623)
                      ·
                        rfl

theorem cell23_605226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_605226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605226 prefixEnd_605226 := by exact prefixLift 605226
  have htrace : WordTrace (prefixWord ++ tailWord_605226) baseStart_605226 baseEnd_605226 := by
    simpa [prefixWord, tailWord_605226, baseEnd_605226] using wordTrace_append hprefix tailTrace_605226
  have hstable : (prefixWord ++ tailWord_605226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605226).length < 2 ^ (prefixWord ++ tailWord_605226).sum := by decide
  have hdescent : baseEnd_605226 < baseStart_605226 := by decide
  rcases family_descends (prefixWord ++ tailWord_605226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605238 : List Nat := [5, 1, 2, 1, 1, 2, 1, 10]
def baseStart_605238 : Nat := 118140960795 + 605238 * 2 ^ 59
def prefixEnd_605238 : Nat := 4983230072969 + 3 ^ 40 * 605238 * 2
def baseEnd_605238 : Nat := 11510296458000305083021

theorem tailTrace_605238 : CollatzResearch.WordTrace tailWord_605238 prefixEnd_605238 11510296458000305083021 := by
  unfold tailWord_605238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1379677711333347954130523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14716562254222378177392245 1379677711333347954130523)
  ·
    refine ⟨2069516567000021931195785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1379677711333347954130523 2069516567000021931195785)
    ·
      refine ⟨1552137425250016448396839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2069516567000021931195785 1552137425250016448396839)
      ·
        refine ⟨2328206137875024672595259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1552137425250016448396839 2328206137875024672595259)
        ·
          refine ⟨3492309206812537008892889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2328206137875024672595259 3492309206812537008892889)
          ·
            refine ⟨2619231905109402756669667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3492309206812537008892889 2619231905109402756669667)
            ·
              refine ⟨3928847857664104135004501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2619231905109402756669667 3928847857664104135004501)
              ·
                refine ⟨11510296458000305083021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3928847857664104135004501 11510296458000305083021)
                ·
                  rfl

theorem cell23_605238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_605238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605238 prefixEnd_605238 := by exact prefixLift 605238
  have htrace : WordTrace (prefixWord ++ tailWord_605238) baseStart_605238 baseEnd_605238 := by
    simpa [prefixWord, tailWord_605238, baseEnd_605238] using wordTrace_append hprefix tailTrace_605238
  have hstable : (prefixWord ++ tailWord_605238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605238).length < 2 ^ (prefixWord ++ tailWord_605238).sum := by decide
  have hdescent : baseEnd_605238 < baseStart_605238 := by decide
  rcases family_descends (prefixWord ++ tailWord_605238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605248 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 3]
def baseStart_605248 : Nat := 118140960795 + 605248 * 2 ^ 59
def prefixEnd_605248 : Nat := 4983230072969 + 3 ^ 40 * 605248 * 2
def baseEnd_605248 : Nat := 310783139172553198116521

theorem tailTrace_605248 : CollatzResearch.WordTrace tailWord_605248 prefixEnd_605248 310783139172553198116521 := by
  unfold tailWord_605248
  simp only [CollatzResearch.WordTrace]
  refine ⟨11037604055648669486976199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14716805407531559315968265 11037604055648669486976199)
  ·
    refine ⟨16556406083473004230464299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11037604055648669486976199 16556406083473004230464299)
    ·
      refine ⟨24834609125209506345696449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16556406083473004230464299 24834609125209506345696449)
      ·
        refine ⟨18625956843907129759272337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24834609125209506345696449 18625956843907129759272337)
        ·
          refine ⟨13969467632930347319454253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18625956843907129759272337 13969467632930347319454253)
          ·
            refine ⟨5238550362348880244795345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13969467632930347319454253 5238550362348880244795345)
            ·
              refine ⟨3928912771761660183596509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5238550362348880244795345 3928912771761660183596509)
              ·
                refine ⟨1473342289410622568848691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3928912771761660183596509 1473342289410622568848691)
                ·
                  refine ⟨2210013434115933853273037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1473342289410622568848691 2210013434115933853273037)
                  ·
                    refine ⟨828755037793475194977389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2210013434115933853273037 828755037793475194977389)
                    ·
                      refine ⟨310783139172553198116521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 828755037793475194977389 310783139172553198116521)
                      ·
                        rfl

theorem cell23_605248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_605248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605248 prefixEnd_605248 := by exact prefixLift 605248
  have htrace : WordTrace (prefixWord ++ tailWord_605248) baseStart_605248 baseEnd_605248 := by
    simpa [prefixWord, tailWord_605248, baseEnd_605248] using wordTrace_append hprefix tailTrace_605248
  have hstable : (prefixWord ++ tailWord_605248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605248).length < 2 ^ (prefixWord ++ tailWord_605248).sum := by decide
  have hdescent : baseEnd_605248 < baseStart_605248 := by decide
  rcases family_descends (prefixWord ++ tailWord_605248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605249 : List Nat := [1, 2, 5, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_605249 : Nat := 118140960795 + 605249 * 2 ^ 59
def prefixEnd_605249 : Nat := 4983230072969 + 3 ^ 40 * 605249 * 2
def baseEnd_605249 : Nat := 310783652653207694204017

theorem tailTrace_605249 : CollatzResearch.WordTrace tailWord_605249 prefixEnd_605249 310783652653207694204017 := by
  unfold tailWord_605249
  simp only [CollatzResearch.WordTrace]
  refine ⟨22075244584293716144738801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14716829722862477429825867 22075244584293716144738801)
  ·
    refine ⟨16556433438220287108554101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22075244584293716144738801 16556433438220287108554101)
    ·
      refine ⟨1552165634833151916426947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16556433438220287108554101 1552165634833151916426947)
      ·
        refine ⟨2328248452249727874640421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1552165634833151916426947 2328248452249727874640421)
        ·
          refine ⟨436546584796823976495079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2328248452249727874640421 436546584796823976495079)
          ·
            refine ⟨654819877195235964742619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436546584796823976495079 654819877195235964742619)
            ·
              refine ⟨982229815792853947113929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654819877195235964742619 982229815792853947113929)
              ·
                refine ⟨736672361844640460335447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982229815792853947113929 736672361844640460335447)
                ·
                  refine ⟨1105008542766960690503171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 736672361844640460335447 1105008542766960690503171)
                  ·
                    refine ⟨1657512814150441035754757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1105008542766960690503171 1657512814150441035754757)
                    ·
                      refine ⟨310783652653207694204017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1657512814150441035754757 310783652653207694204017)
                      ·
                        rfl

theorem cell23_605249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_605249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605249 prefixEnd_605249 := by exact prefixLift 605249
  have htrace : WordTrace (prefixWord ++ tailWord_605249) baseStart_605249 baseEnd_605249 := by
    simpa [prefixWord, tailWord_605249, baseEnd_605249] using wordTrace_append hprefix tailTrace_605249
  have hstable : (prefixWord ++ tailWord_605249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605249).length < 2 ^ (prefixWord ++ tailWord_605249).sum := by decide
  have hdescent : baseEnd_605249 < baseStart_605249 := by decide
  rcases family_descends (prefixWord ++ tailWord_605249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605298 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 2, 6]
def baseStart_605298 : Nat := 118140960795 + 605298 * 2 ^ 59
def prefixEnd_605298 : Nat := 4983230072969 + 3 ^ 40 * 605298 * 2
def baseEnd_605298 : Nat := 103602937735092667497097

theorem tailTrace_605298 : CollatzResearch.WordTrace tailWord_605298 prefixEnd_605298 103602937735092667497097 := by
  unfold tailWord_605298
  simp only [CollatzResearch.WordTrace]
  refine ⟨5519257940279049378318137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14718021174077465008848365 5519257940279049378318137)
  ·
    refine ⟨4139443455209287033738603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5519257940279049378318137 4139443455209287033738603)
    ·
      refine ⟨6209165182813930550607905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4139443455209287033738603 6209165182813930550607905)
      ·
        refine ⟨4656873887110447912955929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6209165182813930550607905 4656873887110447912955929)
        ·
          refine ⟨3492655415332835934716947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4656873887110447912955929 3492655415332835934716947)
          ·
            refine ⟨5238983122999253902075421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3492655415332835934716947 5238983122999253902075421)
            ·
              refine ⟨1964618671124720213278283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5238983122999253902075421 1964618671124720213278283)
              ·
                refine ⟨2946928006687080319917425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1964618671124720213278283 2946928006687080319917425)
                ·
                  refine ⟨2210196005015310239938069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2946928006687080319917425 2210196005015310239938069)
                  ·
                    refine ⟨103602937735092667497097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2210196005015310239938069 103602937735092667497097)
                    ·
                      rfl

theorem cell23_605298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_605298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605298 prefixEnd_605298 := by exact prefixLift 605298
  have htrace : WordTrace (prefixWord ++ tailWord_605298) baseStart_605298 baseEnd_605298 := by
    simpa [prefixWord, tailWord_605298, baseEnd_605298] using wordTrace_append hprefix tailTrace_605298
  have hstable : (prefixWord ++ tailWord_605298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605298).length < 2 ^ (prefixWord ++ tailWord_605298).sum := by decide
  have hdescent : baseEnd_605298 < baseStart_605298 := by decide
  rcases family_descends (prefixWord ++ tailWord_605298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605308 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 2, 4, 3]
def baseStart_605308 : Nat := 118140960795 + 605308 * 2 ^ 59
def prefixEnd_605308 : Nat := 4983230072969 + 3 ^ 40 * 605308 * 2
def baseEnd_605308 : Nat := 310813948011822963366245

theorem tailTrace_605308 : CollatzResearch.WordTrace tailWord_605308 prefixEnd_605308 310813948011822963366245 := by
  unfold tailWord_605308
  simp only [CollatzResearch.WordTrace]
  refine ⟨11038698245539984610568289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14718264327386646147424385 11038698245539984610568289)
  ·
    refine ⟨8279023684154988457926217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11038698245539984610568289 8279023684154988457926217)
    ·
      refine ⟨6209267763116241343444663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8279023684154988457926217 6209267763116241343444663)
      ·
        refine ⟨9313901644674362015166995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6209267763116241343444663 9313901644674362015166995)
        ·
          refine ⟨13970852467011543022750493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9313901644674362015166995 13970852467011543022750493)
          ·
            refine ⟨5239069675129328633531435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13970852467011543022750493 5239069675129328633531435)
            ·
              refine ⟨7858604512693992950297153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5239069675129328633531435 7858604512693992950297153)
              ·
                refine ⟨5893953384520494712722865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7858604512693992950297153 5893953384520494712722865)
                ·
                  refine ⟨4420465038390371034542149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5893953384520494712722865 4420465038390371034542149)
                  ·
                    refine ⟨828837194698194568976653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4420465038390371034542149 828837194698194568976653)
                    ·
                      refine ⟨310813948011822963366245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 828837194698194568976653 310813948011822963366245)
                      ·
                        rfl

theorem cell23_605308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_605308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605308 prefixEnd_605308 := by exact prefixLift 605308
  have htrace : WordTrace (prefixWord ++ tailWord_605308) baseStart_605308 baseEnd_605308 := by
    simpa [prefixWord, tailWord_605308, baseEnd_605308] using wordTrace_append hprefix tailTrace_605308
  have hstable : (prefixWord ++ tailWord_605308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605308).length < 2 ^ (prefixWord ++ tailWord_605308).sum := by decide
  have hdescent : baseEnd_605308 < baseStart_605308 := by decide
  rcases family_descends (prefixWord ++ tailWord_605308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605322 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 4, 2, 2]
def baseStart_605322 : Nat := 118140960795 + 605322 * 2 ^ 59
def prefixEnd_605322 : Nat := 4983230072969 + 3 ^ 40 * 605322 * 2
def baseEnd_605322 : Nat := 310821136740985908591181

theorem tailTrace_605322 : CollatzResearch.WordTrace tailWord_605322 prefixEnd_605322 310821136740985908591181 := by
  unfold tailWord_605322
  simp only [CollatzResearch.WordTrace]
  refine ⟨5519476778257312403036555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14718604742019499741430813 5519476778257312403036555)
  ·
    refine ⟨8279215167385968604554833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5519476778257312403036555 8279215167385968604554833)
    ·
      refine ⟨6209411375539476453416125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8279215167385968604554833 6209411375539476453416125)
      ·
        refine ⟨2328529265827303670031047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6209411375539476453416125 2328529265827303670031047)
        ·
          refine ⟨3492793898740955505046571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2328529265827303670031047 3492793898740955505046571)
          ·
            refine ⟨5239190848111433257569857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3492793898740955505046571 5239190848111433257569857)
            ·
              refine ⟨3929393136083574943177393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5239190848111433257569857 3929393136083574943177393)
              ·
                refine ⟨2947044852062681207383045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3929393136083574943177393 2947044852062681207383045)
                ·
                  refine ⟨552570909761752726384321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2947044852062681207383045 552570909761752726384321)
                  ·
                    refine ⟨414428182321314544788241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 552570909761752726384321 414428182321314544788241)
                    ·
                      refine ⟨310821136740985908591181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 414428182321314544788241 310821136740985908591181)
                      ·
                        rfl

theorem cell23_605322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_605322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605322 prefixEnd_605322 := by exact prefixLift 605322
  have htrace : WordTrace (prefixWord ++ tailWord_605322) baseStart_605322 baseEnd_605322 := by
    simpa [prefixWord, tailWord_605322, baseEnd_605322] using wordTrace_append hprefix tailTrace_605322
  have hstable : (prefixWord ++ tailWord_605322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605322).length < 2 ^ (prefixWord ++ tailWord_605322).sum := by decide
  have hdescent : baseEnd_605322 < baseStart_605322 := by decide
  rcases family_descends (prefixWord ++ tailWord_605322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605326 : List Nat := [4, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2]
def baseStart_605326 : Nat := 118140960795 + 605326 * 2 ^ 59
def prefixEnd_605326 : Nat := 4983230072969 + 3 ^ 40 * 605326 * 2
def baseEnd_605326 : Nat := 310823190663603892941163

theorem tailTrace_605326 : CollatzResearch.WordTrace tailWord_605326 prefixEnd_605326 310823190663603892941163 := by
  unfold tailWord_605326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2759756625626844786911479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14718702003343172196861221 2759756625626844786911479)
  ·
    refine ⟨4139634938440267180367219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2759756625626844786911479 4139634938440267180367219)
    ·
      refine ⟨6209452407660400770550829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4139634938440267180367219 6209452407660400770550829)
      ·
        refine ⟨2328544652872650288956561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6209452407660400770550829 2328544652872650288956561)
        ·
          refine ⟨1746408489654487716717421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2328544652872650288956561 1746408489654487716717421)
          ·
            refine ⟨654903183620432893769033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1746408489654487716717421 654903183620432893769033)
            ·
              refine ⟨491177387715324670326775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 654903183620432893769033 491177387715324670326775)
              ·
                refine ⟨736766081572987005490163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491177387715324670326775 736766081572987005490163)
                ·
                  refine ⟨1105149122359480508235245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 736766081572987005490163 1105149122359480508235245)
                  ·
                    refine ⟨414430920884805190588217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1105149122359480508235245 414430920884805190588217)
                    ·
                      refine ⟨310823190663603892941163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 414430920884805190588217 310823190663603892941163)
                      ·
                        rfl

theorem cell23_605326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_605326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605326 prefixEnd_605326 := by exact prefixLift 605326
  have htrace : WordTrace (prefixWord ++ tailWord_605326) baseStart_605326 baseEnd_605326 := by
    simpa [prefixWord, tailWord_605326, baseEnd_605326] using wordTrace_append hprefix tailTrace_605326
  have hstable : (prefixWord ++ tailWord_605326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605326).length < 2 ^ (prefixWord ++ tailWord_605326).sum := by decide
  have hdescent : baseEnd_605326 < baseStart_605326 := by decide
  rcases family_descends (prefixWord ++ tailWord_605326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605345 : List Nat := [1, 2, 3, 3, 1, 1, 1, 6, 5]
def baseStart_605345 : Nat := 118140960795 + 605345 * 2 ^ 59
def prefixEnd_605345 : Nat := 4983230072969 + 3 ^ 40 * 605345 * 2
def baseEnd_605345 : Nat := 34536994088448813178175

theorem tailTrace_605345 : CollatzResearch.WordTrace tailWord_605345 prefixEnd_605345 34536994088448813178175 := by
  unfold tailWord_605345
  simp only [CollatzResearch.WordTrace]
  refine ⟨22078745991945924540233489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14719163994630616360155659 22078745991945924540233489)
  ·
    refine ⟨16559059493959443405175117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22078745991945924540233489 16559059493959443405175117)
    ·
      refine ⟨6209647310234791276940669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16559059493959443405175117 6209647310234791276940669)
      ·
        refine ⟨2328617741338046728852751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6209647310234791276940669 2328617741338046728852751)
        ·
          refine ⟨3492926612007070093279127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2328617741338046728852751 3492926612007070093279127)
          ·
            refine ⟨5239389918010605139918691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3492926612007070093279127 5239389918010605139918691)
            ·
              refine ⟨7859084877015907709878037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5239389918010605139918691 7859084877015907709878037)
              ·
                refine ⟨368394603610120673900533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7859084877015907709878037 368394603610120673900533)
                ·
                  refine ⟨34536994088448813178175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 368394603610120673900533 34536994088448813178175)
                  ·
                    rfl

theorem cell23_605345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 5].length) (baseStart_605345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605345 prefixEnd_605345 := by exact prefixLift 605345
  have htrace : WordTrace (prefixWord ++ tailWord_605345) baseStart_605345 baseEnd_605345 := by
    simpa [prefixWord, tailWord_605345, baseEnd_605345] using wordTrace_append hprefix tailTrace_605345
  have hstable : (prefixWord ++ tailWord_605345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605345).length < 2 ^ (prefixWord ++ tailWord_605345).sum := by decide
  have hdescent : baseEnd_605345 < baseStart_605345 := by decide
  rcases family_descends (prefixWord ++ tailWord_605345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605396 : List Nat := [2, 4, 1, 4, 1, 1, 3, 2, 5]
def baseStart_605396 : Nat := 118140960795 + 605396 * 2 ^ 59
def prefixEnd_605396 : Nat := 4983230072969 + 3 ^ 40 * 605396 * 2
def baseEnd_605396 : Nat := 34539903812157624340649

theorem tailTrace_605396 : CollatzResearch.WordTrace tailWord_605396 prefixEnd_605396 34539903812157624340649 := by
  unfold tailWord_605396
  simp only [CollatzResearch.WordTrace]
  refine ⟨11040303057380580125170021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14720404076507440166893361 11040303057380580125170021)
  ·
    refine ⟨2070056823258858773469379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11040303057380580125170021 2070056823258858773469379)
    ·
      refine ⟨3105085234888288160204069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2070056823258858773469379 3105085234888288160204069)
      ·
        refine ⟨582203481541554030038263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3105085234888288160204069 582203481541554030038263)
        ·
          refine ⟨873305222312331045057395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582203481541554030038263 873305222312331045057395)
          ·
            refine ⟨1309957833468496567586093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873305222312331045057395 1309957833468496567586093)
            ·
              refine ⟨491234187550686212844785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1309957833468496567586093 491234187550686212844785)
              ·
                refine ⟨368425640663014659633589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491234187550686212844785 368425640663014659633589)
                ·
                  refine ⟨34539903812157624340649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 368425640663014659633589 34539903812157624340649)
                  ·
                    rfl

theorem cell23_605396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_605396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605396 prefixEnd_605396 := by exact prefixLift 605396
  have htrace : WordTrace (prefixWord ++ tailWord_605396) baseStart_605396 baseEnd_605396 := by
    simpa [prefixWord, tailWord_605396, baseEnd_605396] using wordTrace_append hprefix tailTrace_605396
  have hstable : (prefixWord ++ tailWord_605396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605396).length < 2 ^ (prefixWord ++ tailWord_605396).sum := by decide
  have hdescent : baseEnd_605396 < baseStart_605396 := by decide
  rcases family_descends (prefixWord ++ tailWord_605396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605455 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 5, 5, 2]
def baseStart_605455 : Nat := 118140960795 + 605455 * 2 ^ 59
def prefixEnd_605455 : Nat := 4983230072969 + 3 ^ 40 * 605455 * 2
def baseEnd_605455 : Nat := 310889429668033888228069

theorem tailTrace_605455 : CollatzResearch.WordTrace tailWord_605455 prefixEnd_605455 310889429668033888228069 := by
  unfold tailWord_605455
  simp only [CollatzResearch.WordTrace]
  refine ⟨22082758021547413326737819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14721838681031608884491879 22082758021547413326737819)
  ·
    refine ⟨33124137032321119990106729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22082758021547413326737819 33124137032321119990106729)
    ·
      refine ⟨24843102774240839992580047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33124137032321119990106729 24843102774240839992580047)
      ·
        refine ⟨37264654161361259988870071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24843102774240839992580047 37264654161361259988870071)
        ·
          refine ⟨55896981242041889983305107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37264654161361259988870071 55896981242041889983305107)
          ·
            refine ⟨83845471863062834974957661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55896981242041889983305107 83845471863062834974957661)
            ·
              refine ⟨31442051948648563115609123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83845471863062834974957661 31442051948648563115609123)
              ·
                refine ⟨47163077922972844673413685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31442051948648563115609123 47163077922972844673413685)
                ·
                  refine ⟨4421538555278704188132533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47163077922972844673413685 4421538555278704188132533)
                  ·
                    refine ⟨414519239557378517637425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4421538555278704188132533 414519239557378517637425)
                    ·
                      refine ⟨310889429668033888228069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 414519239557378517637425 310889429668033888228069)
                      ·
                        rfl

theorem cell23_605455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 5, 2].length) (baseStart_605455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605455 prefixEnd_605455 := by exact prefixLift 605455
  have htrace : WordTrace (prefixWord ++ tailWord_605455) baseStart_605455 baseEnd_605455 := by
    simpa [prefixWord, tailWord_605455, baseEnd_605455] using wordTrace_append hprefix tailTrace_605455
  have hstable : (prefixWord ++ tailWord_605455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605455).length < 2 ^ (prefixWord ++ tailWord_605455).sum := by decide
  have hdescent : baseEnd_605455 < baseStart_605455 := by decide
  rcases family_descends (prefixWord ++ tailWord_605455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605482 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 3, 5]
def baseStart_605482 : Nat := 118140960795 + 605482 * 2 ^ 59
def prefixEnd_605482 : Nat := 4983230072969 + 3 ^ 40 * 605482 * 2
def baseEnd_605482 : Nat := 103634431215235094196815

theorem tailTrace_605482 : CollatzResearch.WordTrace tailWord_605482 prefixEnd_605482 103634431215235094196815 := by
  unfold tailWord_605482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5520935698112399234492675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14722495194966397958647133 5520935698112399234492675)
  ·
    refine ⟨8281403547168598851739013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5520935698112399234492675 8281403547168598851739013)
    ·
      refine ⟨1552763165094112284701065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8281403547168598851739013 1552763165094112284701065)
      ·
        refine ⟨1164572373820584213525799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1552763165094112284701065 1164572373820584213525799)
        ·
          refine ⟨1746858560730876320288699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164572373820584213525799 1746858560730876320288699)
          ·
            refine ⟨2620287841096314480433049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746858560730876320288699 2620287841096314480433049)
            ·
              refine ⟨1965215880822235860324787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2620287841096314480433049 1965215880822235860324787)
              ·
                refine ⟨2947823821233353790487181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1965215880822235860324787 2947823821233353790487181)
                ·
                  refine ⟨1105433932962507671432693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2947823821233353790487181 1105433932962507671432693)
                  ·
                    refine ⟨103634431215235094196815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1105433932962507671432693 103634431215235094196815)
                    ·
                      rfl

theorem cell23_605482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_605482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605482 prefixEnd_605482 := by exact prefixLift 605482
  have htrace : WordTrace (prefixWord ++ tailWord_605482) baseStart_605482 baseEnd_605482 := by
    simpa [prefixWord, tailWord_605482, baseEnd_605482] using wordTrace_append hprefix tailTrace_605482
  have hstable : (prefixWord ++ tailWord_605482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605482).length < 2 ^ (prefixWord ++ tailWord_605482).sum := by decide
  have hdescent : baseEnd_605482 < baseStart_605482 := by decide
  rcases family_descends (prefixWord ++ tailWord_605482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605489 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 2, 3, 2]
def baseStart_605489 : Nat := 118140960795 + 605489 * 2 ^ 59
def prefixEnd_605489 : Nat := 4983230072969 + 3 ^ 40 * 605489 * 2
def baseEnd_605489 : Nat := 310906888010286755202913

theorem tailTrace_605489 : CollatzResearch.WordTrace tailWord_605489 prefixEnd_605489 310906888010286755202913 := by
  unfold tailWord_605489
  simp only [CollatzResearch.WordTrace]
  refine ⟨22083998103424237133475521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14722665402282824755650347 22083998103424237133475521)
  ·
    refine ⟨16562998577568177850106641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22083998103424237133475521 16562998577568177850106641)
    ·
      refine ⟨12422248933176133387579981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16562998577568177850106641 12422248933176133387579981)
      ·
        refine ⟨4658343349941050020342493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12422248933176133387579981 4658343349941050020342493)
        ·
          refine ⟨1746878756227893757628435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4658343349941050020342493 1746878756227893757628435)
          ·
            refine ⟨2620318134341840636442653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746878756227893757628435 2620318134341840636442653)
            ·
              refine ⟨982619300378190238665995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2620318134341840636442653 982619300378190238665995)
              ·
                refine ⟨1473928950567285357998993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982619300378190238665995 1473928950567285357998993)
                ·
                  refine ⟨1105446712925464018499245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1473928950567285357998993 1105446712925464018499245)
                  ·
                    refine ⟨414542517347049006937217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1105446712925464018499245 414542517347049006937217)
                    ·
                      refine ⟨310906888010286755202913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 414542517347049006937217 310906888010286755202913)
                      ·
                        rfl

theorem cell23_605489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_605489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605489 prefixEnd_605489 := by exact prefixLift 605489
  have htrace : WordTrace (prefixWord ++ tailWord_605489) baseStart_605489 baseEnd_605489 := by
    simpa [prefixWord, tailWord_605489, baseEnd_605489] using wordTrace_append hprefix tailTrace_605489
  have hstable : (prefixWord ++ tailWord_605489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605489).length < 2 ^ (prefixWord ++ tailWord_605489).sum := by decide
  have hdescent : baseEnd_605489 < baseStart_605489 := by decide
  rcases family_descends (prefixWord ++ tailWord_605489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605533 : List Nat := [1, 4, 5, 1, 1, 1, 2, 2, 1, 5]
def baseStart_605533 : Nat := 118140960795 + 605533 * 2 ^ 59
def prefixEnd_605533 : Nat := 4983230072969 + 3 ^ 40 * 605533 * 2
def baseEnd_605533 : Nat := 103643160386361527684237

theorem tailTrace_605533 : CollatzResearch.WordTrace tailWord_605533 prefixEnd_605533 103643160386361527684237 := by
  unfold tailWord_605533
  simp only [CollatzResearch.WordTrace]
  refine ⟨22085602915264832648077253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14723735276843221765384835 22085602915264832648077253)
  ·
    refine ⟨4141050546612156121514485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22085602915264832648077253 4141050546612156121514485)
    ·
      refine ⟨388223488744889636391983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4141050546612156121514485 388223488744889636391983)
      ·
        refine ⟨582335233117334454587975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388223488744889636391983 582335233117334454587975)
        ·
          refine ⟨873502849676001681881963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582335233117334454587975 873502849676001681881963)
          ·
            refine ⟨1310254274514002522822945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873502849676001681881963 1310254274514002522822945)
            ·
              refine ⟨982690705885501892117209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1310254274514002522822945 982690705885501892117209)
              ·
                refine ⟨737018029414126419087907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982690705885501892117209 737018029414126419087907)
                ·
                  refine ⟨1105527044121189628631861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737018029414126419087907 1105527044121189628631861)
                  ·
                    refine ⟨103643160386361527684237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1105527044121189628631861 103643160386361527684237)
                    ·
                      rfl

theorem cell23_605533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_605533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605533 prefixEnd_605533 := by exact prefixLift 605533
  have htrace : WordTrace (prefixWord ++ tailWord_605533) baseStart_605533 baseEnd_605533 := by
    simpa [prefixWord, tailWord_605533, baseEnd_605533] using wordTrace_append hprefix tailTrace_605533
  have hstable : (prefixWord ++ tailWord_605533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605533).length < 2 ^ (prefixWord ++ tailWord_605533).sum := by decide
  have hdescent : baseEnd_605533 < baseStart_605533 := by decide
  rcases family_descends (prefixWord ++ tailWord_605533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605539 : List Nat := [1, 1, 1, 5, 2, 3, 2, 2, 1, 2, 3]
def baseStart_605539 : Nat := 118140960795 + 605539 * 2 ^ 59
def prefixEnd_605539 : Nat := 4983230072969 + 3 ^ 40 * 605539 * 2
def baseEnd_605539 : Nat := 310932562043011559577683

theorem tailTrace_605539 : CollatzResearch.WordTrace tailWord_605539 prefixEnd_605539 310932562043011559577683 := by
  unfold tailWord_605539
  simp only [CollatzResearch.WordTrace]
  refine ⟨22085821753243095672795671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14723881168828730448530447 22085821753243095672795671)
  ·
    refine ⟨33128732629864643509193507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22085821753243095672795671 33128732629864643509193507)
    ·
      refine ⟨49693098944796965263790261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33128732629864643509193507 49693098944796965263790261)
      ·
        refine ⟨4658728026074715493480337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49693098944796965263790261 4658728026074715493480337)
        ·
          refine ⟨3494046019556036620110253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4658728026074715493480337 3494046019556036620110253)
          ·
            refine ⟨1310267257333513732541345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3494046019556036620110253 1310267257333513732541345)
            ·
              refine ⟨982700443000135299406009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1310267257333513732541345 982700443000135299406009)
              ·
                refine ⟨737025332250101474554507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982700443000135299406009 737025332250101474554507)
                ·
                  refine ⟨1105537998375152211831761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737025332250101474554507 1105537998375152211831761)
                  ·
                    refine ⟨829153498781364158873821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1105537998375152211831761 829153498781364158873821)
                    ·
                      refine ⟨310932562043011559577683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 829153498781364158873821 310932562043011559577683)
                      ·
                        rfl

theorem cell23_605539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_605539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605539 prefixEnd_605539 := by exact prefixLift 605539
  have htrace : WordTrace (prefixWord ++ tailWord_605539) baseStart_605539 baseEnd_605539 := by
    simpa [prefixWord, tailWord_605539, baseEnd_605539] using wordTrace_append hprefix tailTrace_605539
  have hstable : (prefixWord ++ tailWord_605539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605539).length < 2 ^ (prefixWord ++ tailWord_605539).sum := by decide
  have hdescent : baseEnd_605539 < baseStart_605539 := by decide
  rcases family_descends (prefixWord ++ tailWord_605539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605552 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 6, 1, 3]
def baseStart_605552 : Nat := 118140960795 + 605552 * 2 ^ 59
def prefixEnd_605552 : Nat := 4983230072969 + 3 ^ 40 * 605552 * 2
def baseEnd_605552 : Nat := 310939237291520008715123

theorem tailTrace_605552 : CollatzResearch.WordTrace tailWord_605552 prefixEnd_605552 310939237291520008715123 := by
  unfold tailWord_605552
  simp only [CollatzResearch.WordTrace]
  refine ⟨11043147951097999446509455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14724197268130665928679273 11043147951097999446509455)
  ·
    refine ⟨16564721926646999169764183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11043147951097999446509455 16564721926646999169764183)
    ·
      refine ⟨24847082889970498754646275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16564721926646999169764183 24847082889970498754646275)
      ·
        refine ⟨37270624334955748131969413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24847082889970498754646275 37270624334955748131969413)
        ·
          refine ⟨6988242062804202774744265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37270624334955748131969413 6988242062804202774744265)
          ·
            refine ⟨5241181547103152081058199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6988242062804202774744265 5241181547103152081058199)
            ·
              refine ⟨7861772320654728121587299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5241181547103152081058199 7861772320654728121587299)
              ·
                refine ⟨11792658480982092182380949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7861772320654728121587299 11792658480982092182380949)
                ·
                  refine ⟨552780866296035571049107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11792658480982092182380949 552780866296035571049107)
                  ·
                    refine ⟨829171299444053356573661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 552780866296035571049107 829171299444053356573661)
                    ·
                      refine ⟨310939237291520008715123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 829171299444053356573661 310939237291520008715123)
                      ·
                        rfl

theorem cell23_605552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 6, 1, 3].length) (baseStart_605552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605552 prefixEnd_605552 := by exact prefixLift 605552
  have htrace : WordTrace (prefixWord ++ tailWord_605552) baseStart_605552 baseEnd_605552 := by
    simpa [prefixWord, tailWord_605552, baseEnd_605552] using wordTrace_append hprefix tailTrace_605552
  have hstable : (prefixWord ++ tailWord_605552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605552).length < 2 ^ (prefixWord ++ tailWord_605552).sum := by decide
  have hdescent : baseEnd_605552 < baseStart_605552 := by decide
  rcases family_descends (prefixWord ++ tailWord_605552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605565 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_605565 : Nat := 118140960795 + 605565 * 2 ^ 59
def prefixEnd_605565 : Nat := 4983230072969 + 3 ^ 40 * 605565 * 2
def baseEnd_605565 : Nat := 310945912540028457852563

theorem tailTrace_605565 : CollatzResearch.WordTrace tailWord_605565 prefixEnd_605565 310945912540028457852563 := by
  unfold tailWord_605565
  simp only [CollatzResearch.WordTrace]
  refine ⟨22086770051148902113242149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14724513367432601408828099 22086770051148902113242149)
  ·
    refine ⟨4141269384590419146232903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22086770051148902113242149 4141269384590419146232903)
    ·
      refine ⟨6211904076885628719349355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4141269384590419146232903 6211904076885628719349355)
      ·
        refine ⟨9317856115328443079024033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6211904076885628719349355 9317856115328443079024033)
        ·
          refine ⟨6988392086496332309268025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9317856115328443079024033 6988392086496332309268025)
          ·
            refine ⟨5241294064872249231951019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6988392086496332309268025 5241294064872249231951019)
            ·
              refine ⟨7861941097308373847926529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5241294064872249231951019 7861941097308373847926529)
              ·
                refine ⟨5896455822981280385944897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7861941097308373847926529 5896455822981280385944897)
                ·
                  refine ⟨4422341867235960289458673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5896455822981280385944897 4422341867235960289458673)
                  ·
                    refine ⟨3316756400426970217094005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4422341867235960289458673 3316756400426970217094005)
                    ·
                      refine ⟨310945912540028457852563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3316756400426970217094005 310945912540028457852563)
                      ·
                        rfl

theorem cell23_605565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_605565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605565 prefixEnd_605565 := by exact prefixLift 605565
  have htrace : WordTrace (prefixWord ++ tailWord_605565) baseStart_605565 baseEnd_605565 := by
    simpa [prefixWord, tailWord_605565, baseEnd_605565] using wordTrace_append hprefix tailTrace_605565
  have hstable : (prefixWord ++ tailWord_605565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605565).length < 2 ^ (prefixWord ++ tailWord_605565).sum := by decide
  have hdescent : baseEnd_605565 < baseStart_605565 := by decide
  rcases family_descends (prefixWord ++ tailWord_605565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605570 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_605570 : Nat := 118140960795 + 605570 * 2 ^ 59
def prefixEnd_605570 : Nat := 4983230072969 + 3 ^ 40 * 605570 * 2
def baseEnd_605570 : Nat := 310948479943300938290041

theorem tailTrace_605570 : CollatzResearch.WordTrace tailWord_605570 prefixEnd_605570 310948479943300938290041 := by
  unfold tailWord_605570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5521738104032696991793541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14724634944087191978116109 5521738104032696991793541)
  ·
    refine ⟨1035325894506130685961289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5521738104032696991793541 1035325894506130685961289)
    ·
      refine ⟨776494420879598014470967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1035325894506130685961289 776494420879598014470967)
      ·
        refine ⟨1164741631319397021706451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 776494420879598014470967 1164741631319397021706451)
        ·
          refine ⟨1747112446979095532559677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164741631319397021706451 1747112446979095532559677)
          ·
            refine ⟨655167167617160824709879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1747112446979095532559677 655167167617160824709879)
            ·
              refine ⟨982750751425741237064819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655167167617160824709879 982750751425741237064819)
              ·
                refine ⟨1474126127138611855597229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982750751425741237064819 1474126127138611855597229)
                ·
                  refine ⟨552797297676979445848961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1474126127138611855597229 552797297676979445848961)
                  ·
                    refine ⟨414597973257734584386721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 552797297676979445848961 414597973257734584386721)
                    ·
                      refine ⟨310948479943300938290041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 414597973257734584386721 310948479943300938290041)
                      ·
                        rfl

theorem cell23_605570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_605570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605570 prefixEnd_605570 := by exact prefixLift 605570
  have htrace : WordTrace (prefixWord ++ tailWord_605570) baseStart_605570 baseEnd_605570 := by
    simpa [prefixWord, tailWord_605570, baseEnd_605570] using wordTrace_append hprefix tailTrace_605570
  have hstable : (prefixWord ++ tailWord_605570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605570).length < 2 ^ (prefixWord ++ tailWord_605570).sum := by decide
  have hdescent : baseEnd_605570 < baseStart_605570 := by decide
  rcases family_descends (prefixWord ++ tailWord_605570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605595 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 3]
def baseStart_605595 : Nat := 118140960795 + 605595 * 2 ^ 59
def prefixEnd_605595 : Nat := 4983230072969 + 3 ^ 40 * 605595 * 2
def baseEnd_605595 : Nat := 310961316959663340477425

theorem tailTrace_605595 : CollatzResearch.WordTrace tailWord_605595 prefixEnd_605595 310961316959663340477425 := by
  unfold tailWord_605595
  simp only [CollatzResearch.WordTrace]
  refine ⟨22087864241040217236834239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14725242827360144824556159 22087864241040217236834239)
  ·
    refine ⟨33131796361560325855251359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22087864241040217236834239 33131796361560325855251359)
    ·
      refine ⟨49697694542340488782877039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33131796361560325855251359 49697694542340488782877039)
      ·
        refine ⟨74546541813510733174315559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49697694542340488782877039 74546541813510733174315559)
        ·
          refine ⟨111819812720266099761473339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74546541813510733174315559 111819812720266099761473339)
          ·
            refine ⟨167729719080399149642210009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111819812720266099761473339 167729719080399149642210009)
            ·
              refine ⟨125797289310299362231657507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167729719080399149642210009 125797289310299362231657507)
              ·
                refine ⟨188695933965449043347486261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125797289310299362231657507 188695933965449043347486261)
                ·
                  refine ⟨17690243809260847813826837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188695933965449043347486261 17690243809260847813826837)
                  ·
                    refine ⟨829230178559102241273133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17690243809260847813826837 829230178559102241273133)
                    ·
                      refine ⟨310961316959663340477425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 829230178559102241273133 310961316959663340477425)
                      ·
                        rfl

theorem cell23_605595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 3].length) (baseStart_605595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605595 prefixEnd_605595 := by exact prefixLift 605595
  have htrace : WordTrace (prefixWord ++ tailWord_605595) baseStart_605595 baseEnd_605595 := by
    simpa [prefixWord, tailWord_605595, baseEnd_605595] using wordTrace_append hprefix tailTrace_605595
  have hstable : (prefixWord ++ tailWord_605595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605595).length < 2 ^ (prefixWord ++ tailWord_605595).sum := by decide
  have hdescent : baseEnd_605595 < baseStart_605595 := by decide
  rcases family_descends (prefixWord ++ tailWord_605595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605605 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 3, 4, 4]
def baseStart_605605 : Nat := 118140960795 + 605605 * 2 ^ 59
def prefixEnd_605605 : Nat := 4983230072969 + 3 ^ 40 * 605605 * 2
def baseEnd_605605 : Nat := 310966451766208301352379

theorem tailTrace_605605 : CollatzResearch.WordTrace tailWord_605605 prefixEnd_605605 310966451766208301352379 := by
  unfold tailWord_605605
  simp only [CollatzResearch.WordTrace]
  refine ⟨22088228971003988944698269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14725485980669325963132179 22088228971003988944698269)
  ·
    refine ⟨8283085864126495854261851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22088228971003988944698269 8283085864126495854261851)
    ·
      refine ⟨12424628796189743781392777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8283085864126495854261851 12424628796189743781392777)
      ·
        refine ⟨9318471597142307836044583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12424628796189743781392777 9318471597142307836044583)
        ·
          refine ⟨13977707395713461754066875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9318471597142307836044583 13977707395713461754066875)
          ·
            refine ⟨20966561093570192631100313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13977707395713461754066875 20966561093570192631100313)
            ·
              refine ⟨15724920820177644473325235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20966561093570192631100313 15724920820177644473325235)
              ·
                refine ⟨23587381230266466709987853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15724920820177644473325235 23587381230266466709987853)
                ·
                  refine ⟨8845267961349925016245445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23587381230266466709987853 8845267961349925016245445)
                  ·
                    refine ⟨1658487742753110940546021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8845267961349925016245445 1658487742753110940546021)
                    ·
                      refine ⟨310966451766208301352379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1658487742753110940546021 310966451766208301352379)
                      ·
                        rfl

theorem cell23_605605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_605605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605605 prefixEnd_605605 := by exact prefixLift 605605
  have htrace : WordTrace (prefixWord ++ tailWord_605605) baseStart_605605 baseEnd_605605 := by
    simpa [prefixWord, tailWord_605605, baseEnd_605605] using wordTrace_append hprefix tailTrace_605605
  have hstable : (prefixWord ++ tailWord_605605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605605).length < 2 ^ (prefixWord ++ tailWord_605605).sum := by decide
  have hdescent : baseEnd_605605 < baseStart_605605 := by decide
  rcases family_descends (prefixWord ++ tailWord_605605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605642 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 1, 5, 3]
def baseStart_605642 : Nat := 118140960795 + 605642 * 2 ^ 59
def prefixEnd_605642 : Nat := 4983230072969 + 3 ^ 40 * 605642 * 2
def baseEnd_605642 : Nat := 310985450550424656589709

theorem tailTrace_605642 : CollatzResearch.WordTrace tailWord_605642 prefixEnd_605642 310985450550424656589709 := by
  unfold tailWord_605642
  simp only [CollatzResearch.WordTrace]
  refine ⟨5522394617967486065948795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14726385647913296175863453 5522394617967486065948795)
  ·
    refine ⟨8283591926951229098923193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5522394617967486065948795 8283591926951229098923193)
    ·
      refine ⟨6212693945213421824192395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8283591926951229098923193 6212693945213421824192395)
      ·
        refine ⟨9319040917820132736288593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6212693945213421824192395 9319040917820132736288593)
        ·
          refine ⟨6989280688365099552216445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9319040917820132736288593 6989280688365099552216445)
          ·
            refine ⟨2620980258136912332081167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6989280688365099552216445 2620980258136912332081167)
            ·
              refine ⟨3931470387205368498121751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2620980258136912332081167 3931470387205368498121751)
              ·
                refine ⟨5897205580808052747182627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3931470387205368498121751 5897205580808052747182627)
                ·
                  refine ⟨8845808371212079120773941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5897205580808052747182627 8845808371212079120773941)
                  ·
                    refine ⟨829294534801132417572557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8845808371212079120773941 829294534801132417572557)
                    ·
                      refine ⟨310985450550424656589709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 829294534801132417572557 310985450550424656589709)
                      ·
                        rfl

theorem cell23_605642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_605642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605642 prefixEnd_605642 := by exact prefixLift 605642
  have htrace : WordTrace (prefixWord ++ tailWord_605642) baseStart_605642 baseEnd_605642 := by
    simpa [prefixWord, tailWord_605642, baseEnd_605642] using wordTrace_append hprefix tailTrace_605642
  have hstable : (prefixWord ++ tailWord_605642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605642).length < 2 ^ (prefixWord ++ tailWord_605642).sum := by decide
  have hdescent : baseEnd_605642 < baseStart_605642 := by decide
  rcases family_descends (prefixWord ++ tailWord_605642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605655 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 7]
def baseStart_605655 : Nat := 118140960795 + 605655 * 2 ^ 59
def prefixEnd_605655 : Nat := 4983230072969 + 3 ^ 40 * 605655 * 2
def baseEnd_605655 : Nat := 310992125798933105727149

theorem tailTrace_605655 : CollatzResearch.WordTrace tailWord_605655 prefixEnd_605655 310992125798933105727149 := by
  unfold tailWord_605655
  simp only [CollatzResearch.WordTrace]
  refine ⟨22090052620822847484018419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14726701747215231656012279 22090052620822847484018419)
  ·
    refine ⟨33135078931234271226027629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22090052620822847484018419 33135078931234271226027629)
    ·
      refine ⟨12425654599212851709760361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33135078931234271226027629 12425654599212851709760361)
      ·
        refine ⟨9319240949409638782320271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12425654599212851709760361 9319240949409638782320271)
        ·
          refine ⟨13978861424114458173480407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9319240949409638782320271 13978861424114458173480407)
          ·
            refine ⟨20968292136171687260220611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13978861424114458173480407 20968292136171687260220611)
            ·
              refine ⟨31452438204257530890330917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20968292136171687260220611 31452438204257530890330917)
              ·
                refine ⟨5897332163298287041937047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31452438204257530890330917 5897332163298287041937047)
                ·
                  refine ⟨8845998244947430562905571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5897332163298287041937047 8845998244947430562905571)
                  ·
                    refine ⟨13268997367421145844358357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8845998244947430562905571 13268997367421145844358357)
                    ·
                      refine ⟨310992125798933105727149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13268997367421145844358357 310992125798933105727149)
                      ·
                        rfl

theorem cell23_605655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_605655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605655 prefixEnd_605655 := by exact prefixLift 605655
  have htrace : WordTrace (prefixWord ++ tailWord_605655) baseStart_605655 baseEnd_605655 := by
    simpa [prefixWord, tailWord_605655, baseEnd_605655] using wordTrace_append hprefix tailTrace_605655
  have hstable : (prefixWord ++ tailWord_605655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605655).length < 2 ^ (prefixWord ++ tailWord_605655).sum := by decide
  have hdescent : baseEnd_605655 < baseStart_605655 := by decide
  rcases family_descends (prefixWord ++ tailWord_605655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605677 : List Nat := [1, 5, 1, 3, 3, 1, 1, 2, 2, 2, 2]
def baseStart_605677 : Nat := 118140960795 + 605677 * 2 ^ 59
def prefixEnd_605677 : Nat := 4983230072969 + 3 ^ 40 * 605677 * 2
def baseEnd_605677 : Nat := 311003422373332019652049

theorem tailTrace_605677 : CollatzResearch.WordTrace tailWord_605677 prefixEnd_605677 311003422373332019652049 := by
  unfold tailWord_605677
  simp only [CollatzResearch.WordTrace]
  refine ⟨22090855026743145241319285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14727236684495430160879523 22090855026743145241319285)
  ·
    refine ⟨2071017658757169866373683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22090855026743145241319285 2071017658757169866373683)
    ·
      refine ⟨3106526488135754799560525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2071017658757169866373683 3106526488135754799560525)
      ·
        refine ⟨1164947433050908049835197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3106526488135754799560525 1164947433050908049835197)
        ·
          refine ⟨436855287394090518688199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1164947433050908049835197 436855287394090518688199)
          ·
            refine ⟨655282931091135778032299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436855287394090518688199 655282931091135778032299)
            ·
              refine ⟨982924396636703667048449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655282931091135778032299 982924396636703667048449)
              ·
                refine ⟨737193297477527750286337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982924396636703667048449 737193297477527750286337)
                ·
                  refine ⟨552894973108145812714753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 737193297477527750286337 552894973108145812714753)
                  ·
                    refine ⟨414671229831109359536065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 552894973108145812714753 414671229831109359536065)
                    ·
                      refine ⟨311003422373332019652049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 414671229831109359536065 311003422373332019652049)
                      ·
                        rfl

theorem cell23_605677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_605677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605677 prefixEnd_605677 := by exact prefixLift 605677
  have htrace : WordTrace (prefixWord ++ tailWord_605677) baseStart_605677 baseEnd_605677 := by
    simpa [prefixWord, tailWord_605677, baseEnd_605677] using wordTrace_append hprefix tailTrace_605677
  have hstable : (prefixWord ++ tailWord_605677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605677).length < 2 ^ (prefixWord ++ tailWord_605677).sum := by decide
  have hdescent : baseEnd_605677 < baseStart_605677 := by decide
  rcases family_descends (prefixWord ++ tailWord_605677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605776 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 2, 3, 2]
def baseStart_605776 : Nat := 118140960795 + 605776 * 2 ^ 59
def prefixEnd_605776 : Nat := 4983230072969 + 3 ^ 40 * 605776 * 2
def baseEnd_605776 : Nat := 311054256958127132314093

theorem tailTrace_605776 : CollatzResearch.WordTrace tailWord_605776 prefixEnd_605776 311054256958127132314093 := by
  unfold tailWord_605776
  simp only [CollatzResearch.WordTrace]
  refine ⟨11047232926692242574586591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14729643902256323432782121 11047232926692242574586591)
  ·
    refine ⟨16570849390038363861879887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11047232926692242574586591 16570849390038363861879887)
    ·
      refine ⟨24856274085057545792819831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16570849390038363861879887 24856274085057545792819831)
      ·
        refine ⟨37284411127586318689229747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24856274085057545792819831 37284411127586318689229747)
        ·
          refine ⟨55926616691379478033844621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37284411127586318689229747 55926616691379478033844621)
          ·
            refine ⟨20972481259267304262691733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55926616691379478033844621 20972481259267304262691733)
            ·
              refine ⟨983085059028154887313675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20972481259267304262691733 983085059028154887313675)
              ·
                refine ⟨1474627588542232330970513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983085059028154887313675 1474627588542232330970513)
                ·
                  refine ⟨1105970691406674248227885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1474627588542232330970513 1105970691406674248227885)
                  ·
                    refine ⟨414739009277502843085457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1105970691406674248227885 414739009277502843085457)
                    ·
                      refine ⟨311054256958127132314093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 414739009277502843085457 311054256958127132314093)
                      ·
                        rfl

theorem cell23_605776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 2, 3, 2].length) (baseStart_605776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605776 prefixEnd_605776 := by exact prefixLift 605776
  have htrace : WordTrace (prefixWord ++ tailWord_605776) baseStart_605776 baseEnd_605776 := by
    simpa [prefixWord, tailWord_605776, baseEnd_605776] using wordTrace_append hprefix tailTrace_605776
  have hstable : (prefixWord ++ tailWord_605776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605776).length < 2 ^ (prefixWord ++ tailWord_605776).sum := by decide
  have hdescent : baseEnd_605776 < baseStart_605776 := by decide
  rcases family_descends (prefixWord ++ tailWord_605776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605799 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 4, 4]
def baseStart_605799 : Nat := 118140960795 + 605799 * 2 ^ 59
def prefixEnd_605799 : Nat := 4983230072969 + 3 ^ 40 * 605799 * 2
def baseEnd_605799 : Nat := 103688689004393514108829

theorem tailTrace_605799 : CollatzResearch.WordTrace tailWord_605799 prefixEnd_605799 103688689004393514108829 := by
  unfold tailWord_605799
  simp only [CollatzResearch.WordTrace]
  refine ⟨22095304732301160077260451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14730203154867440051506967 22095304732301160077260451)
  ·
    refine ⟨33142957098451740115890677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22095304732301160077260451 33142957098451740115890677)
    ·
      refine ⟨3107152227979850635864751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33142957098451740115890677 3107152227979850635864751)
      ·
        refine ⟨4660728341969775953797127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3107152227979850635864751 4660728341969775953797127)
        ·
          refine ⟨6991092512954663930695691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4660728341969775953797127 6991092512954663930695691)
          ·
            refine ⟨10486638769431995896043537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6991092512954663930695691 10486638769431995896043537)
            ·
              refine ⟨7864979077073996922032653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10486638769431995896043537 7864979077073996922032653)
              ·
                refine ⟨2949367153902748845762245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7864979077073996922032653 2949367153902748845762245)
                ·
                  refine ⟨553006341356765408580421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2949367153902748845762245 553006341356765408580421)
                  ·
                    refine ⟨103688689004393514108829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 553006341356765408580421 103688689004393514108829)
                    ·
                      rfl

theorem cell23_605799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_605799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605799 prefixEnd_605799 := by exact prefixLift 605799
  have htrace : WordTrace (prefixWord ++ tailWord_605799) baseStart_605799 baseEnd_605799 := by
    simpa [prefixWord, tailWord_605799, baseEnd_605799] using wordTrace_append hprefix tailTrace_605799
  have hstable : (prefixWord ++ tailWord_605799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605799).length < 2 ^ (prefixWord ++ tailWord_605799).sum := by decide
  have hdescent : baseEnd_605799 < baseStart_605799 := by decide
  rcases family_descends (prefixWord ++ tailWord_605799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605800 : List Nat := [2, 1, 4, 3, 1, 2, 1, 4, 1, 1, 3]
def baseStart_605800 : Nat := 118140960795 + 605800 * 2 ^ 59
def prefixEnd_605800 : Nat := 4983230072969 + 3 ^ 40 * 605800 * 2
def baseEnd_605800 : Nat := 311066580493835038413983

theorem tailTrace_605800 : CollatzResearch.WordTrace tailWord_605800 prefixEnd_605800 311066580493835038413983 := by
  unfold tailWord_605800
  simp only [CollatzResearch.WordTrace]
  refine ⟨11047670602648768624023427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14730227470198358165364569 11047670602648768624023427)
  ·
    refine ⟨16571505903973152936035141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11047670602648768624023427 16571505903973152936035141)
    ·
      refine ⟨3107157356994966175506589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16571505903973152936035141 3107157356994966175506589)
      ·
        refine ⟨1165184008873112315814971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3107157356994966175506589 1165184008873112315814971)
        ·
          refine ⟨1747776013309668473722457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1165184008873112315814971 1747776013309668473722457)
          ·
            refine ⟨1310832009982251355291843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1747776013309668473722457 1310832009982251355291843)
            ·
              refine ⟨1966248014973377032937765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1310832009982251355291843 1966248014973377032937765)
              ·
                refine ⟨368671502807508193675831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1966248014973377032937765 368671502807508193675831)
                ·
                  refine ⟨553007254211262290513747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368671502807508193675831 553007254211262290513747)
                  ·
                    refine ⟨829510881316893435770621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 553007254211262290513747 829510881316893435770621)
                    ·
                      refine ⟨311066580493835038413983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 829510881316893435770621 311066580493835038413983)
                      ·
                        rfl

theorem cell23_605800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_605800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605800 prefixEnd_605800 := by exact prefixLift 605800
  have htrace : WordTrace (prefixWord ++ tailWord_605800) baseStart_605800 baseEnd_605800 := by
    simpa [prefixWord, tailWord_605800, baseEnd_605800] using wordTrace_append hprefix tailTrace_605800
  have hstable : (prefixWord ++ tailWord_605800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605800).length < 2 ^ (prefixWord ++ tailWord_605800).sum := by decide
  have hdescent : baseEnd_605800 < baseStart_605800 := by decide
  rcases family_descends (prefixWord ++ tailWord_605800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605819 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 4]
def baseStart_605819 : Nat := 118140960795 + 605819 * 2 ^ 59
def prefixEnd_605819 : Nat := 4983230072969 + 3 ^ 40 * 605819 * 2
def baseEnd_605819 : Nat := 311076336626270464076395

theorem tailTrace_605819 : CollatzResearch.WordTrace tailWord_605819 prefixEnd_605819 311076336626270464076395 := by
  unfold tailWord_605819
  simp only [CollatzResearch.WordTrace]
  refine ⟨22096034192228703492988511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14730689461485802328659007 22096034192228703492988511)
  ·
    refine ⟨33144051288343055239482767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22096034192228703492988511 33144051288343055239482767)
    ·
      refine ⟨49716076932514582859224151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33144051288343055239482767 49716076932514582859224151)
      ·
        refine ⟨74574115398771874288836227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49716076932514582859224151 74574115398771874288836227)
        ·
          refine ⟨111861173098157811433254341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74574115398771874288836227 111861173098157811433254341)
          ·
            refine ⟨20973969955904589643735189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111861173098157811433254341 20973969955904589643735189)
            ·
              refine ⟨983154841683027639550087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20973969955904589643735189 983154841683027639550087)
              ·
                refine ⟨1474732262524541459325131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983154841683027639550087 1474732262524541459325131)
                ·
                  refine ⟨2212098393786812188987697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474732262524541459325131 2212098393786812188987697)
                  ·
                    refine ⟨1659073795340109141740773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2212098393786812188987697 1659073795340109141740773)
                    ·
                      refine ⟨311076336626270464076395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1659073795340109141740773 311076336626270464076395)
                      ·
                        rfl

theorem cell23_605819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 4].length) (baseStart_605819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605819 prefixEnd_605819 := by exact prefixLift 605819
  have htrace : WordTrace (prefixWord ++ tailWord_605819) baseStart_605819 baseEnd_605819 := by
    simpa [prefixWord, tailWord_605819, baseEnd_605819] using wordTrace_append hprefix tailTrace_605819
  have hstable : (prefixWord ++ tailWord_605819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605819).length < 2 ^ (prefixWord ++ tailWord_605819).sum := by decide
  have hdescent : baseEnd_605819 < baseStart_605819 := by decide
  rcases family_descends (prefixWord ++ tailWord_605819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605829 : List Nat := [1, 3, 1, 1, 4, 1, 5, 7]
def baseStart_605829 : Nat := 118140960795 + 605829 * 2 ^ 59
def prefixEnd_605829 : Nat := 4983230072969 + 3 ^ 40 * 605829 * 2
def baseEnd_605829 : Nat := 11521535978993163887087

theorem tailTrace_605829 : CollatzResearch.WordTrace tailWord_605829 prefixEnd_605829 11521535978993163887087 := by
  unfold tailWord_605829
  simp only [CollatzResearch.WordTrace]
  refine ⟨22096398922192475200852541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14730932614794983467235027 22096398922192475200852541)
  ·
    refine ⟨8286149595822178200319703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22096398922192475200852541 8286149595822178200319703)
    ·
      refine ⟨12429224393733267300479555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8286149595822178200319703 12429224393733267300479555)
      ·
        refine ⟨18643836590599900950719333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12429224393733267300479555 18643836590599900950719333)
        ·
          refine ⟨3495719360737481428259875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18643836590599900950719333 3495719360737481428259875)
          ·
            refine ⟨5243579041106222142389813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3495719360737481428259875 5243579041106222142389813)
            ·
              refine ⟨491585535103708325849045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5243579041106222142389813 491585535103708325849045)
              ·
                refine ⟨11521535978993163887087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 491585535103708325849045 11521535978993163887087)
                ·
                  rfl

theorem cell23_605829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 7].length) (baseStart_605829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605829 prefixEnd_605829 := by exact prefixLift 605829
  have htrace : WordTrace (prefixWord ++ tailWord_605829) baseStart_605829 baseEnd_605829 := by
    simpa [prefixWord, tailWord_605829, baseEnd_605829] using wordTrace_append hprefix tailTrace_605829
  have hstable : (prefixWord ++ tailWord_605829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605829).length < 2 ^ (prefixWord ++ tailWord_605829).sum := by decide
  have hdescent : baseEnd_605829 < baseStart_605829 := by decide
  rcases family_descends (prefixWord ++ tailWord_605829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605870 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_605870 : Nat := 118140960795 + 605870 * 2 ^ 59
def prefixEnd_605870 : Nat := 4983230072969 + 3 ^ 40 * 605870 * 2
def baseEnd_605870 : Nat := 311102524139649764538661

theorem tailTrace_605870 : CollatzResearch.WordTrace tailWord_605870 prefixEnd_605870 311102524139649764538661 := by
  unfold tailWord_605870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2762236789380492400386883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14731929543362626135396709 2762236789380492400386883)
  ·
    refine ⟨4143355184070738600580325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2762236789380492400386883 4143355184070738600580325)
    ·
      refine ⟨776879097013263487608811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4143355184070738600580325 776879097013263487608811)
      ·
        refine ⟨1165318645519895231413217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 776879097013263487608811 1165318645519895231413217)
        ·
          refine ⟨873988984139921423559913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1165318645519895231413217 873988984139921423559913)
          ·
            refine ⟨655491738104941067669935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 873988984139921423559913 655491738104941067669935)
            ·
              refine ⟨983237607157411601504903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655491738104941067669935 983237607157411601504903)
              ·
                refine ⟨1474856410736117402257355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983237607157411601504903 1474856410736117402257355)
                ·
                  refine ⟨2212284616104176103386033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474856410736117402257355 2212284616104176103386033)
                  ·
                    refine ⟨1659213462078132077539525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2212284616104176103386033 1659213462078132077539525)
                    ·
                      refine ⟨311102524139649764538661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1659213462078132077539525 311102524139649764538661)
                      ·
                        rfl

theorem cell23_605870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_605870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605870 prefixEnd_605870 := by exact prefixLift 605870
  have htrace : WordTrace (prefixWord ++ tailWord_605870) baseStart_605870 baseEnd_605870 := by
    simpa [prefixWord, tailWord_605870, baseEnd_605870] using wordTrace_append hprefix tailTrace_605870
  have hstable : (prefixWord ++ tailWord_605870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605870).length < 2 ^ (prefixWord ++ tailWord_605870).sum := by decide
  have hdescent : baseEnd_605870 < baseStart_605870 := by decide
  rcases family_descends (prefixWord ++ tailWord_605870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605896 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 3, 4, 2]
def baseStart_605896 : Nat := 118140960795 + 605896 * 2 ^ 59
def prefixEnd_605896 : Nat := 4983230072969 + 3 ^ 40 * 605896 * 2
def baseEnd_605896 : Nat := 311115874636666662813541

theorem tailTrace_605896 : CollatzResearch.WordTrace tailWord_605896 prefixEnd_605896 311115874636666662813541 := by
  unfold tailWord_605896
  simp only [CollatzResearch.WordTrace]
  refine ⟨11049421306474872821770771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14732561741966497095694361 11049421306474872821770771)
  ·
    refine ⟨16574131959712309232656157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11049421306474872821770771 16574131959712309232656157)
    ·
      refine ⟨6215299484892115962246059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16574131959712309232656157 6215299484892115962246059)
      ·
        refine ⟨9322949227338173943369089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6215299484892115962246059 9322949227338173943369089)
        ·
          refine ⟨6992211920503630457526817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9322949227338173943369089 6992211920503630457526817)
          ·
            refine ⟨5244158940377722843145113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6992211920503630457526817 5244158940377722843145113)
            ·
              refine ⟨3933119205283292132358835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5244158940377722843145113 3933119205283292132358835)
              ·
                refine ⟨5899678807924938198538253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3933119205283292132358835 5899678807924938198538253)
                ·
                  refine ⟨2212379552971851824451845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5899678807924938198538253 2212379552971851824451845)
                  ·
                    refine ⟨414821166182222217084721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2212379552971851824451845 414821166182222217084721)
                    ·
                      refine ⟨311115874636666662813541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 414821166182222217084721 311115874636666662813541)
                      ·
                        rfl

theorem cell23_605896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_605896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605896 prefixEnd_605896 := by exact prefixLift 605896
  have htrace : WordTrace (prefixWord ++ tailWord_605896) baseStart_605896 baseEnd_605896 := by
    simpa [prefixWord, tailWord_605896, baseEnd_605896] using wordTrace_append hprefix tailTrace_605896
  have hstable : (prefixWord ++ tailWord_605896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605896).length < 2 ^ (prefixWord ++ tailWord_605896).sum := by decide
  have hdescent : baseEnd_605896 < baseStart_605896 := by decide
  rcases family_descends (prefixWord ++ tailWord_605896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605913 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 4, 2, 2]
def baseStart_605913 : Nat := 118140960795 + 605913 * 2 ^ 59
def prefixEnd_605913 : Nat := 4983230072969 + 3 ^ 40 * 605913 * 2
def baseEnd_605913 : Nat := 311124603807793096300963

theorem tailTrace_605913 : CollatzResearch.WordTrace tailWord_605913 prefixEnd_605913 311124603807793096300963 := by
  unfold tailWord_605913
  simp only [CollatzResearch.WordTrace]
  refine ⟨22099462653888157546910393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14732975102592105031273595 22099462653888157546910393)
  ·
    refine ⟨16574596990416118160182795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22099462653888157546910393 16574596990416118160182795)
    ·
      refine ⟨24861895485624177240274193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16574596990416118160182795 24861895485624177240274193)
      ·
        refine ⟨18646421614218132930205645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24861895485624177240274193 18646421614218132930205645)
        ·
          refine ⟨6992408105331799848827117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18646421614218132930205645 6992408105331799848827117)
          ·
            refine ⟨2622153039499424943310169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6992408105331799848827117 2622153039499424943310169)
            ·
              refine ⟨1966614779624568707482627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2622153039499424943310169 1966614779624568707482627)
              ·
                refine ⟨2949922169436853061223941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1966614779624568707482627 2949922169436853061223941)
                ·
                  refine ⟨553110406769409948979489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2949922169436853061223941 553110406769409948979489)
                  ·
                    refine ⟨414832805077057461734617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 553110406769409948979489 414832805077057461734617)
                    ·
                      refine ⟨311124603807793096300963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 414832805077057461734617 311124603807793096300963)
                      ·
                        rfl

theorem cell23_605913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 2, 2].length) (baseStart_605913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605913 prefixEnd_605913 := by exact prefixLift 605913
  have htrace : WordTrace (prefixWord ++ tailWord_605913) baseStart_605913 baseEnd_605913 := by
    simpa [prefixWord, tailWord_605913, baseEnd_605913] using wordTrace_append hprefix tailTrace_605913
  have hstable : (prefixWord ++ tailWord_605913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605913).length < 2 ^ (prefixWord ++ tailWord_605913).sum := by decide
  have hdescent : baseEnd_605913 < baseStart_605913 := by decide
  rcases family_descends (prefixWord ++ tailWord_605913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605929 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 1, 5, 3]
def baseStart_605929 : Nat := 118140960795 + 605929 * 2 ^ 59
def prefixEnd_605929 : Nat := 4983230072969 + 3 ^ 40 * 605929 * 2
def baseEnd_605929 : Nat := 311132819498265033700889

theorem tailTrace_605929 : CollatzResearch.WordTrace tailWord_605929 prefixEnd_605929 311132819498265033700889 := by
  unfold tailWord_605929
  simp only [CollatzResearch.WordTrace]
  refine ⟨22100046221830192279492841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14733364147886794852995227 22100046221830192279492841)
  ·
    refine ⟨16575034666372644209619631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22100046221830192279492841 16575034666372644209619631)
    ·
      refine ⟨24862551999558966314429447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16575034666372644209619631 24862551999558966314429447)
      ·
        refine ⟨37293827999338449471644171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24862551999558966314429447 37293827999338449471644171)
        ·
          refine ⟨55940741999007674207466257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37293827999338449471644171 55940741999007674207466257)
          ·
            refine ⟨41955556499255755655599693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55940741999007674207466257 41955556499255755655599693)
            ·
              refine ⟨15733333687220908370849885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41955556499255755655599693 15733333687220908370849885)
              ·
                refine ⟨5900000132707840639068707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15733333687220908370849885 5900000132707840639068707)
                ·
                  refine ⟨8850000199061760958603061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5900000132707840639068707 8850000199061760958603061)
                  ·
                    refine ⟨829687518662040089869037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8850000199061760958603061 829687518662040089869037)
                    ·
                      refine ⟨311132819498265033700889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 829687518662040089869037 311132819498265033700889)
                      ·
                        rfl

theorem cell23_605929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 5, 3].length) (baseStart_605929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605929 prefixEnd_605929 := by exact prefixLift 605929
  have htrace : WordTrace (prefixWord ++ tailWord_605929) baseStart_605929 baseEnd_605929 := by
    simpa [prefixWord, tailWord_605929, baseEnd_605929] using wordTrace_append hprefix tailTrace_605929
  have hstable : (prefixWord ++ tailWord_605929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605929).length < 2 ^ (prefixWord ++ tailWord_605929).sum := by decide
  have hdescent : baseEnd_605929 < baseStart_605929 := by decide
  rcases family_descends (prefixWord ++ tailWord_605929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605958 : List Nat := [6, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_605958 : Nat := 118140960795 + 605958 * 2 ^ 59
def prefixEnd_605958 : Nat := 4983230072969 + 3 ^ 40 * 605958 * 2
def baseEnd_605958 : Nat := 311147710437245420238257

theorem tailTrace_605958 : CollatzResearch.WordTrace tailWord_605958 prefixEnd_605958 311147710437245420238257 := by
  unfold tailWord_605958
  simp only [CollatzResearch.WordTrace]
  refine ⟨690659498085160319759329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14734069292483420154865685 690659498085160319759329)
  ·
    refine ⟨517994623563870239819497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 690659498085160319759329 517994623563870239819497)
    ·
      refine ⟨388495967672902679864623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 517994623563870239819497 388495967672902679864623)
      ·
        refine ⟨582743951509354019796935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388495967672902679864623 582743951509354019796935)
        ·
          refine ⟨874115927264031029695403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582743951509354019796935 874115927264031029695403)
          ·
            refine ⟨1311173890896046544543105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874115927264031029695403 1311173890896046544543105)
            ·
              refine ⟨983380418172034908407329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1311173890896046544543105 983380418172034908407329)
              ·
                refine ⟨737535313629026181305497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 983380418172034908407329 737535313629026181305497)
                ·
                  refine ⟨553151485221769635979123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 737535313629026181305497 553151485221769635979123)
                  ·
                    refine ⟨829727227832654453968685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 553151485221769635979123 829727227832654453968685)
                    ·
                      refine ⟨311147710437245420238257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 829727227832654453968685 311147710437245420238257)
                      ·
                        rfl

theorem cell23_605958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_605958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605958 prefixEnd_605958 := by exact prefixLift 605958
  have htrace : WordTrace (prefixWord ++ tailWord_605958) baseStart_605958 baseEnd_605958 := by
    simpa [prefixWord, tailWord_605958, baseEnd_605958] using wordTrace_append hprefix tailTrace_605958
  have hstable : (prefixWord ++ tailWord_605958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605958).length < 2 ^ (prefixWord ++ tailWord_605958).sum := by decide
  have hdescent : baseEnd_605958 < baseStart_605958 := by decide
  rcases family_descends (prefixWord ++ tailWord_605958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605966 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 2, 5]
def baseStart_605966 : Nat := 118140960795 + 605966 * 2 ^ 59
def prefixEnd_605966 : Nat := 4983230072969 + 3 ^ 40 * 605966 * 2
def baseEnd_605966 : Nat := 103717272760827129646073

theorem tailTrace_605966 : CollatzResearch.WordTrace tailWord_605966 prefixEnd_605966 103717272760827129646073 := by
  unfold tailWord_605966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2762674465337018449823719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14734263815130765065726501 2762674465337018449823719)
  ·
    refine ⟨4144011698005527674735579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2762674465337018449823719 4144011698005527674735579)
    ·
      refine ⟨6216017547008291512103369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4144011698005527674735579 6216017547008291512103369)
      ·
        refine ⟨4662013160256218634077527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6216017547008291512103369 4662013160256218634077527)
        ·
          refine ⟨6993019740384327951116291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4662013160256218634077527 6993019740384327951116291)
          ·
            refine ⟨10489529610576491926674437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6993019740384327951116291 10489529610576491926674437)
            ·
              refine ⟨1966786801983092236251457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10489529610576491926674437 1966786801983092236251457)
              ·
                refine ⟨1475090101487319177188593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1966786801983092236251457 1475090101487319177188593)
                ·
                  refine ⟨1106317576115489382891445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1475090101487319177188593 1106317576115489382891445)
                  ·
                    refine ⟨103717272760827129646073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1106317576115489382891445 103717272760827129646073)
                    ·
                      rfl

theorem cell23_605966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_605966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605966 prefixEnd_605966 := by exact prefixLift 605966
  have htrace : WordTrace (prefixWord ++ tailWord_605966) baseStart_605966 baseEnd_605966 := by
    simpa [prefixWord, tailWord_605966, baseEnd_605966] using wordTrace_append hprefix tailTrace_605966
  have hstable : (prefixWord ++ tailWord_605966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605966).length < 2 ^ (prefixWord ++ tailWord_605966).sum := by decide
  have hdescent : baseEnd_605966 < baseStart_605966 := by decide
  rcases family_descends (prefixWord ++ tailWord_605966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605969 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 4]
def baseStart_605969 : Nat := 118140960795 + 605969 * 2 ^ 59
def prefixEnd_605969 : Nat := 4983230072969 + 3 ^ 40 * 605969 * 2
def baseEnd_605969 : Nat := 311153358724444877200705

theorem tailTrace_605969 : CollatzResearch.WordTrace tailWord_605969 prefixEnd_605969 311153358724444877200705 := by
  unfold tailWord_605969
  simp only [CollatzResearch.WordTrace]
  refine ⟨22101505141685279110948961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14734336761123519407299307 22101505141685279110948961)
  ·
    refine ⟨16576128856263959333211721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22101505141685279110948961 16576128856263959333211721)
    ·
      refine ⟨12432096642197969499908791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16576128856263959333211721 12432096642197969499908791)
      ·
        refine ⟨18648144963296954249863187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12432096642197969499908791 18648144963296954249863187)
        ·
          refine ⟨27972217444945431374794781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18648144963296954249863187 27972217444945431374794781)
          ·
            refine ⟨10489581541854536765548043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27972217444945431374794781 10489581541854536765548043)
            ·
              refine ⟨15734372312781805148322065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10489581541854536765548043 15734372312781805148322065)
              ·
                refine ⟨11800779234586353861241549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15734372312781805148322065 11800779234586353861241549)
                ·
                  refine ⟨4425292212969882697965581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11800779234586353861241549 4425292212969882697965581)
                  ·
                    refine ⟨1659484579863706011737093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4425292212969882697965581 1659484579863706011737093)
                    ·
                      refine ⟨311153358724444877200705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1659484579863706011737093 311153358724444877200705)
                      ·
                        rfl

theorem cell23_605969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_605969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605969 prefixEnd_605969 := by exact prefixLift 605969
  have htrace : WordTrace (prefixWord ++ tailWord_605969) baseStart_605969 baseEnd_605969 := by
    simpa [prefixWord, tailWord_605969, baseEnd_605969] using wordTrace_append hprefix tailTrace_605969
  have hstable : (prefixWord ++ tailWord_605969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605969).length < 2 ^ (prefixWord ++ tailWord_605969).sum := by decide
  have hdescent : baseEnd_605969 < baseStart_605969 := by decide
  rcases family_descends (prefixWord ++ tailWord_605969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605970 : List Nat := [3, 2, 4, 1, 1, 2, 1, 4, 5]
def baseStart_605970 : Nat := 118140960795 + 605970 * 2 ^ 59
def prefixEnd_605970 : Nat := 4983230072969 + 3 ^ 40 * 605970 * 2
def baseEnd_605970 : Nat := 34572652467233263698689

theorem tailTrace_605970 : CollatzResearch.WordTrace tailWord_605970 prefixEnd_605970 34572652467233263698689 := by
  unfold tailWord_605970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5525385403670414070433841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14734361076454437521156909 5525385403670414070433841)
  ·
    refine ⟨4144039052752810552825381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5525385403670414070433841 4144039052752810552825381)
    ·
      refine ⟨777007322391151978654759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4144039052752810552825381 777007322391151978654759)
      ·
        refine ⟨1165510983586727967982139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 777007322391151978654759 1165510983586727967982139)
        ·
          refine ⟨1748266475380091951973209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1165510983586727967982139 1748266475380091951973209)
          ·
            refine ⟨1311199856535068963979907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1748266475380091951973209 1311199856535068963979907)
            ·
              refine ⟨1966799784802603445969861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1311199856535068963979907 1966799784802603445969861)
              ·
                refine ⟨368774959650488146119349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1966799784802603445969861 368774959650488146119349)
                ·
                  refine ⟨34572652467233263698689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 368774959650488146119349 34572652467233263698689)
                  ·
                    rfl

theorem cell23_605970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_605970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605970 prefixEnd_605970 := by exact prefixLift 605970
  have htrace : WordTrace (prefixWord ++ tailWord_605970) baseStart_605970 baseEnd_605970 := by
    simpa [prefixWord, tailWord_605970, baseEnd_605970] using wordTrace_append hprefix tailTrace_605970
  have hstable : (prefixWord ++ tailWord_605970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605970).length < 2 ^ (prefixWord ++ tailWord_605970).sum := by decide
  have hdescent : baseEnd_605970 < baseStart_605970 := by decide
  rcases family_descends (prefixWord ++ tailWord_605970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605986 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_605986 : Nat := 118140960795 + 605986 * 2 ^ 59
def prefixEnd_605986 : Nat := 4983230072969 + 3 ^ 40 * 605986 * 2
def baseEnd_605986 : Nat := 311162087895571310688127

theorem tailTrace_605986 : CollatzResearch.WordTrace tailWord_605986 prefixEnd_605986 311162087895571310688127 := by
  unfold tailWord_605986
  simp only [CollatzResearch.WordTrace]
  refine ⟨5525531295655922753579453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14734750121749127342878541 5525531295655922753579453)
  ·
    refine ⟨2072074235870971032592295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5525531295655922753579453 2072074235870971032592295)
    ·
      refine ⟨3108111353806456548888443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2072074235870971032592295 3108111353806456548888443)
      ·
        refine ⟨4662167030709684823332665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3108111353806456548888443 4662167030709684823332665)
        ·
          refine ⟨3496625273032263617499499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4662167030709684823332665 3496625273032263617499499)
          ·
            refine ⟨5244937909548395426249249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3496625273032263617499499 5244937909548395426249249)
            ·
              refine ⟨3933703432161296569686937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5244937909548395426249249 3933703432161296569686937)
              ·
                refine ⟨2950277574120972427265203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3933703432161296569686937 2950277574120972427265203)
                ·
                  refine ⟨4425416361181458640897805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2950277574120972427265203 4425416361181458640897805)
                  ·
                    refine ⟨1659531135443046990336677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4425416361181458640897805 1659531135443046990336677)
                    ·
                      refine ⟨311162087895571310688127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1659531135443046990336677 311162087895571310688127)
                      ·
                        rfl

theorem cell23_605986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_605986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605986 prefixEnd_605986 := by exact prefixLift 605986
  have htrace : WordTrace (prefixWord ++ tailWord_605986) baseStart_605986 baseEnd_605986 := by
    simpa [prefixWord, tailWord_605986, baseEnd_605986] using wordTrace_append hprefix tailTrace_605986
  have hstable : (prefixWord ++ tailWord_605986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605986).length < 2 ^ (prefixWord ++ tailWord_605986).sum := by decide
  have hdescent : baseEnd_605986 < baseStart_605986 := by decide
  rcases family_descends (prefixWord ++ tailWord_605986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605996 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 5, 4]
def baseStart_605996 : Nat := 118140960795 + 605996 * 2 ^ 59
def prefixEnd_605996 : Nat := 4983230072969 + 3 ^ 40 * 605996 * 2
def baseEnd_605996 : Nat := 103722407567372090521027

theorem tailTrace_605996 : CollatzResearch.WordTrace tailWord_605996 prefixEnd_605996 103722407567372090521027 := by
  unfold tailWord_605996
  simp only [CollatzResearch.WordTrace]
  refine ⟨11051244956293731361090921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14734993275058308481454561 11051244956293731361090921)
  ·
    refine ⟨8288433717220298520818191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11051244956293731361090921 8288433717220298520818191)
    ·
      refine ⟨12432650575830447781227287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8288433717220298520818191 12432650575830447781227287)
      ·
        refine ⟨18648975863745671671840931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12432650575830447781227287 18648975863745671671840931)
        ·
          refine ⟨27973463795618507507761397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18648975863745671671840931 27973463795618507507761397)
          ·
            refine ⟨2622512230839235078852631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27973463795618507507761397 2622512230839235078852631)
            ·
              refine ⟨3933768346258852618278947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2622512230839235078852631 3933768346258852618278947)
              ·
                refine ⟨5900652519388278927418421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3933768346258852618278947 5900652519388278927418421)
                ·
                  refine ⟨553186173692651149445477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5900652519388278927418421 553186173692651149445477)
                  ·
                    refine ⟨103722407567372090521027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 553186173692651149445477 103722407567372090521027)
                    ·
                      rfl

theorem cell23_605996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_605996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605996 prefixEnd_605996 := by exact prefixLift 605996
  have htrace : WordTrace (prefixWord ++ tailWord_605996) baseStart_605996 baseEnd_605996 := by
    simpa [prefixWord, tailWord_605996, baseEnd_605996] using wordTrace_append hprefix tailTrace_605996
  have hstable : (prefixWord ++ tailWord_605996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605996).length < 2 ^ (prefixWord ++ tailWord_605996).sum := by decide
  have hdescent : baseEnd_605996 < baseStart_605996 := by decide
  rcases family_descends (prefixWord ++ tailWord_605996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605999 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 4]
def baseStart_605999 : Nat := 118140960795 + 605999 * 2 ^ 59
def prefixEnd_605999 : Nat := 4983230072969 + 3 ^ 40 * 605999 * 2
def baseEnd_605999 : Nat := 311168763144079759825567

theorem tailTrace_605999 : CollatzResearch.WordTrace tailWord_605999 prefixEnd_605999 311168763144079759825567 := by
  unfold tailWord_605999
  simp only [CollatzResearch.WordTrace]
  refine ⟨22102599331576594234541051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14735066221051062823027367 22102599331576594234541051)
  ·
    refine ⟨33153898997364891351811577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22102599331576594234541051 33153898997364891351811577)
    ·
      refine ⟨24865424248023668513858683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33153898997364891351811577 24865424248023668513858683)
      ·
        refine ⟨37298136372035502770788025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24865424248023668513858683 37298136372035502770788025)
        ·
          refine ⟨27973602279026627078091019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37298136372035502770788025 27973602279026627078091019)
          ·
            refine ⟨41960403418539940617136529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27973602279026627078091019 41960403418539940617136529)
            ·
              refine ⟨31470302563904955462852397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41960403418539940617136529 31470302563904955462852397)
              ·
                refine ⟨11801363461464358298569649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31470302563904955462852397 11801363461464358298569649)
                ·
                  refine ⟨8851022596098268723927237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11801363461464358298569649 8851022596098268723927237)
                  ·
                    refine ⟨1659566736768425385736357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8851022596098268723927237 1659566736768425385736357)
                    ·
                      refine ⟨311168763144079759825567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1659566736768425385736357 311168763144079759825567)
                      ·
                        rfl

theorem cell23_605999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_605999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_605999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_605999 prefixEnd_605999 := by exact prefixLift 605999
  have htrace : WordTrace (prefixWord ++ tailWord_605999) baseStart_605999 baseEnd_605999 := by
    simpa [prefixWord, tailWord_605999, baseEnd_605999] using wordTrace_append hprefix tailTrace_605999
  have hstable : (prefixWord ++ tailWord_605999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605999).length < 2 ^ (prefixWord ++ tailWord_605999).sum := by decide
  have hdescent : baseEnd_605999 < baseStart_605999 := by decide
  rcases family_descends (prefixWord ++ tailWord_605999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606076 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_606076 : Nat := 118140960795 + 606076 * 2 ^ 59
def prefixEnd_606076 : Nat := 4983230072969 + 3 ^ 40 * 606076 * 2
def baseEnd_606076 : Nat := 311208301154475958562713

theorem tailTrace_606076 : CollatzResearch.WordTrace tailWord_606076 prefixEnd_606076 311208301154475958562713 := by
  unfold tailWord_606076
  simp only [CollatzResearch.WordTrace]
  refine ⟨11052703876148818192547041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14736938501531757590062721 11052703876148818192547041)
  ·
    refine ⟨8289527907111613644410281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11052703876148818192547041 8289527907111613644410281)
    ·
      refine ⟨6217145930333710233307711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8289527907111613644410281 6217145930333710233307711)
      ·
        refine ⟨9325718895500565349961567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6217145930333710233307711 9325718895500565349961567)
        ·
          refine ⟨13988578343250848024942351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9325718895500565349961567 13988578343250848024942351)
          ·
            refine ⟨20982867514876272037413527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13988578343250848024942351 20982867514876272037413527)
            ·
              refine ⟨31474301272314408056120291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20982867514876272037413527 31474301272314408056120291)
              ·
                refine ⟨47211451908471612084180437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31474301272314408056120291 47211451908471612084180437)
                ·
                  refine ⟨1106518404104803408222979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 47211451908471612084180437 1106518404104803408222979)
                  ·
                    refine ⟨1659777606157205112334469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1106518404104803408222979 1659777606157205112334469)
                    ·
                      refine ⟨311208301154475958562713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1659777606157205112334469 311208301154475958562713)
                      ·
                        rfl

theorem cell23_606076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_606076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606076 prefixEnd_606076 := by exact prefixLift 606076
  have htrace : WordTrace (prefixWord ++ tailWord_606076) baseStart_606076 baseEnd_606076 := by
    simpa [prefixWord, tailWord_606076, baseEnd_606076] using wordTrace_append hprefix tailTrace_606076
  have hstable : (prefixWord ++ tailWord_606076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606076).length < 2 ^ (prefixWord ++ tailWord_606076).sum := by decide
  have hdescent : baseEnd_606076 < baseStart_606076 := by decide
  rcases family_descends (prefixWord ++ tailWord_606076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606087 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 3, 1, 3]
def baseStart_606087 : Nat := 118140960795 + 606087 * 2 ^ 59
def prefixEnd_606087 : Nat := 4983230072969 + 3 ^ 40 * 606087 * 2
def baseEnd_606087 : Nat := 311213949441675415525163

theorem tailTrace_606087 : CollatzResearch.WordTrace tailWord_606087 prefixEnd_606087 311213949441675415525163 := by
  unfold tailWord_606087
  simp only [CollatzResearch.WordTrace]
  refine ⟨22105808955257785263744515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14737205970171856842496343 22105808955257785263744515)
  ·
    refine ⟨33158713432886677895616773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22105808955257785263744515 33158713432886677895616773)
    ·
      refine ⟨6217258768666252105428145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33158713432886677895616773 6217258768666252105428145)
      ·
        refine ⟨4662944076499689079071109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6217258768666252105428145 4662944076499689079071109)
        ·
          refine ⟨874302014343691702325833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4662944076499689079071109 874302014343691702325833)
          ·
            refine ⟨655726510757768776744375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 874302014343691702325833 655726510757768776744375)
            ·
              refine ⟨983589766136653165116563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655726510757768776744375 983589766136653165116563)
              ·
                refine ⟨1475384649204979747674845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983589766136653165116563 1475384649204979747674845)
                ·
                  refine ⟨553269243451867405378067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1475384649204979747674845 553269243451867405378067)
                  ·
                    refine ⟨829903865177801108067101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 553269243451867405378067 829903865177801108067101)
                    ·
                      refine ⟨311213949441675415525163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 829903865177801108067101 311213949441675415525163)
                      ·
                        rfl

theorem cell23_606087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_606087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606087 prefixEnd_606087 := by exact prefixLift 606087
  have htrace : WordTrace (prefixWord ++ tailWord_606087) baseStart_606087 baseEnd_606087 := by
    simpa [prefixWord, tailWord_606087, baseEnd_606087] using wordTrace_append hprefix tailTrace_606087
  have hstable : (prefixWord ++ tailWord_606087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606087).length < 2 ^ (prefixWord ++ tailWord_606087).sum := by decide
  have hdescent : baseEnd_606087 < baseStart_606087 := by decide
  rcases family_descends (prefixWord ++ tailWord_606087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606094 : List Nat := [4, 1, 1, 5, 2, 1, 2, 1, 6]
def baseStart_606094 : Nat := 118140960795 + 606094 * 2 ^ 59
def prefixEnd_606094 : Nat := 4983230072969 + 3 ^ 40 * 606094 * 2
def baseEnd_606094 : Nat := 34579727089584098681959

theorem tailTrace_606094 : CollatzResearch.WordTrace tailWord_606094 prefixEnd_606094 34579727089584098681959 := by
  unfold tailWord_606094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2763258033279053182406167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14737376177488283639499557 2763258033279053182406167)
  ·
    refine ⟨4144887049918579773609251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2763258033279053182406167 4144887049918579773609251)
    ·
      refine ⟨6217330574877869660413877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4144887049918579773609251 6217330574877869660413877)
      ·
        refine ⟨582874741394800280663801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6217330574877869660413877 582874741394800280663801)
        ·
          refine ⟨437156056046100210497851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 582874741394800280663801 437156056046100210497851)
          ·
            refine ⟨655734084069150315746777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437156056046100210497851 655734084069150315746777)
            ·
              refine ⟨491800563051862736810083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 655734084069150315746777 491800563051862736810083)
              ·
                refine ⟨737700844577794105215125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491800563051862736810083 737700844577794105215125)
                ·
                  refine ⟨34579727089584098681959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 737700844577794105215125 34579727089584098681959)
                  ·
                    rfl

theorem cell23_606094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_606094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606094 prefixEnd_606094 := by exact prefixLift 606094
  have htrace : WordTrace (prefixWord ++ tailWord_606094) baseStart_606094 baseEnd_606094 := by
    simpa [prefixWord, tailWord_606094, baseEnd_606094] using wordTrace_append hprefix tailTrace_606094
  have hstable : (prefixWord ++ tailWord_606094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606094).length < 2 ^ (prefixWord ++ tailWord_606094).sum := by decide
  have hdescent : baseEnd_606094 < baseStart_606094 := by decide
  rcases family_descends (prefixWord ++ tailWord_606094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606116 : List Nat := [2, 3, 1, 2, 1, 3, 2, 9]
def baseStart_606116 : Nat := 118140960795 + 606116 * 2 ^ 59
def prefixEnd_606116 : Nat := 4983230072969 + 3 ^ 40 * 606116 * 2
def baseEnd_606116 : Nat := 11526994088172437113427

theorem tailTrace_606116 : CollatzResearch.WordTrace tailWord_606116 prefixEnd_606116 11526994088172437113427 := by
  unfold tailWord_606116
  simp only [CollatzResearch.WordTrace]
  refine ⟨11053433336076361608275101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14737911114768482144366801 11053433336076361608275101)
  ·
    refine ⟨4145037501028635603103163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11053433336076361608275101 4145037501028635603103163)
    ·
      refine ⟨6217556251542953404654745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4145037501028635603103163 6217556251542953404654745)
      ·
        refine ⟨4663167188657215053491059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6217556251542953404654745 4663167188657215053491059)
        ·
          refine ⟨6994750782985822580236589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4663167188657215053491059 6994750782985822580236589)
          ·
            refine ⟨2623031543619683467588721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6994750782985822580236589 2623031543619683467588721)
            ·
              refine ⟨1967273657714762600691541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2623031543619683467588721 1967273657714762600691541)
              ·
                refine ⟨11526994088172437113427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1967273657714762600691541 11526994088172437113427)
                ·
                  rfl

theorem cell23_606116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 9].length) (baseStart_606116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606116 prefixEnd_606116 := by exact prefixLift 606116
  have htrace : WordTrace (prefixWord ++ tailWord_606116) baseStart_606116 baseEnd_606116 := by
    simpa [prefixWord, tailWord_606116, baseEnd_606116] using wordTrace_append hprefix tailTrace_606116
  have hstable : (prefixWord ++ tailWord_606116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606116).length < 2 ^ (prefixWord ++ tailWord_606116).sum := by decide
  have hdescent : baseEnd_606116 < baseStart_606116 := by decide
  rcases family_descends (prefixWord ++ tailWord_606116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606127 : List Nat := [1, 1, 2, 1, 2, 2, 4, 5, 1, 2, 2]
def baseStart_606127 : Nat := 118140960795 + 606127 * 2 ^ 59
def prefixEnd_606127 : Nat := 4983230072969 + 3 ^ 40 * 606127 * 2
def baseEnd_606127 : Nat := 311234488667855259024979

theorem tailTrace_606127 : CollatzResearch.WordTrace tailWord_606127 prefixEnd_606127 311234488667855259024979 := by
  unfold tailWord_606127
  simp only [CollatzResearch.WordTrace]
  refine ⟨22107267875112872095200635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14738178583408581396800423 22107267875112872095200635)
  ·
    refine ⟨33160901812669308142800953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22107267875112872095200635 33160901812669308142800953)
    ·
      refine ⟨24870676359501981107100715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33160901812669308142800953 24870676359501981107100715)
      ·
        refine ⟨37306014539252971660651073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24870676359501981107100715 37306014539252971660651073)
        ·
          refine ⟨27979510904439728745488305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37306014539252971660651073 27979510904439728745488305)
          ·
            refine ⟨20984633178329796559116229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27979510904439728745488305 20984633178329796559116229)
            ·
              refine ⟨3934618720936836854834293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20984633178329796559116229 3934618720936836854834293)
              ·
                refine ⟨368870505087828455140715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3934618720936836854834293 368870505087828455140715)
                ·
                  refine ⟨553305757631742682711073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368870505087828455140715 553305757631742682711073)
                  ·
                    refine ⟨414979318223807012033305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 553305757631742682711073 414979318223807012033305)
                    ·
                      refine ⟨311234488667855259024979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 414979318223807012033305 311234488667855259024979)
                      ·
                        rfl

theorem cell23_606127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 1, 2, 2].length) (baseStart_606127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606127 prefixEnd_606127 := by exact prefixLift 606127
  have htrace : WordTrace (prefixWord ++ tailWord_606127) baseStart_606127 baseEnd_606127 := by
    simpa [prefixWord, tailWord_606127, baseEnd_606127] using wordTrace_append hprefix tailTrace_606127
  have hstable : (prefixWord ++ tailWord_606127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606127).length < 2 ^ (prefixWord ++ tailWord_606127).sum := by decide
  have hdescent : baseEnd_606127 < baseStart_606127 := by decide
  rcases family_descends (prefixWord ++ tailWord_606127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606160 : List Nat := [2, 1, 1, 1, 1, 2, 6, 3, 2, 1, 3]
def baseStart_606160 : Nat := 118140960795 + 606160 * 2 ^ 59
def prefixEnd_606160 : Nat := 4983230072969 + 3 ^ 40 * 606160 * 2
def baseEnd_606160 : Nat := 311251433529453629912327

theorem tailTrace_606160 : CollatzResearch.WordTrace tailWord_606160 prefixEnd_606160 311251433529453629912327 := by
  unfold tailWord_606160
  simp only [CollatzResearch.WordTrace]
  refine ⟨11054235741996659365575967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14738980989328879154101289 11054235741996659365575967)
  ·
    refine ⟨16581353612994989048363951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11054235741996659365575967 16581353612994989048363951)
    ·
      refine ⟨24872030419492483572545927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16581353612994989048363951 24872030419492483572545927)
      ·
        refine ⟨37308045629238725358818891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24872030419492483572545927 37308045629238725358818891)
        ·
          refine ⟨55962068443858088038228337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37308045629238725358818891 55962068443858088038228337)
          ·
            refine ⟨41971551332893566028671253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55962068443858088038228337 41971551332893566028671253)
            ·
              refine ⟨1967416468729385907593965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41971551332893566028671253 1967416468729385907593965)
              ·
                refine ⟨737781175773519715347737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1967416468729385907593965 737781175773519715347737)
                ·
                  refine ⟨553335881830139786510803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 737781175773519715347737 553335881830139786510803)
                  ·
                    refine ⟨830003822745209679766205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 553335881830139786510803 830003822745209679766205)
                    ·
                      refine ⟨311251433529453629912327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 830003822745209679766205 311251433529453629912327)
                      ·
                        rfl

theorem cell23_606160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 2, 1, 3].length) (baseStart_606160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606160 prefixEnd_606160 := by exact prefixLift 606160
  have htrace : WordTrace (prefixWord ++ tailWord_606160) baseStart_606160 baseEnd_606160 := by
    simpa [prefixWord, tailWord_606160, baseEnd_606160] using wordTrace_append hprefix tailTrace_606160
  have hstable : (prefixWord ++ tailWord_606160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606160).length < 2 ^ (prefixWord ++ tailWord_606160).sum := by decide
  have hdescent : baseEnd_606160 < baseStart_606160 := by decide
  rcases family_descends (prefixWord ++ tailWord_606160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606178 : List Nat := [3, 3, 3, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_606178 : Nat := 118140960795 + 606178 * 2 ^ 59
def prefixEnd_606178 : Nat := 4983230072969 + 3 ^ 40 * 606178 * 2
def baseEnd_606178 : Nat := 311260676181234559487245

theorem tailTrace_606178 : CollatzResearch.WordTrace tailWord_606178 prefixEnd_606178 311260676181234559487245 := by
  unfold tailWord_606178
  simp only [CollatzResearch.WordTrace]
  refine ⟨5527281999482026951326797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14739418665285405203538125 5527281999482026951326797)
  ·
    refine ⟨2072730749805760106747549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5527281999482026951326797 2072730749805760106747549)
    ·
      refine ⟨777274031177160040030331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2072730749805760106747549 777274031177160040030331)
      ·
        refine ⟨1165911046765740060045497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 777274031177160040030331 1165911046765740060045497)
        ·
          refine ⟨874433285074305045034123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1165911046765740060045497 874433285074305045034123)
          ·
            refine ⟨1311649927611457567551185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874433285074305045034123 1311649927611457567551185)
            ·
              refine ⟨983737445708593175663389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1311649927611457567551185 983737445708593175663389)
              ·
                refine ⟨368901542140722440873771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 983737445708593175663389 368901542140722440873771)
                ·
                  refine ⟨553352313211083661310657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368901542140722440873771 553352313211083661310657)
                  ·
                    refine ⟨415014234908312745982993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 553352313211083661310657 415014234908312745982993)
                    ·
                      refine ⟨311260676181234559487245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 415014234908312745982993 311260676181234559487245)
                      ·
                        rfl

theorem cell23_606178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_606178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606178 prefixEnd_606178 := by exact prefixLift 606178
  have htrace : WordTrace (prefixWord ++ tailWord_606178) baseStart_606178 baseEnd_606178 := by
    simpa [prefixWord, tailWord_606178, baseEnd_606178] using wordTrace_append hprefix tailTrace_606178
  have hstable : (prefixWord ++ tailWord_606178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606178).length < 2 ^ (prefixWord ++ tailWord_606178).sum := by decide
  have hdescent : baseEnd_606178 < baseStart_606178 := by decide
  rcases family_descends (prefixWord ++ tailWord_606178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606213 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 2, 2, 4]
def baseStart_606213 : Nat := 118140960795 + 606213 * 2 ^ 59
def prefixEnd_606213 : Nat := 4983230072969 + 3 ^ 40 * 606213 * 2
def baseEnd_606213 : Nat := 311278648004141922549583

theorem tailTrace_606213 : CollatzResearch.WordTrace tailWord_606213 prefixEnd_606213 311278648004141922549583 := by
  unfold tailWord_606213
  simp only [CollatzResearch.WordTrace]
  refine ⟨22110404552801308782831293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14740269701867539188554195 22110404552801308782831293)
  ·
    refine ⟨8291401707300490793561735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22110404552801308782831293 8291401707300490793561735)
    ·
      refine ⟨12437102560950736190342603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8291401707300490793561735 12437102560950736190342603)
      ·
        refine ⟨18655653841426104285513905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12437102560950736190342603 18655653841426104285513905)
        ·
          refine ⟨13991740381069578214135429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18655653841426104285513905 13991740381069578214135429)
          ·
            refine ⟨2623451321450545915150393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13991740381069578214135429 2623451321450545915150393)
            ·
              refine ⟨1967588491087909436362795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2623451321450545915150393 1967588491087909436362795)
              ·
                refine ⟨2951382736631864154544193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1967588491087909436362795 2951382736631864154544193)
                ·
                  refine ⟨2213537052473898115908145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2951382736631864154544193 2213537052473898115908145)
                  ·
                    refine ⟨1660152789355423586931109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2213537052473898115908145 1660152789355423586931109)
                    ·
                      refine ⟨311278648004141922549583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1660152789355423586931109 311278648004141922549583)
                      ·
                        rfl

theorem cell23_606213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_606213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606213 prefixEnd_606213 := by exact prefixLift 606213
  have htrace : WordTrace (prefixWord ++ tailWord_606213) baseStart_606213 baseEnd_606213 := by
    simpa [prefixWord, tailWord_606213, baseEnd_606213] using wordTrace_append hprefix tailTrace_606213
  have hstable : (prefixWord ++ tailWord_606213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606213).length < 2 ^ (prefixWord ++ tailWord_606213).sum := by decide
  have hdescent : baseEnd_606213 < baseStart_606213 := by decide
  rcases family_descends (prefixWord ++ tailWord_606213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606257 : List Nat := [1, 2, 2, 3, 1, 4, 3, 2, 5]
def baseStart_606257 : Nat := 118140960795 + 606257 * 2 ^ 59
def prefixEnd_606257 : Nat := 4983230072969 + 3 ^ 40 * 606257 * 2
def baseEnd_606257 : Nat := 34589026794771083377709

theorem tailTrace_606257 : CollatzResearch.WordTrace tailWord_606257 prefixEnd_606257 34589026794771083377709 := by
  unfold tailWord_606257
  simp only [CollatzResearch.WordTrace]
  refine ⟨22112009364641904297433025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14741339576427936198288683 22112009364641904297433025)
  ·
    refine ⟨16584007023481428223074769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22112009364641904297433025 16584007023481428223074769)
    ·
      refine ⟨12438005267611071167306077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16584007023481428223074769 12438005267611071167306077)
      ·
        refine ⟨4664251975354151687739779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12438005267611071167306077 4664251975354151687739779)
        ·
          refine ⟨6996377963031227531609669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4664251975354151687739779 6996377963031227531609669)
          ·
            refine ⟨1311820868068355162176813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6996377963031227531609669 1311820868068355162176813)
            ·
              refine ⟨491932825525633185816305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1311820868068355162176813 491932825525633185816305)
              ·
                refine ⟨368949619144224889362229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491932825525633185816305 368949619144224889362229)
                ·
                  refine ⟨34589026794771083377709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 368949619144224889362229 34589026794771083377709)
                  ·
                    rfl

theorem cell23_606257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 5].length) (baseStart_606257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606257 prefixEnd_606257 := by exact prefixLift 606257
  have htrace : WordTrace (prefixWord ++ tailWord_606257) baseStart_606257 baseEnd_606257 := by
    simpa [prefixWord, tailWord_606257, baseEnd_606257] using wordTrace_append hprefix tailTrace_606257
  have hstable : (prefixWord ++ tailWord_606257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606257).length < 2 ^ (prefixWord ++ tailWord_606257).sum := by decide
  have hdescent : baseEnd_606257 < baseStart_606257 := by decide
  rcases family_descends (prefixWord ++ tailWord_606257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606344 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 2, 2, 3]
def baseStart_606344 : Nat := 118140960795 + 606344 * 2 ^ 59
def prefixEnd_606344 : Nat := 4983230072969 + 3 ^ 40 * 606344 * 2
def baseEnd_606344 : Nat := 311345913969880910011481

theorem tailTrace_606344 : CollatzResearch.WordTrace tailWord_606344 prefixEnd_606344 311345913969880910011481 := by
  unfold tailWord_606344
  simp only [CollatzResearch.WordTrace]
  refine ⟨11057591257663359077925043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14743455010217812103900057 11057591257663359077925043)
  ·
    refine ⟨16586386886495038616887565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11057591257663359077925043 16586386886495038616887565)
    ·
      refine ⟨6219895082435639481332837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16586386886495038616887565 6219895082435639481332837)
      ·
        refine ⟨1166230327956682402749907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6219895082435639481332837 1166230327956682402749907)
        ·
          refine ⟨1749345491935023604124861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1166230327956682402749907 1749345491935023604124861)
          ·
            refine ⟨656004559475633851546823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1749345491935023604124861 656004559475633851546823)
            ·
              refine ⟨984006839213450777320235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656004559475633851546823 984006839213450777320235)
              ·
                refine ⟨1476010258820176165980353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984006839213450777320235 1476010258820176165980353)
                ·
                  refine ⟨1107007694115132124485265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1476010258820176165980353 1107007694115132124485265)
                  ·
                    refine ⟨830255770586349093363949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1107007694115132124485265 830255770586349093363949)
                    ·
                      refine ⟨311345913969880910011481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 830255770586349093363949 311345913969880910011481)
                      ·
                        rfl

theorem cell23_606344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_606344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606344 prefixEnd_606344 := by exact prefixLift 606344
  have htrace : WordTrace (prefixWord ++ tailWord_606344) baseStart_606344 baseEnd_606344 := by
    simpa [prefixWord, tailWord_606344, baseEnd_606344] using wordTrace_append hprefix tailTrace_606344
  have hstable : (prefixWord ++ tailWord_606344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606344).length < 2 ^ (prefixWord ++ tailWord_606344).sum := by decide
  have hdescent : baseEnd_606344 < baseStart_606344 := by decide
  rcases family_descends (prefixWord ++ tailWord_606344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606410 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_606410 : Nat := 118140960795 + 606410 * 2 ^ 59
def prefixEnd_606410 : Nat := 4983230072969 + 3 ^ 40 * 606410 * 2
def baseEnd_606410 : Nat := 311379803693077651786177

theorem tailTrace_606410 : CollatzResearch.WordTrace tailWord_606410 prefixEnd_606410 311379803693077651786177 := by
  unfold tailWord_606410
  simp only [CollatzResearch.WordTrace]
  refine ⟨5529397433271902856938171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14745059822058407618501789 5529397433271902856938171)
  ·
    refine ⟨8294096149907854285407257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5529397433271902856938171 8294096149907854285407257)
    ·
      refine ⟨6220572112430890714055443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8294096149907854285407257 6220572112430890714055443)
      ·
        refine ⟨9330858168646336071083165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6220572112430890714055443 9330858168646336071083165)
        ·
          refine ⟨3499071813242376026656187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9330858168646336071083165 3499071813242376026656187)
          ·
            refine ⟨5248607719863564039984281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3499071813242376026656187 5248607719863564039984281)
            ·
              refine ⟨3936455789897673029988211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5248607719863564039984281 3936455789897673029988211)
              ·
                refine ⟨5904683684846509544982317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3936455789897673029988211 5904683684846509544982317)
                ·
                  refine ⟨2214256381817441079368369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5904683684846509544982317 2214256381817441079368369)
                  ·
                    refine ⟨1660692286363080809526277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2214256381817441079368369 1660692286363080809526277)
                    ·
                      refine ⟨311379803693077651786177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1660692286363080809526277 311379803693077651786177)
                      ·
                        rfl

theorem cell23_606410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_606410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606410 prefixEnd_606410 := by exact prefixLift 606410
  have htrace : WordTrace (prefixWord ++ tailWord_606410) baseStart_606410 baseEnd_606410 := by
    simpa [prefixWord, tailWord_606410, baseEnd_606410] using wordTrace_append hprefix tailTrace_606410
  have hstable : (prefixWord ++ tailWord_606410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606410).length < 2 ^ (prefixWord ++ tailWord_606410).sum := by decide
  have hdescent : baseEnd_606410 < baseStart_606410 := by decide
  rcases family_descends (prefixWord ++ tailWord_606410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606417 : List Nat := [1, 2, 2, 1, 2, 2, 4, 3, 1, 2, 3]
def baseStart_606417 : Nat := 118140960795 + 606417 * 2 ^ 59
def prefixEnd_606417 : Nat := 4983230072969 + 3 ^ 40 * 606417 * 2
def baseEnd_606417 : Nat := 311383398057659124398645

theorem tailTrace_606417 : CollatzResearch.WordTrace tailWord_606417 prefixEnd_606417 311383398057659124398645 := by
  unfold tailWord_606417
  simp only [CollatzResearch.WordTrace]
  refine ⟨22117845044062251623257505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14745230029374834415505003 22117845044062251623257505)
  ·
    refine ⟨16588383783046688717443129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22117845044062251623257505 16588383783046688717443129)
    ·
      refine ⟨12441287837285016538082347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16588383783046688717443129 12441287837285016538082347)
      ·
        refine ⟨18661931755927524807123521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12441287837285016538082347 18661931755927524807123521)
        ·
          refine ⟨13996448816945643605342641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18661931755927524807123521 13996448816945643605342641)
          ·
            refine ⟨10497336612709232704006981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13996448816945643605342641 10497336612709232704006981)
            ·
              refine ⟨1968250614882981132001309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10497336612709232704006981 1968250614882981132001309)
              ·
                refine ⟨738093980581117924500491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1968250614882981132001309 738093980581117924500491)
                ·
                  refine ⟨1107140970871676886750737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 738093980581117924500491 1107140970871676886750737)
                  ·
                    refine ⟨830355728153757665063053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1107140970871676886750737 830355728153757665063053)
                    ·
                      refine ⟨311383398057659124398645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 830355728153757665063053 311383398057659124398645)
                      ·
                        rfl

theorem cell23_606417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_606417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606417 prefixEnd_606417 := by exact prefixLift 606417
  have htrace : WordTrace (prefixWord ++ tailWord_606417) baseStart_606417 baseEnd_606417 := by
    simpa [prefixWord, tailWord_606417, baseEnd_606417] using wordTrace_append hprefix tailTrace_606417
  have hstable : (prefixWord ++ tailWord_606417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606417).length < 2 ^ (prefixWord ++ tailWord_606417).sum := by decide
  have hdescent : baseEnd_606417 < baseStart_606417 := by decide
  rcases family_descends (prefixWord ++ tailWord_606417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606474 : List Nat := [3, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2]
def baseStart_606474 : Nat := 118140960795 + 606474 * 2 ^ 59
def prefixEnd_606474 : Nat := 4983230072969 + 3 ^ 40 * 606474 * 2
def baseEnd_606474 : Nat := 311412666454965401385883

theorem tailTrace_606474 : CollatzResearch.WordTrace tailWord_606474 prefixEnd_606474 311412666454965401385883 := by
  unfold tailWord_606474
  simp only [CollatzResearch.WordTrace]
  refine ⟨5529981001213937589520619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14746616003237166905388317 5529981001213937589520619)
  ·
    refine ⟨8294971501820906384280929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5529981001213937589520619 8294971501820906384280929)
    ·
      refine ⟨6221228626365679788210697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8294971501820906384280929 6221228626365679788210697)
      ·
        refine ⟨4665921469774259841158023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6221228626365679788210697 4665921469774259841158023)
        ·
          refine ⟨6998882204661389761737035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4665921469774259841158023 6998882204661389761737035)
          ·
            refine ⟨10498323306992084642605553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6998882204661389761737035 10498323306992084642605553)
            ·
              refine ⟨7873742480244063481954165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10498323306992084642605553 7873742480244063481954165)
              ·
                refine ⟨738163357522880951433203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7873742480244063481954165 738163357522880951433203)
                ·
                  refine ⟨1107245036284321427149805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 738163357522880951433203 1107245036284321427149805)
                  ·
                    refine ⟨415216888606620535181177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1107245036284321427149805 415216888606620535181177)
                    ·
                      refine ⟨311412666454965401385883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 415216888606620535181177 311412666454965401385883)
                      ·
                        rfl

theorem cell23_606474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_606474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606474 prefixEnd_606474 := by exact prefixLift 606474
  have htrace : WordTrace (prefixWord ++ tailWord_606474) baseStart_606474 baseEnd_606474 := by
    simpa [prefixWord, tailWord_606474, baseEnd_606474] using wordTrace_append hprefix tailTrace_606474
  have hstable : (prefixWord ++ tailWord_606474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606474).length < 2 ^ (prefixWord ++ tailWord_606474).sum := by decide
  have hdescent : baseEnd_606474 < baseStart_606474 := by decide
  rcases family_descends (prefixWord ++ tailWord_606474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606547 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 2, 5, 2]
def baseStart_606547 : Nat := 118140960795 + 606547 * 2 ^ 59
def prefixEnd_606547 : Nat := 4983230072969 + 3 ^ 40 * 606547 * 2
def baseEnd_606547 : Nat := 311450150542743615773047

theorem tailTrace_606547 : CollatzResearch.WordTrace tailWord_606547 prefixEnd_606547 311450150542743615773047 := by
  unfold tailWord_606547
  simp only [CollatzResearch.WordTrace]
  refine ⟨22122586533591283825489895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14748391022394189216993263 22122586533591283825489895)
  ·
    refine ⟨33183879800386925738234843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22122586533591283825489895 33183879800386925738234843)
    ·
      refine ⟨49775819700580388607352265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33183879800386925738234843 49775819700580388607352265)
      ·
        refine ⟨37331864775435291455514199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49775819700580388607352265 37331864775435291455514199)
        ·
          refine ⟨55997797163152937183271299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37331864775435291455514199 55997797163152937183271299)
          ·
            refine ⟨83996695744729405774906949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55997797163152937183271299 83996695744729405774906949)
            ·
              refine ⟨15749380452136763582795053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83996695744729405774906949 15749380452136763582795053)
              ·
                refine ⟨5906017669551286343548145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15749380452136763582795053 5906017669551286343548145)
                ·
                  refine ⟨4429513252163464757661109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5906017669551286343548145 4429513252163464757661109)
                  ·
                    refine ⟨415266867390324821030729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4429513252163464757661109 415266867390324821030729)
                    ·
                      refine ⟨311450150542743615773047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 415266867390324821030729 311450150542743615773047)
                      ·
                        rfl

theorem cell23_606547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 5, 2].length) (baseStart_606547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606547 prefixEnd_606547 := by exact prefixLift 606547
  have htrace : WordTrace (prefixWord ++ tailWord_606547) baseStart_606547 baseEnd_606547 := by
    simpa [prefixWord, tailWord_606547, baseEnd_606547] using wordTrace_append hprefix tailTrace_606547
  have hstable : (prefixWord ++ tailWord_606547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606547).length < 2 ^ (prefixWord ++ tailWord_606547).sum := by decide
  have hdescent : baseEnd_606547 < baseStart_606547 := by decide
  rcases family_descends (prefixWord ++ tailWord_606547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606577 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 2, 1, 4]
def baseStart_606577 : Nat := 118140960795 + 606577 * 2 ^ 59
def prefixEnd_606577 : Nat := 4983230072969 + 3 ^ 40 * 606577 * 2
def baseEnd_606577 : Nat := 311465554962378498397909

theorem tailTrace_606577 : CollatzResearch.WordTrace tailWord_606577 prefixEnd_606577 311465554962378498397909 := by
  unfold tailWord_606577
  simp only [CollatzResearch.WordTrace]
  refine ⟨22123680723482598949081985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14749120482321732632721323 22123680723482598949081985)
  ·
    refine ⟨16592760542611949211811489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22123680723482598949081985 16592760542611949211811489)
    ·
      refine ⟨12444570406958961908858617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16592760542611949211811489 12444570406958961908858617)
      ·
        refine ⟨9333427805219221431643963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12444570406958961908858617 9333427805219221431643963)
        ·
          refine ⟨14000141707828832147465945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9333427805219221431643963 14000141707828832147465945)
          ·
            refine ⟨10500106280871624110599459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14000141707828832147465945 10500106280871624110599459)
            ·
              refine ⟨15750159421307436165899189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10500106280871624110599459 15750159421307436165899189)
              ·
                refine ⟨1476577445747572140553049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15750159421307436165899189 1476577445747572140553049)
                ·
                  refine ⟨1107433084310679105414787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1476577445747572140553049 1107433084310679105414787)
                  ·
                    refine ⟨1661149626466018658122181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1107433084310679105414787 1661149626466018658122181)
                    ·
                      refine ⟨311465554962378498397909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1661149626466018658122181 311465554962378498397909)
                      ·
                        rfl

theorem cell23_606577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_606577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606577 prefixEnd_606577 := by exact prefixLift 606577
  have htrace : WordTrace (prefixWord ++ tailWord_606577) baseStart_606577 baseEnd_606577 := by
    simpa [prefixWord, tailWord_606577, baseEnd_606577] using wordTrace_append hprefix tailTrace_606577
  have hstable : (prefixWord ++ tailWord_606577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606577).length < 2 ^ (prefixWord ++ tailWord_606577).sum := by decide
  have hdescent : baseEnd_606577 < baseStart_606577 := by decide
  rcases family_descends (prefixWord ++ tailWord_606577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606604 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 3, 4]
def baseStart_606604 : Nat := 118140960795 + 606604 * 2 ^ 59
def prefixEnd_606604 : Nat := 4983230072969 + 3 ^ 40 * 606604 * 2
def baseEnd_606604 : Nat := 103826472980016630920095

theorem tailTrace_606604 : CollatzResearch.WordTrace tailWord_606604 prefixEnd_606604 103826472980016630920095 := by
  unfold tailWord_606604
  simp only [CollatzResearch.WordTrace]
  refine ⟨11062332747192391280157433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14749776996256521706876577 11062332747192391280157433)
  ·
    refine ⟨8296749560394293460118075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11062332747192391280157433 8296749560394293460118075)
    ·
      refine ⟨12445124340591440190177113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8296749560394293460118075 12445124340591440190177113)
      ·
        refine ⟨9333843255443580142632835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12445124340591440190177113 9333843255443580142632835)
        ·
          refine ⟨14000764883165370213949253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9333843255443580142632835 14000764883165370213949253)
          ·
            refine ⟨2625143415593506915115485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14000764883165370213949253 2625143415593506915115485)
            ·
              refine ⟨984428780847565093168307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2625143415593506915115485 984428780847565093168307)
              ·
                refine ⟨1476643171271347639752461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984428780847565093168307 1476643171271347639752461)
                ·
                  refine ⟨553741189226755364907173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1476643171271347639752461 553741189226755364907173)
                  ·
                    refine ⟨103826472980016630920095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 553741189226755364907173 103826472980016630920095)
                    ·
                      rfl

theorem cell23_606604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_606604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606604 prefixEnd_606604 := by exact prefixLift 606604
  have htrace : WordTrace (prefixWord ++ tailWord_606604) baseStart_606604 baseEnd_606604 := by
    simpa [prefixWord, tailWord_606604, baseEnd_606604] using wordTrace_append hprefix tailTrace_606604
  have hstable : (prefixWord ++ tailWord_606604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606604).length < 2 ^ (prefixWord ++ tailWord_606604).sum := by decide
  have hdescent : baseEnd_606604 < baseStart_606604 := by decide
  rcases family_descends (prefixWord ++ tailWord_606604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606617 : List Nat := [1, 2, 1, 2, 1, 4, 3, 3, 6]
def baseStart_606617 : Nat := 118140960795 + 606617 * 2 ^ 59
def prefixEnd_606617 : Nat := 4983230072969 + 3 ^ 40 * 606617 * 2
def baseEnd_606617 : Nat := 34609566020950926877525

theorem tailTrace_606617 : CollatzResearch.WordTrace tailWord_606617 prefixEnd_606617 34609566020950926877525 := by
  unfold tailWord_606617
  simp only [CollatzResearch.WordTrace]
  refine ⟨22125139643337685780538105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14750093095558457187025403 22125139643337685780538105)
  ·
    refine ⟨16593854732503264335403579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22125139643337685780538105 16593854732503264335403579)
    ·
      refine ⟨24890782098754896503105369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16593854732503264335403579 24890782098754896503105369)
      ·
        refine ⟨18668086574066172377329027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24890782098754896503105369 18668086574066172377329027)
        ·
          refine ⟨28002129861099258565993541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18668086574066172377329027 28002129861099258565993541)
          ·
            refine ⟨5250399348956110981123789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28002129861099258565993541 5250399348956110981123789)
            ·
              refine ⟨1968899755858541617921421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5250399348956110981123789 1968899755858541617921421)
              ·
                refine ⟨738337408446953106720533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1968899755858541617921421 738337408446953106720533)
                ·
                  refine ⟨34609566020950926877525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 738337408446953106720533 34609566020950926877525)
                  ·
                    rfl

theorem cell23_606617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 6].length) (baseStart_606617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606617 prefixEnd_606617 := by exact prefixLift 606617
  have htrace : WordTrace (prefixWord ++ tailWord_606617) baseStart_606617 baseEnd_606617 := by
    simpa [prefixWord, tailWord_606617, baseEnd_606617] using wordTrace_append hprefix tailTrace_606617
  have hstable : (prefixWord ++ tailWord_606617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606617).length < 2 ^ (prefixWord ++ tailWord_606617).sum := by decide
  have hdescent : baseEnd_606617 < baseStart_606617 := by decide
  rcases family_descends (prefixWord ++ tailWord_606617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606631 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_606631 : Nat := 118140960795 + 606631 * 2 ^ 59
def prefixEnd_606631 : Nat := 4983230072969 + 3 ^ 40 * 606631 * 2
def baseEnd_606631 : Nat := 311493282917721287122661

theorem tailTrace_606631 : CollatzResearch.WordTrace tailWord_606631 prefixEnd_606631 311493282917721287122661 := by
  unfold tailWord_606631
  simp only [CollatzResearch.WordTrace]
  refine ⟨22125650265286966171547747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14750433510191310781031831 22125650265286966171547747)
  ·
    refine ⟨33188475397930449257321621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22125650265286966171547747 33188475397930449257321621)
    ·
      refine ⟨1555709784277989808936951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33188475397930449257321621 1555709784277989808936951)
      ·
        refine ⟨2333564676416984713405427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1555709784277989808936951 2333564676416984713405427)
        ·
          refine ⟨3500347014625477070108141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2333564676416984713405427 3500347014625477070108141)
          ·
            refine ⟨1312630130484553901290553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3500347014625477070108141 1312630130484553901290553)
            ·
              refine ⟨984472597863415425967915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1312630130484553901290553 984472597863415425967915)
              ·
                refine ⟨1476708896795123138951873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984472597863415425967915 1476708896795123138951873)
                ·
                  refine ⟨1107531672596342354213905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1476708896795123138951873 1107531672596342354213905)
                  ·
                    refine ⟨830648754447256765660429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1107531672596342354213905 830648754447256765660429)
                    ·
                      refine ⟨311493282917721287122661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 830648754447256765660429 311493282917721287122661)
                      ·
                        rfl

theorem cell23_606631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_606631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606631 prefixEnd_606631 := by exact prefixLift 606631
  have htrace : WordTrace (prefixWord ++ tailWord_606631) baseStart_606631 baseEnd_606631 := by
    simpa [prefixWord, tailWord_606631, baseEnd_606631] using wordTrace_append hprefix tailTrace_606631
  have hstable : (prefixWord ++ tailWord_606631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606631).length < 2 ^ (prefixWord ++ tailWord_606631).sum := by decide
  have hdescent : baseEnd_606631 < baseStart_606631 := by decide
  rcases family_descends (prefixWord ++ tailWord_606631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606678 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_606678 : Nat := 118140960795 + 606678 * 2 ^ 59
def prefixEnd_606678 : Nat := 4983230072969 + 3 ^ 40 * 606678 * 2
def baseEnd_606678 : Nat := 311517416508482603234945

theorem tailTrace_606678 : CollatzResearch.WordTrace tailWord_606678 prefixEnd_606678 311517416508482603234945 := by
  unfold tailWord_606678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1382960281007293324906793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14751576330744462132339125 1382960281007293324906793)
  ·
    refine ⟨1037220210755469993680095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1382960281007293324906793 1037220210755469993680095)
    ·
      refine ⟨1555830316133204990520143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1037220210755469993680095 1555830316133204990520143)
      ·
        refine ⟨2333745474199807485780215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1555830316133204990520143 2333745474199807485780215)
        ·
          refine ⟨3500618211299711228670323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2333745474199807485780215 3500618211299711228670323)
          ·
            refine ⟨5250927316949566843005485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3500618211299711228670323 5250927316949566843005485)
            ·
              refine ⟨1969097743856087566127057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5250927316949566843005485 1969097743856087566127057)
              ·
                refine ⟨1476823307892065674595293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1969097743856087566127057 1476823307892065674595293)
                ·
                  refine ⟨553808740459524627973235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1476823307892065674595293 553808740459524627973235)
                  ·
                    refine ⟨830713110689286941959853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 553808740459524627973235 830713110689286941959853)
                    ·
                      refine ⟨311517416508482603234945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 830713110689286941959853 311517416508482603234945)
                      ·
                        rfl

theorem cell23_606678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_606678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606678 prefixEnd_606678 := by exact prefixLift 606678
  have htrace : WordTrace (prefixWord ++ tailWord_606678) baseStart_606678 baseEnd_606678 := by
    simpa [prefixWord, tailWord_606678, baseEnd_606678] using wordTrace_append hprefix tailTrace_606678
  have hstable : (prefixWord ++ tailWord_606678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606678).length < 2 ^ (prefixWord ++ tailWord_606678).sum := by decide
  have hdescent : baseEnd_606678 < baseStart_606678 := by decide
  rcases family_descends (prefixWord ++ tailWord_606678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606697 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 3, 2, 4]
def baseStart_606697 : Nat := 118140960795 + 606697 * 2 ^ 59
def prefixEnd_606697 : Nat := 4983230072969 + 3 ^ 40 * 606697 * 2
def baseEnd_606697 : Nat := 311527172640918028897357

theorem tailTrace_606697 : CollatzResearch.WordTrace tailWord_606697 prefixEnd_606697 311527172640918028897357 := by
  unfold tailWord_606697
  simp only [CollatzResearch.WordTrace]
  refine ⟨22128057483047859443450345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14752038322031906295633563 22128057483047859443450345)
  ·
    refine ⟨16596043112285894582587759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22128057483047859443450345 16596043112285894582587759)
    ·
      refine ⟨24894064668428841873881639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16596043112285894582587759 24894064668428841873881639)
      ·
        refine ⟨37341097002643262810822459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24894064668428841873881639 37341097002643262810822459)
        ·
          refine ⟨56011645503964894216233689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37341097002643262810822459 56011645503964894216233689)
          ·
            refine ⟨42008734127973670662175267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56011645503964894216233689 42008734127973670662175267)
            ·
              refine ⟨63013101191960505993262901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42008734127973670662175267 63013101191960505993262901)
              ·
                refine ⟨5907478236746297436868397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63013101191960505993262901 5907478236746297436868397)
                ·
                  refine ⟨2215304338779861538825649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5907478236746297436868397 2215304338779861538825649)
                  ·
                    refine ⟨1661478254084896154119237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2215304338779861538825649 1661478254084896154119237)
                    ·
                      refine ⟨311527172640918028897357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1661478254084896154119237 311527172640918028897357)
                      ·
                        rfl

theorem cell23_606697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_606697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606697 prefixEnd_606697 := by exact prefixLift 606697
  have htrace : WordTrace (prefixWord ++ tailWord_606697) baseStart_606697 baseEnd_606697 := by
    simpa [prefixWord, tailWord_606697, baseEnd_606697] using wordTrace_append hprefix tailTrace_606697
  have hstable : (prefixWord ++ tailWord_606697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606697).length < 2 ^ (prefixWord ++ tailWord_606697).sum := by decide
  have hdescent : baseEnd_606697 < baseStart_606697 := by decide
  rcases family_descends (prefixWord ++ tailWord_606697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606698 : List Nat := [3, 1, 3, 1, 3, 3, 2, 1, 1, 5]
def baseStart_606698 : Nat := 118140960795 + 606698 * 2 ^ 59
def prefixEnd_606698 : Nat := 4983230072969 + 3 ^ 40 * 606698 * 2
def baseEnd_606698 : Nat := 103842562040524174994951

theorem tailTrace_606698 : CollatzResearch.WordTrace tailWord_606698 prefixEnd_606698 103842562040524174994951 := by
  unfold tailWord_606698
  simp only [CollatzResearch.WordTrace]
  refine ⟨5532023489011059153559187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14752062637362824409491165 5532023489011059153559187)
  ·
    refine ⟨8298035233516588730338781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5532023489011059153559187 8298035233516588730338781)
    ·
      refine ⟨3111763212568720773877043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8298035233516588730338781 3111763212568720773877043)
      ·
        refine ⟨4667644818853081160815565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3111763212568720773877043 4667644818853081160815565)
        ·
          refine ⟨1750366807069905435305837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4667644818853081160815565 1750366807069905435305837)
          ·
            refine ⟨656387552651214538239689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1750366807069905435305837 656387552651214538239689)
            ·
              refine ⟨492290664488410903679767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 656387552651214538239689 492290664488410903679767)
              ·
                refine ⟨738435996732616355519651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492290664488410903679767 738435996732616355519651)
                ·
                  refine ⟨1107653995098924533279477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 738435996732616355519651 1107653995098924533279477)
                  ·
                    refine ⟨103842562040524174994951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1107653995098924533279477 103842562040524174994951)
                    ·
                      rfl

theorem cell23_606698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_606698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606698 prefixEnd_606698 := by exact prefixLift 606698
  have htrace : WordTrace (prefixWord ++ tailWord_606698) baseStart_606698 baseEnd_606698 := by
    simpa [prefixWord, tailWord_606698, baseEnd_606698] using wordTrace_append hprefix tailTrace_606698
  have hstable : (prefixWord ++ tailWord_606698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606698).length < 2 ^ (prefixWord ++ tailWord_606698).sum := by decide
  have hdescent : baseEnd_606698 < baseStart_606698 := by decide
  rcases family_descends (prefixWord ++ tailWord_606698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606731 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 1, 2, 4]
def baseStart_606731 : Nat := 118140960795 + 606731 * 2 ^ 59
def prefixEnd_606731 : Nat := 4983230072969 + 3 ^ 40 * 606731 * 2
def baseEnd_606731 : Nat := 311544630983170895872201

theorem tailTrace_606731 : CollatzResearch.WordTrace tailWord_606731 prefixEnd_606731 311544630983170895872201 := by
  unfold tailWord_606731
  simp only [CollatzResearch.WordTrace]
  refine ⟨22129297564924683250188047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14752865043283122166792031 22129297564924683250188047)
  ·
    refine ⟨33193946347387024875282071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22129297564924683250188047 33193946347387024875282071)
    ·
      refine ⟨49790919521080537312923107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33193946347387024875282071 49790919521080537312923107)
      ·
        refine ⟨74686379281620805969384661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49790919521080537312923107 74686379281620805969384661)
        ·
          refine ⟨1750462014412987639907453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 74686379281620805969384661 1750462014412987639907453)
          ·
            refine ⟨656423255404870364965295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1750462014412987639907453 656423255404870364965295)
            ·
              refine ⟨984634883107305547447943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656423255404870364965295 984634883107305547447943)
              ·
                refine ⟨1476952324660958321171915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984634883107305547447943 1476952324660958321171915)
                ·
                  refine ⟨2215428486991437481757873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1476952324660958321171915 2215428486991437481757873)
                  ·
                    refine ⟨1661571365243578111318405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2215428486991437481757873 1661571365243578111318405)
                    ·
                      refine ⟨311544630983170895872201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1661571365243578111318405 311544630983170895872201)
                      ·
                        rfl

theorem cell23_606731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 2, 4].length) (baseStart_606731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606731 prefixEnd_606731 := by exact prefixLift 606731
  have htrace : WordTrace (prefixWord ++ tailWord_606731) baseStart_606731 baseEnd_606731 := by
    simpa [prefixWord, tailWord_606731, baseEnd_606731] using wordTrace_append hprefix tailTrace_606731
  have hstable : (prefixWord ++ tailWord_606731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606731).length < 2 ^ (prefixWord ++ tailWord_606731).sum := by decide
  have hdescent : baseEnd_606731 < baseStart_606731 := by decide
  rcases family_descends (prefixWord ++ tailWord_606731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606785 : List Nat := [1, 2, 5, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_606785 : Nat := 118140960795 + 606785 * 2 ^ 59
def prefixEnd_606785 : Nat := 4983230072969 + 3 ^ 40 * 606785 * 2
def baseEnd_606785 : Nat := 311572358938513684596953

theorem tailTrace_606785 : CollatzResearch.WordTrace tailWord_606785 prefixEnd_606785 311572358938513684596953 := by
  unfold tailWord_606785
  simp only [CollatzResearch.WordTrace]
  refine ⟨22131267106729050472653809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14754178071152700315102539 22131267106729050472653809)
  ·
    refine ⟨16598450330046787854490357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22131267106729050472653809 16598450330046787854490357)
    ·
      refine ⟨1556104718441886361358471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16598450330046787854490357 1556104718441886361358471)
      ·
        refine ⟨2334157077662829542037707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1556104718441886361358471 2334157077662829542037707)
        ·
          refine ⟨3501235616494244313056561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2334157077662829542037707 3501235616494244313056561)
          ·
            refine ⟨2625926712370683234792421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3501235616494244313056561 2625926712370683234792421)
            ·
              refine ⟨492361258569503106523579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2625926712370683234792421 492361258569503106523579)
              ·
                refine ⟨738541887854254659785369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492361258569503106523579 738541887854254659785369)
                ·
                  refine ⟨553906415890690994839027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 738541887854254659785369 553906415890690994839027)
                  ·
                    refine ⟨830859623836036492258541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 553906415890690994839027 830859623836036492258541)
                    ·
                      refine ⟨311572358938513684596953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 830859623836036492258541 311572358938513684596953)
                      ·
                        rfl

theorem cell23_606785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_606785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606785 prefixEnd_606785 := by exact prefixLift 606785
  have htrace : WordTrace (prefixWord ++ tailWord_606785) baseStart_606785 baseEnd_606785 := by
    simpa [prefixWord, tailWord_606785, baseEnd_606785] using wordTrace_append hprefix tailTrace_606785
  have hstable : (prefixWord ++ tailWord_606785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606785).length < 2 ^ (prefixWord ++ tailWord_606785).sum := by decide
  have hdescent : baseEnd_606785 < baseStart_606785 := by decide
  rcases family_descends (prefixWord ++ tailWord_606785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606787 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 6]
def baseStart_606787 : Nat := 118140960795 + 606787 * 2 ^ 59
def prefixEnd_606787 : Nat := 4983230072969 + 3 ^ 40 * 606787 * 2
def baseEnd_606787 : Nat := 311573385899822676771943

theorem tailTrace_606787 : CollatzResearch.WordTrace tailWord_606787 prefixEnd_606787 311573385899822676771943 := by
  unfold tailWord_606787
  simp only [CollatzResearch.WordTrace]
  refine ⟨22131340052721804814226615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14754226701814536542817743 22131340052721804814226615)
  ·
    refine ⟨33197010079082707221339923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22131340052721804814226615 33197010079082707221339923)
    ·
      refine ⟨49795515118624060832009885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33197010079082707221339923 49795515118624060832009885)
      ·
        refine ⟨18673318169484022812003707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49795515118624060832009885 18673318169484022812003707)
        ·
          refine ⟨28009977254226034218005561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18673318169484022812003707 28009977254226034218005561)
          ·
            refine ⟨21007482940669525663504171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28009977254226034218005561 21007482940669525663504171)
            ·
              refine ⟨31511224411004288495256257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21007482940669525663504171 31511224411004288495256257)
              ·
                refine ⟨23633418308253216371442193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31511224411004288495256257 23633418308253216371442193)
                ·
                  refine ⟨17725063731189912278581645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23633418308253216371442193 17725063731189912278581645)
                  ·
                    refine ⟨6646898899196217104468117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17725063731189912278581645 6646898899196217104468117)
                    ·
                      refine ⟨311573385899822676771943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6646898899196217104468117 311573385899822676771943)
                      ·
                        rfl

theorem cell23_606787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_606787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606787 prefixEnd_606787 := by exact prefixLift 606787
  have htrace : WordTrace (prefixWord ++ tailWord_606787) baseStart_606787 baseEnd_606787 := by
    simpa [prefixWord, tailWord_606787, baseEnd_606787] using wordTrace_append hprefix tailTrace_606787
  have hstable : (prefixWord ++ tailWord_606787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606787).length < 2 ^ (prefixWord ++ tailWord_606787).sum := by decide
  have hdescent : baseEnd_606787 < baseStart_606787 := by decide
  rcases family_descends (prefixWord ++ tailWord_606787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606794 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_606794 : Nat := 118140960795 + 606794 * 2 ^ 59
def prefixEnd_606794 : Nat := 4983230072969 + 3 ^ 40 * 606794 * 2
def baseEnd_606794 : Nat := 311576980264404149384411

theorem tailTrace_606794 : CollatzResearch.WordTrace tailWord_606794 prefixEnd_606794 311576980264404149384411 := by
  unfold tailWord_606794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5532898840924111252432859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14754396909130963339820957 5532898840924111252432859)
  ·
    refine ⟨8299348261386166878649289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5532898840924111252432859 8299348261386166878649289)
    ·
      refine ⟨6224511196039625158986967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8299348261386166878649289 6224511196039625158986967)
      ·
        refine ⟨9336766794059437738480451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6224511196039625158986967 9336766794059437738480451)
        ·
          refine ⟨14005150191089156607720677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9336766794059437738480451 14005150191089156607720677)
          ·
            refine ⟨2625965660829216863947627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14005150191089156607720677 2625965660829216863947627)
            ·
              refine ⟨3938948491243825295921441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2625965660829216863947627 3938948491243825295921441)
              ·
                refine ⟨2954211368432868971941081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3938948491243825295921441 2954211368432868971941081)
                ·
                  refine ⟨2215658526324651728955811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2954211368432868971941081 2215658526324651728955811)
                  ·
                    refine ⟨3323487789486977593433717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2215658526324651728955811 3323487789486977593433717)
                    ·
                      refine ⟨311576980264404149384411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3323487789486977593433717 311576980264404149384411)
                      ·
                        rfl

theorem cell23_606794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_606794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606794 prefixEnd_606794 := by exact prefixLift 606794
  have htrace : WordTrace (prefixWord ++ tailWord_606794) baseStart_606794 baseEnd_606794 := by
    simpa [prefixWord, tailWord_606794, baseEnd_606794] using wordTrace_append hprefix tailTrace_606794
  have hstable : (prefixWord ++ tailWord_606794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606794).length < 2 ^ (prefixWord ++ tailWord_606794).sum := by decide
  have hdescent : baseEnd_606794 < baseStart_606794 := by decide
  rcases family_descends (prefixWord ++ tailWord_606794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606812 : List Nat := [2, 2, 4, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_606812 : Nat := 118140960795 + 606812 * 2 ^ 59
def prefixEnd_606812 : Nat := 4983230072969 + 3 ^ 40 * 606812 * 2
def baseEnd_606812 : Nat := 311586222916185078959329

theorem tailTrace_606812 : CollatzResearch.WordTrace tailWord_606812 prefixEnd_606812 311586222916185078959329 := by
  unfold tailWord_606812
  simp only [CollatzResearch.WordTrace]
  refine ⟨11066125938815617041943345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14754834585087489389257793 11066125938815617041943345)
  ·
    refine ⟨8299594454111712781457509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11066125938815617041943345 8299594454111712781457509)
    ·
      refine ⟨1556173960145946146523283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8299594454111712781457509 1556173960145946146523283)
      ·
        refine ⟨2334260940218919219784925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1556173960145946146523283 2334260940218919219784925)
        ·
          refine ⟨875347852582094707419347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2334260940218919219784925 875347852582094707419347)
          ·
            refine ⟨1313021778873142061129021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875347852582094707419347 1313021778873142061129021)
            ·
              refine ⟨492383167077428272923383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1313021778873142061129021 492383167077428272923383)
              ·
                refine ⟨738574750616142409385075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492383167077428272923383 738574750616142409385075)
                ·
                  refine ⟨1107862125924213614077613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 738574750616142409385075 1107862125924213614077613)
                  ·
                    refine ⟨415448297221580105279105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1107862125924213614077613 415448297221580105279105)
                    ·
                      refine ⟨311586222916185078959329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 415448297221580105279105 311586222916185078959329)
                      ·
                        rfl

theorem cell23_606812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_606812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606812 prefixEnd_606812 := by exact prefixLift 606812
  have htrace : WordTrace (prefixWord ++ tailWord_606812) baseStart_606812 baseEnd_606812 := by
    simpa [prefixWord, tailWord_606812, baseEnd_606812] using wordTrace_append hprefix tailTrace_606812
  have hstable : (prefixWord ++ tailWord_606812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606812).length < 2 ^ (prefixWord ++ tailWord_606812).sum := by decide
  have hdescent : baseEnd_606812 < baseStart_606812 := by decide
  rcases family_descends (prefixWord ++ tailWord_606812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606838 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_606838 : Nat := 118140960795 + 606838 * 2 ^ 59
def prefixEnd_606838 : Nat := 4983230072969 + 3 ^ 40 * 606838 * 2
def baseEnd_606838 : Nat := 311599573413201977234209

theorem tailTrace_606838 : CollatzResearch.WordTrace tailWord_606838 prefixEnd_606838 311599573413201977234209 := by
  unfold tailWord_606838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1383325010971065032770823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14755466783691360349555445 1383325010971065032770823)
  ·
    refine ⟨2074987516456597549156235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1383325010971065032770823 2074987516456597549156235)
    ·
      refine ⟨3112481274684896323734353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2074987516456597549156235 3112481274684896323734353)
      ·
        refine ⟨2334360956013672242800765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3112481274684896323734353 2334360956013672242800765)
        ·
          refine ⟨875385358505127091050287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2334360956013672242800765 875385358505127091050287)
          ·
            refine ⟨1313078037757690636575431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875385358505127091050287 1313078037757690636575431)
            ·
              refine ⟨1969617056636535954863147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313078037757690636575431 1969617056636535954863147)
              ·
                refine ⟨2954425584954803932294721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969617056636535954863147 2954425584954803932294721)
                ·
                  refine ⟨2215819188716102949221041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2954425584954803932294721 2215819188716102949221041)
                  ·
                    refine ⟨1661864391537077211915781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2215819188716102949221041 1661864391537077211915781)
                    ·
                      refine ⟨311599573413201977234209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1661864391537077211915781 311599573413201977234209)
                      ·
                        rfl

theorem cell23_606838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_606838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606838 prefixEnd_606838 := by exact prefixLift 606838
  have htrace : WordTrace (prefixWord ++ tailWord_606838) baseStart_606838 baseEnd_606838 := by
    simpa [prefixWord, tailWord_606838, baseEnd_606838] using wordTrace_append hprefix tailTrace_606838
  have hstable : (prefixWord ++ tailWord_606838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606838).length < 2 ^ (prefixWord ++ tailWord_606838).sum := by decide
  have hdescent : baseEnd_606838 < baseStart_606838 := by decide
  rcases family_descends (prefixWord ++ tailWord_606838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606841 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 2, 3, 3]
def baseStart_606841 : Nat := 118140960795 + 606841 * 2 ^ 59
def prefixEnd_606841 : Nat := 4983230072969 + 3 ^ 40 * 606841 * 2
def baseEnd_606841 : Nat := 311601113855165465496695

theorem tailTrace_606841 : CollatzResearch.WordTrace tailWord_606841 prefixEnd_606841 311601113855165465496695 := by
  unfold tailWord_606841
  simp only [CollatzResearch.WordTrace]
  refine ⟨22133309594526172036692377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14755539729684114691128251 22133309594526172036692377)
  ·
    refine ⟨16599982195894629027519283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22133309594526172036692377 16599982195894629027519283)
    ·
      refine ⟨24899973293841943541278925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16599982195894629027519283 24899973293841943541278925)
      ·
        refine ⟨9337489985190728827979597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24899973293841943541278925 9337489985190728827979597)
        ·
          refine ⟨3501558744446523310492349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9337489985190728827979597 3501558744446523310492349)
          ·
            refine ⟨1313084529167446241434631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3501558744446523310492349 1313084529167446241434631)
            ·
              refine ⟨1969626793751169362151947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313084529167446241434631 1969626793751169362151947)
              ·
                refine ⟨2954440190626754043227921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969626793751169362151947 2954440190626754043227921)
                ·
                  refine ⟨2215830142970065532420941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2954440190626754043227921 2215830142970065532420941)
                  ·
                    refine ⟨830936303613774574657853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2215830142970065532420941 830936303613774574657853)
                    ·
                      refine ⟨311601113855165465496695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 830936303613774574657853 311601113855165465496695)
                      ·
                        rfl

theorem cell23_606841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_606841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606841 prefixEnd_606841 := by exact prefixLift 606841
  have htrace : WordTrace (prefixWord ++ tailWord_606841) baseStart_606841 baseEnd_606841 := by
    simpa [prefixWord, tailWord_606841, baseEnd_606841] using wordTrace_append hprefix tailTrace_606841
  have hstable : (prefixWord ++ tailWord_606841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606841).length < 2 ^ (prefixWord ++ tailWord_606841).sum := by decide
  have hdescent : baseEnd_606841 < baseStart_606841 := by decide
  rcases family_descends (prefixWord ++ tailWord_606841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606844 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 4, 5]
def baseStart_606844 : Nat := 118140960795 + 606844 * 2 ^ 59
def prefixEnd_606844 : Nat := 4983230072969 + 3 ^ 40 * 606844 * 2
def baseEnd_606844 : Nat := 103867551432376317919727

theorem tailTrace_606844 : CollatzResearch.WordTrace tailWord_606844 prefixEnd_606844 103867551432376317919727 := by
  unfold tailWord_606844
  simp only [CollatzResearch.WordTrace]
  refine ⟨11066709506757651774525793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14755612675676869032701057 11066709506757651774525793)
  ·
    refine ⟨8300032130068238830894345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11066709506757651774525793 8300032130068238830894345)
    ·
      refine ⟨6225024097551179123170759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8300032130068238830894345 6225024097551179123170759)
      ·
        refine ⟨9337536146326768684756139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6225024097551179123170759 9337536146326768684756139)
        ·
          refine ⟨14006304219490153027134209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9337536146326768684756139 14006304219490153027134209)
          ·
            refine ⟨10504728164617614770350657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14006304219490153027134209 10504728164617614770350657)
            ·
              refine ⟨7878546123463211077762993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10504728164617614770350657 7878546123463211077762993)
              ·
                refine ⟨5908909592597408308322245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7878546123463211077762993 5908909592597408308322245)
                ·
                  refine ⟨1107920548612014057810421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5908909592597408308322245 1107920548612014057810421)
                  ·
                    refine ⟨103867551432376317919727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1107920548612014057810421 103867551432376317919727)
                    ·
                      rfl

theorem cell23_606844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_606844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606844 prefixEnd_606844 := by exact prefixLift 606844
  have htrace : WordTrace (prefixWord ++ tailWord_606844) baseStart_606844 baseEnd_606844 := by
    simpa [prefixWord, tailWord_606844, baseEnd_606844] using wordTrace_append hprefix tailTrace_606844
  have hstable : (prefixWord ++ tailWord_606844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606844).length < 2 ^ (prefixWord ++ tailWord_606844).sum := by decide
  have hdescent : baseEnd_606844 < baseStart_606844 := by decide
  rcases family_descends (prefixWord ++ tailWord_606844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606944 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 7]
def baseStart_606944 : Nat := 118140960795 + 606944 * 2 ^ 59
def prefixEnd_606944 : Nat := 4983230072969 + 3 ^ 40 * 606944 * 2
def baseEnd_606944 : Nat := 311654002362578562508721

theorem tailTrace_606944 : CollatzResearch.WordTrace tailWord_606944 prefixEnd_606944 311654002362578562508721 := by
  unfold tailWord_606944
  simp only [CollatzResearch.WordTrace]
  refine ⟨11068533156576510313845943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14758044208768680418461257 11068533156576510313845943)
  ·
    refine ⟨16602799734864765470768915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11068533156576510313845943 16602799734864765470768915)
    ·
      refine ⟨24904199602297148206153373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16602799734864765470768915 24904199602297148206153373)
      ·
        refine ⟨9339074850861430577307515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24904199602297148206153373 9339074850861430577307515)
        ·
          refine ⟨14008612276292145865961273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9339074850861430577307515 14008612276292145865961273)
          ·
            refine ⟨10506459207219109399470955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14008612276292145865961273 10506459207219109399470955)
            ·
              refine ⟨15759688810828664099206433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10506459207219109399470955 15759688810828664099206433)
              ·
                refine ⟨11819766608121498074404825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15759688810828664099206433 11819766608121498074404825)
                ·
                  refine ⟨8864824956091123555803619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11819766608121498074404825 8864824956091123555803619)
                  ·
                    refine ⟨13297237434136685333705429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8864824956091123555803619 13297237434136685333705429)
                    ·
                      refine ⟨311654002362578562508721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13297237434136685333705429 311654002362578562508721)
                      ·
                        rfl

theorem cell23_606944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_606944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606944 prefixEnd_606944 := by exact prefixLift 606944
  have htrace : WordTrace (prefixWord ++ tailWord_606944) baseStart_606944 baseEnd_606944 := by
    simpa [prefixWord, tailWord_606944, baseEnd_606944] using wordTrace_append hprefix tailTrace_606944
  have hstable : (prefixWord ++ tailWord_606944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606944).length < 2 ^ (prefixWord ++ tailWord_606944).sum := by decide
  have hdescent : baseEnd_606944 < baseStart_606944 := by decide
  rcases family_descends (prefixWord ++ tailWord_606944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606981 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 6, 4]
def baseStart_606981 : Nat := 118140960795 + 606981 * 2 ^ 59
def prefixEnd_606981 : Nat := 4983230072969 + 3 ^ 40 * 606981 * 2
def baseEnd_606981 : Nat := 103891000382264972582017

theorem tailTrace_606981 : CollatzResearch.WordTrace tailWord_606981 prefixEnd_606981 103891000382264972582017 := by
  unfold tailWord_606981
  simp only [CollatzResearch.WordTrace]
  refine ⟨22138415814018975946788797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14758943876012650631192531 22138415814018975946788797)
  ·
    refine ⟨8301905930257115980045799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22138415814018975946788797 8301905930257115980045799)
    ·
      refine ⟨12452858895385673970068699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8301905930257115980045799 12452858895385673970068699)
      ·
        refine ⟨18679288343078510955103049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12452858895385673970068699 18679288343078510955103049)
        ·
          refine ⟨14009466257308883216327287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18679288343078510955103049 14009466257308883216327287)
          ·
            refine ⟨21014199385963324824490931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14009466257308883216327287 21014199385963324824490931)
            ·
              refine ⟨31521299078944987236736397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21014199385963324824490931 31521299078944987236736397)
              ·
                refine ⟨11820487154604370213776149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31521299078944987236736397 11820487154604370213776149)
                ·
                  refine ⟨554085335372079853770757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11820487154604370213776149 554085335372079853770757)
                  ·
                    refine ⟨103891000382264972582017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 554085335372079853770757 103891000382264972582017)
                    ·
                      rfl

theorem cell23_606981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_606981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_606981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_606981 prefixEnd_606981 := by exact prefixLift 606981
  have htrace : WordTrace (prefixWord ++ tailWord_606981) baseStart_606981 baseEnd_606981 := by
    simpa [prefixWord, tailWord_606981, baseEnd_606981] using wordTrace_append hprefix tailTrace_606981
  have hstable : (prefixWord ++ tailWord_606981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606981).length < 2 ^ (prefixWord ++ tailWord_606981).sum := by decide
  have hdescent : baseEnd_606981 < baseStart_606981 := by decide
  rcases family_descends (prefixWord ++ tailWord_606981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607008 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 3]
def baseStart_607008 : Nat := 118140960795 + 607008 * 2 ^ 59
def prefixEnd_607008 : Nat := 4983230072969 + 3 ^ 40 * 607008 * 2
def baseEnd_607008 : Nat := 311686865124466312108427

theorem tailTrace_607008 : CollatzResearch.WordTrace tailWord_607008 prefixEnd_607008 311686865124466312108427 := by
  unfold tailWord_607008
  simp only [CollatzResearch.WordTrace]
  refine ⟨11069700292460579779010839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14759600389947439705347785 11069700292460579779010839)
  ·
    refine ⟨16604550438690869668516259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11069700292460579779010839 16604550438690869668516259)
    ·
      refine ⟨24906825658036304502774389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16604550438690869668516259 24906825658036304502774389)
      ·
        refine ⟨2335014905440903547135099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24906825658036304502774389 2335014905440903547135099)
        ·
          refine ⟨3502522358161355320702649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2335014905440903547135099 3502522358161355320702649)
          ·
            refine ⟨2626891768621016490526987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3502522358161355320702649 2626891768621016490526987)
            ·
              refine ⟨3940337652931524735790481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626891768621016490526987 3940337652931524735790481)
              ·
                refine ⟨2955253239698643551842861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3940337652931524735790481 2955253239698643551842861)
                ·
                  refine ⟨1108219964886991331941073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2955253239698643551842861 1108219964886991331941073)
                  ·
                    refine ⟨831164973665243498955805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1108219964886991331941073 831164973665243498955805)
                    ·
                      refine ⟨311686865124466312108427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 831164973665243498955805 311686865124466312108427)
                      ·
                        rfl

theorem cell23_607008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_607008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607008 prefixEnd_607008 := by exact prefixLift 607008
  have htrace : WordTrace (prefixWord ++ tailWord_607008) baseStart_607008 baseEnd_607008 := by
    simpa [prefixWord, tailWord_607008, baseEnd_607008] using wordTrace_append hprefix tailTrace_607008
  have hstable : (prefixWord ++ tailWord_607008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607008).length < 2 ^ (prefixWord ++ tailWord_607008).sum := by decide
  have hdescent : baseEnd_607008 < baseStart_607008 := by decide
  rcases family_descends (prefixWord ++ tailWord_607008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607022 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_607022 : Nat := 118140960795 + 607022 * 2 ^ 59
def prefixEnd_607022 : Nat := 4983230072969 + 3 ^ 40 * 607022 * 2
def baseEnd_607022 : Nat := 311694053853629257333363

theorem tailTrace_607022 : CollatzResearch.WordTrace tailWord_607022 prefixEnd_607022 311694053853629257333363 := by
  unfold tailWord_607022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2767488900858804993628915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14759940804580293299354213 2767488900858804993628915)
  ·
    refine ⟨4151233351288207490443373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2767488900858804993628915 4151233351288207490443373)
    ·
      refine ⟨1556712506733077808916265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4151233351288207490443373 1556712506733077808916265)
      ·
        refine ⟨1167534380049808356687199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1556712506733077808916265 1167534380049808356687199)
        ·
          refine ⟨1751301570074712535030799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1167534380049808356687199 1751301570074712535030799)
          ·
            refine ⟨2626952355112068802546199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751301570074712535030799 2626952355112068802546199)
            ·
              refine ⟨3940428532668103203819299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626952355112068802546199 3940428532668103203819299)
              ·
                refine ⟨5910642799002154805728949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3940428532668103203819299 5910642799002154805728949)
                ·
                  refine ⟨554122762406452013037089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5910642799002154805728949 554122762406452013037089)
                  ·
                    refine ⟨415592071804839009777817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 554122762406452013037089 415592071804839009777817)
                    ·
                      refine ⟨311694053853629257333363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 415592071804839009777817 311694053853629257333363)
                      ·
                        rfl

theorem cell23_607022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_607022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607022 prefixEnd_607022 := by exact prefixLift 607022
  have htrace : WordTrace (prefixWord ++ tailWord_607022) baseStart_607022 baseEnd_607022 := by
    simpa [prefixWord, tailWord_607022, baseEnd_607022] using wordTrace_append hprefix tailTrace_607022
  have hstable : (prefixWord ++ tailWord_607022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607022).length < 2 ^ (prefixWord ++ tailWord_607022).sum := by decide
  have hdescent : baseEnd_607022 < baseStart_607022 := by decide
  rcases family_descends (prefixWord ++ tailWord_607022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607039 : List Nat := [1, 1, 2, 2, 5, 2, 2, 3, 1, 2, 2]
def baseStart_607039 : Nat := 118140960795 + 607039 * 2 ^ 59
def prefixEnd_607039 : Nat := 4983230072969 + 3 ^ 40 * 607039 * 2
def baseEnd_607039 : Nat := 311702783024755690820785

theorem tailTrace_607039 : CollatzResearch.WordTrace tailWord_607039 prefixEnd_607039 311702783024755690820785 := by
  unfold tailWord_607039
  simp only [CollatzResearch.WordTrace]
  refine ⟨22140531247808851852400171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14760354165205901234933447 22140531247808851852400171)
  ·
    refine ⟨33210796871713277778600257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22140531247808851852400171 33210796871713277778600257)
    ·
      refine ⟨24908097653784958333950193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33210796871713277778600257 24908097653784958333950193)
      ·
        refine ⟨18681073240338718750462645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24908097653784958333950193 18681073240338718750462645)
        ·
          refine ⟨1751350616281754882855873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18681073240338718750462645 1751350616281754882855873)
          ·
            refine ⟨1313512962211316162141905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1751350616281754882855873 1313512962211316162141905)
            ·
              refine ⟨985134721658487121606429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1313512962211316162141905 985134721658487121606429)
              ·
                refine ⟨369425520621932670602411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 985134721658487121606429 369425520621932670602411)
                ·
                  refine ⟨554138280932899005903617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 369425520621932670602411 554138280932899005903617)
                  ·
                    refine ⟨415603710699674254427713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 554138280932899005903617 415603710699674254427713)
                    ·
                      refine ⟨311702783024755690820785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 415603710699674254427713 311702783024755690820785)
                      ·
                        rfl

theorem cell23_607039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 1, 2, 2].length) (baseStart_607039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607039 prefixEnd_607039 := by exact prefixLift 607039
  have htrace : WordTrace (prefixWord ++ tailWord_607039) baseStart_607039 baseEnd_607039 := by
    simpa [prefixWord, tailWord_607039, baseEnd_607039] using wordTrace_append hprefix tailTrace_607039
  have hstable : (prefixWord ++ tailWord_607039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607039).length < 2 ^ (prefixWord ++ tailWord_607039).sum := by decide
  have hdescent : baseEnd_607039 < baseStart_607039 := by decide
  rcases family_descends (prefixWord ++ tailWord_607039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607071 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 2, 6]
def baseStart_607071 : Nat := 118140960795 + 607071 * 2 ^ 59
def prefixEnd_607071 : Nat := 4983230072969 + 3 ^ 40 * 607071 * 2
def baseEnd_607071 : Nat := 103906404801899855206879

theorem tailTrace_607071 : CollatzResearch.WordTrace tailWord_607071 prefixEnd_607071 103906404801899855206879 := by
  unfold tailWord_607071
  simp only [CollatzResearch.WordTrace]
  refine ⟨22141698383692921317565067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14761132255795280878376711 22141698383692921317565067)
  ·
    refine ⟨33212547575539381976347601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22141698383692921317565067 33212547575539381976347601)
    ·
      refine ⟨24909410681654536482260701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33212547575539381976347601 24909410681654536482260701)
      ·
        refine ⟨9341029005620451180847763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24909410681654536482260701 9341029005620451180847763)
        ·
          refine ⟨14011543508430676771271645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9341029005620451180847763 14011543508430676771271645)
          ·
            refine ⟨5254328815661503789226867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14011543508430676771271645 5254328815661503789226867)
            ·
              refine ⟨7881493223492255683840301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5254328815661503789226867 7881493223492255683840301)
              ·
                refine ⟨2955559958809595881440113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7881493223492255683840301 2955559958809595881440113)
                ·
                  refine ⟨2216669969107196911080085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2955559958809595881440113 2216669969107196911080085)
                  ·
                    refine ⟨103906404801899855206879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2216669969107196911080085 103906404801899855206879)
                    ·
                      rfl

theorem cell23_607071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 6].length) (baseStart_607071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607071 prefixEnd_607071 := by exact prefixLift 607071
  have htrace : WordTrace (prefixWord ++ tailWord_607071) baseStart_607071 baseEnd_607071 := by
    simpa [prefixWord, tailWord_607071, baseEnd_607071] using wordTrace_append hprefix tailTrace_607071
  have hstable : (prefixWord ++ tailWord_607071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607071).length < 2 ^ (prefixWord ++ tailWord_607071).sum := by decide
  have hdescent : baseEnd_607071 < baseStart_607071 := by decide
  rcases family_descends (prefixWord ++ tailWord_607071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607072 : List Nat := [2, 1, 1, 3, 3, 1, 5, 1, 2, 1, 3]
def baseStart_607072 : Nat := 118140960795 + 607072 * 2 ^ 59
def prefixEnd_607072 : Nat := 4983230072969 + 3 ^ 40 * 607072 * 2
def baseEnd_607072 : Nat := 311719727886354061708133

theorem tailTrace_607072 : CollatzResearch.WordTrace tailWord_607072 prefixEnd_607072 311719727886354061708133 := by
  unfold tailWord_607072
  simp only [CollatzResearch.WordTrace]
  refine ⟨11070867428344649244175735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14761156571126198992234313 11070867428344649244175735)
  ·
    refine ⟨16606301142516973866263603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11070867428344649244175735 16606301142516973866263603)
    ·
      refine ⟨24909451713775460799395405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16606301142516973866263603 24909451713775460799395405)
      ·
        refine ⟨9341044392665797799773277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24909451713775460799395405 9341044392665797799773277)
        ·
          refine ⟨3502891647249674174914979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9341044392665797799773277 3502891647249674174914979)
          ·
            refine ⟨5254337470874511262372469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502891647249674174914979 5254337470874511262372469)
            ·
              refine ⟨492594137894485430847419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5254337470874511262372469 492594137894485430847419)
              ·
                refine ⟨738891206841728146271129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492594137894485430847419 738891206841728146271129)
                ·
                  refine ⟨554168405131296109703347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 738891206841728146271129 554168405131296109703347)
                  ·
                    refine ⟨831252607696944164555021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 554168405131296109703347 831252607696944164555021)
                    ·
                      refine ⟨311719727886354061708133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 831252607696944164555021 311719727886354061708133)
                      ·
                        rfl

theorem cell23_607072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_607072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607072 prefixEnd_607072 := by exact prefixLift 607072
  have htrace : WordTrace (prefixWord ++ tailWord_607072) baseStart_607072 baseEnd_607072 := by
    simpa [prefixWord, tailWord_607072, baseEnd_607072] using wordTrace_append hprefix tailTrace_607072
  have hstable : (prefixWord ++ tailWord_607072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607072).length < 2 ^ (prefixWord ++ tailWord_607072).sum := by decide
  have hdescent : baseEnd_607072 < baseStart_607072 := by decide
  rcases family_descends (prefixWord ++ tailWord_607072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607091 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 4]
def baseStart_607091 : Nat := 118140960795 + 607091 * 2 ^ 59
def prefixEnd_607091 : Nat := 4983230072969 + 3 ^ 40 * 607091 * 2
def baseEnd_607091 : Nat := 311729484018789487370545

theorem tailTrace_607091 : CollatzResearch.WordTrace tailWord_607091 prefixEnd_607091 311729484018789487370545 := by
  unfold tailWord_607091
  simp only [CollatzResearch.WordTrace]
  refine ⟨22142427843620464733293127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14761618562413643155528751 22142427843620464733293127)
  ·
    refine ⟨33213641765430697099939691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22142427843620464733293127 33213641765430697099939691)
    ·
      refine ⟨49820462648146045649909537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33213641765430697099939691 49820462648146045649909537)
      ·
        refine ⟨37365346986109534237432153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49820462648146045649909537 37365346986109534237432153)
        ·
          refine ⟨28024010239582150678074115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37365346986109534237432153 28024010239582150678074115)
          ·
            refine ⟨42036015359373226017111173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28024010239582150678074115 42036015359373226017111173)
            ·
              refine ⟨7881752879882479878208345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42036015359373226017111173 7881752879882479878208345)
              ·
                refine ⟨5911314659911859908656259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7881752879882479878208345 5911314659911859908656259)
                ·
                  refine ⟨8866971989867789862984389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5911314659911859908656259 8866971989867789862984389)
                  ·
                    refine ⟨1662557248100210599309573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8866971989867789862984389 1662557248100210599309573)
                    ·
                      refine ⟨311729484018789487370545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1662557248100210599309573 311729484018789487370545)
                      ·
                        rfl

theorem cell23_607091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_607091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607091 prefixEnd_607091 := by exact prefixLift 607091
  have htrace : WordTrace (prefixWord ++ tailWord_607091) baseStart_607091 baseEnd_607091 := by
    simpa [prefixWord, tailWord_607091, baseEnd_607091] using wordTrace_append hprefix tailTrace_607091
  have hstable : (prefixWord ++ tailWord_607091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607091).length < 2 ^ (prefixWord ++ tailWord_607091).sum := by decide
  have hdescent : baseEnd_607091 < baseStart_607091 := by decide
  rcases family_descends (prefixWord ++ tailWord_607091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607101 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 9]
def baseStart_607101 : Nat := 118140960795 + 607101 * 2 ^ 59
def prefixEnd_607101 : Nat := 4983230072969 + 3 ^ 40 * 607101 * 2
def baseEnd_607101 : Nat := 34637179869481605360611

theorem tailTrace_607101 : CollatzResearch.WordTrace tailWord_607101 prefixEnd_607101 34637179869481605360611 := by
  unfold tailWord_607101
  simp only [CollatzResearch.WordTrace]
  refine ⟨22142792573584236441157157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14761861715722824294104771 22142792573584236441157157)
  ·
    refine ⟨4151773607547044332716967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22142792573584236441157157 4151773607547044332716967)
    ·
      refine ⟨6227660411320566499075451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4151773607547044332716967 6227660411320566499075451)
      ·
        refine ⟨9341490616980849748613177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6227660411320566499075451 9341490616980849748613177)
        ·
          refine ⟨7006117962735637311459883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9341490616980849748613177 7006117962735637311459883)
          ·
            refine ⟨10509176944103455967189825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7006117962735637311459883 10509176944103455967189825)
            ·
              refine ⟨7881882708077591975392369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10509176944103455967189825 7881882708077591975392369)
              ·
                refine ⟨5911412031058193981544277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7881882708077591975392369 5911412031058193981544277)
                ·
                  refine ⟨34637179869481605360611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5911412031058193981544277 34637179869481605360611)
                  ·
                    rfl

theorem cell23_607101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_607101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607101 prefixEnd_607101 := by exact prefixLift 607101
  have htrace : WordTrace (prefixWord ++ tailWord_607101) baseStart_607101 baseEnd_607101 := by
    simpa [prefixWord, tailWord_607101, baseEnd_607101] using wordTrace_append hprefix tailTrace_607101
  have hstable : (prefixWord ++ tailWord_607101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607101).length < 2 ^ (prefixWord ++ tailWord_607101).sum := by decide
  have hdescent : baseEnd_607101 < baseStart_607101 := by decide
  rcases family_descends (prefixWord ++ tailWord_607101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607112 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 4, 2, 2]
def baseStart_607112 : Nat := 118140960795 + 607112 * 2 ^ 59
def prefixEnd_607112 : Nat := 4983230072969 + 3 ^ 40 * 607112 * 2
def baseEnd_607112 : Nat := 311740267112533905207949

theorem tailTrace_607112 : CollatzResearch.WordTrace tailWord_607112 prefixEnd_607112 311740267112533905207949 := by
  unfold tailWord_607112
  simp only [CollatzResearch.WordTrace]
  refine ⟨11071596888272192659903795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14762129184362923546538393 11071596888272192659903795)
  ·
    refine ⟨16607395332408288989855693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11071596888272192659903795 16607395332408288989855693)
    ·
      refine ⟨6227773249653108371195885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16607395332408288989855693 6227773249653108371195885)
      ·
        refine ⟨2335414968619915639198457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6227773249653108371195885 2335414968619915639198457)
        ·
          refine ⟨1751561226464936729398843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2335414968619915639198457 1751561226464936729398843)
          ·
            refine ⟨2627341839697405094098265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751561226464936729398843 2627341839697405094098265)
            ·
              refine ⟨1970506379773053820573699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2627341839697405094098265 1970506379773053820573699)
              ·
                refine ⟨2955759569659580730860549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970506379773053820573699 2955759569659580730860549)
                ·
                  refine ⟨554204919311171387036353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2955759569659580730860549 554204919311171387036353)
                  ·
                    refine ⟨415653689483378540277265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 554204919311171387036353 415653689483378540277265)
                    ·
                      refine ⟨311740267112533905207949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 415653689483378540277265 311740267112533905207949)
                      ·
                        rfl

theorem cell23_607112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_607112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607112 prefixEnd_607112 := by exact prefixLift 607112
  have htrace : WordTrace (prefixWord ++ tailWord_607112) baseStart_607112 baseEnd_607112 := by
    simpa [prefixWord, tailWord_607112, baseEnd_607112] using wordTrace_append hprefix tailTrace_607112
  have hstable : (prefixWord ++ tailWord_607112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607112).length < 2 ^ (prefixWord ++ tailWord_607112).sum := by decide
  have hdescent : baseEnd_607112 < baseStart_607112 := by decide
  rcases family_descends (prefixWord ++ tailWord_607112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607185 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 2, 4, 2]
def baseStart_607185 : Nat := 118140960795 + 607185 * 2 ^ 59
def prefixEnd_607185 : Nat := 4983230072969 + 3 ^ 40 * 607185 * 2
def baseEnd_607185 : Nat := 311777751200312119595113

theorem tailTrace_607185 : CollatzResearch.WordTrace tailWord_607185 prefixEnd_607185 311777751200312119595113 := by
  unfold tailWord_607185
  simp only [CollatzResearch.WordTrace]
  refine ⟨22145856305279918787215009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14763904203519945858143339 22145856305279918787215009)
  ·
    refine ⟨16609392228959939090411257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22145856305279918787215009 16609392228959939090411257)
    ·
      refine ⟨12457044171719954317808443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16609392228959939090411257 12457044171719954317808443)
      ·
        refine ⟨18685566257579931476712665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12457044171719954317808443 18685566257579931476712665)
        ·
          refine ⟨14014174693184948607534499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18685566257579931476712665 14014174693184948607534499)
          ·
            refine ⟨21021262039777422911301749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14014174693184948607534499 21021262039777422911301749)
            ·
              refine ⟨1970743316229133397934539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21021262039777422911301749 1970743316229133397934539)
              ·
                refine ⟨2956114974343700096901809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970743316229133397934539 2956114974343700096901809)
                ·
                  refine ⟨2217086230757775072676357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2956114974343700096901809 2217086230757775072676357)
                  ·
                    refine ⟨415703668267082826126817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2217086230757775072676357 415703668267082826126817)
                    ·
                      refine ⟨311777751200312119595113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 415703668267082826126817 311777751200312119595113)
                      ·
                        rfl

theorem cell23_607185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 4, 2].length) (baseStart_607185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607185 prefixEnd_607185 := by exact prefixLift 607185
  have htrace : WordTrace (prefixWord ++ tailWord_607185) baseStart_607185 baseEnd_607185 := by
    simpa [prefixWord, tailWord_607185, baseEnd_607185] using wordTrace_append hprefix tailTrace_607185
  have hstable : (prefixWord ++ tailWord_607185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607185).length < 2 ^ (prefixWord ++ tailWord_607185).sum := by decide
  have hdescent : baseEnd_607185 < baseStart_607185 := by decide
  rcases family_descends (prefixWord ++ tailWord_607185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607202 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_607202 : Nat := 118140960795 + 607202 * 2 ^ 59
def prefixEnd_607202 : Nat := 4983230072969 + 3 ^ 40 * 607202 * 2
def baseEnd_607202 : Nat := 311786480371438553082535

theorem tailTrace_607202 : CollatzResearch.WordTrace tailWord_607202 prefixEnd_607202 311786480371438553082535 := by
  unfold tailWord_607202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5536619086554582672645965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14764317564145553793722573 5536619086554582672645965)
  ·
    refine ⟨2076232157457968502242237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5536619086554582672645965 2076232157457968502242237)
    ·
      refine ⟨778587059046738188340839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2076232157457968502242237 778587059046738188340839)
      ·
        refine ⟨1167880588570107282511259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 778587059046738188340839 1167880588570107282511259)
        ·
          refine ⟨1751820882855160923766889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1167880588570107282511259 1751820882855160923766889)
          ·
            refine ⟨1313865662141370692825167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1751820882855160923766889 1313865662141370692825167)
            ·
              refine ⟨1970798493212056039237751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313865662141370692825167 1970798493212056039237751)
              ·
                refine ⟨2956197739818084058856627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970798493212056039237751 2956197739818084058856627)
                ·
                  refine ⟨4434296609727126088284941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2956197739818084058856627 4434296609727126088284941)
                  ·
                    refine ⟨1662861228647672283106853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4434296609727126088284941 1662861228647672283106853)
                    ·
                      refine ⟨311786480371438553082535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1662861228647672283106853 311786480371438553082535)
                      ·
                        rfl

theorem cell23_607202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_607202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607202 prefixEnd_607202 := by exact prefixLift 607202
  have htrace : WordTrace (prefixWord ++ tailWord_607202) baseStart_607202 baseEnd_607202 := by
    simpa [prefixWord, tailWord_607202, baseEnd_607202] using wordTrace_append hprefix tailTrace_607202
  have hstable : (prefixWord ++ tailWord_607202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607202).length < 2 ^ (prefixWord ++ tailWord_607202).sum := by decide
  have hdescent : baseEnd_607202 < baseStart_607202 := by decide
  rcases family_descends (prefixWord ++ tailWord_607202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607228 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_607228 : Nat := 118140960795 + 607228 * 2 ^ 59
def prefixEnd_607228 : Nat := 4983230072969 + 3 ^ 40 * 607228 * 2
def baseEnd_607228 : Nat := 311799830868455451357415

theorem tailTrace_607228 : CollatzResearch.WordTrace tailWord_607228 prefixEnd_607228 311799830868455451357415 := by
  unfold tailWord_607228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11073712322062068565515169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14764949762749424754020225 11073712322062068565515169)
  ·
    refine ⟨8305284241546551424136377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11073712322062068565515169 8305284241546551424136377)
    ·
      refine ⟨6228963181159913568102283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8305284241546551424136377 6228963181159913568102283)
      ·
        refine ⟨9343444771739870352153425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6228963181159913568102283 9343444771739870352153425)
        ·
          refine ⟨7007583578804902764115069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9343444771739870352153425 7007583578804902764115069)
          ·
            refine ⟨2627843842051838536543151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7007583578804902764115069 2627843842051838536543151)
            ·
              refine ⟨3941765763077757804814727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2627843842051838536543151 3941765763077757804814727)
              ·
                refine ⟨5912648644616636707222091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3941765763077757804814727 5912648644616636707222091)
                ·
                  refine ⟨8868972966924955060833137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5912648644616636707222091 8868972966924955060833137)
                  ·
                    refine ⟨6651729725193716295624853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8868972966924955060833137 6651729725193716295624853)
                    ·
                      refine ⟨311799830868455451357415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6651729725193716295624853 311799830868455451357415)
                      ·
                        rfl

theorem cell23_607228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_607228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607228 prefixEnd_607228 := by exact prefixLift 607228
  have htrace : WordTrace (prefixWord ++ tailWord_607228) baseStart_607228 baseEnd_607228 := by
    simpa [prefixWord, tailWord_607228, baseEnd_607228] using wordTrace_append hprefix tailTrace_607228
  have hstable : (prefixWord ++ tailWord_607228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607228).length < 2 ^ (prefixWord ++ tailWord_607228).sum := by decide
  have hdescent : baseEnd_607228 < baseStart_607228 := by decide
  rcases family_descends (prefixWord ++ tailWord_607228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607242 : List Nat := [3, 1, 2, 2, 3, 2, 3, 1, 6]
def baseStart_607242 : Nat := 118140960795 + 607242 * 2 ^ 59
def prefixEnd_607242 : Nat := 4983230072969 + 3 ^ 40 * 607242 * 2
def baseEnd_607242 : Nat := 34645224399735377398039

theorem tailTrace_607242 : CollatzResearch.WordTrace tailWord_607242 prefixEnd_607242 34645224399735377398039 := by
  unfold tailWord_607242
  simp only [CollatzResearch.WordTrace]
  refine ⟨5536983816518354380509995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14765290177382278348026653 5536983816518354380509995)
  ·
    refine ⟨8305475724777531570764993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5536983816518354380509995 8305475724777531570764993)
    ·
      refine ⟨6229106793583148678073745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8305475724777531570764993 6229106793583148678073745)
      ·
        refine ⟨4671830095187361508555309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6229106793583148678073745 4671830095187361508555309)
        ·
          refine ⟨1751936285695260565708241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4671830095187361508555309 1751936285695260565708241)
          ·
            refine ⟨1313952214271445424281181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1751936285695260565708241 1313952214271445424281181)
            ·
              refine ⟨492732080351792034105443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1313952214271445424281181 492732080351792034105443)
              ·
                refine ⟨739098120527688051158165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492732080351792034105443 739098120527688051158165)
                ·
                  refine ⟨34645224399735377398039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 739098120527688051158165 34645224399735377398039)
                  ·
                    rfl

theorem cell23_607242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 6].length) (baseStart_607242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607242 prefixEnd_607242 := by exact prefixLift 607242
  have htrace : WordTrace (prefixWord ++ tailWord_607242) baseStart_607242 baseEnd_607242 := by
    simpa [prefixWord, tailWord_607242, baseEnd_607242] using wordTrace_append hprefix tailTrace_607242
  have hstable : (prefixWord ++ tailWord_607242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607242).length < 2 ^ (prefixWord ++ tailWord_607242).sum := by decide
  have hdescent : baseEnd_607242 < baseStart_607242 := by decide
  rcases family_descends (prefixWord ++ tailWord_607242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607275 : List Nat := [1, 1, 1, 1, 2, 1, 5, 5, 1, 1, 4]
def baseStart_607275 : Nat := 118140960795 + 607275 * 2 ^ 59
def prefixEnd_607275 : Nat := 4983230072969 + 3 ^ 40 * 607275 * 2
def baseEnd_607275 : Nat := 311823964459216767469699

theorem tailTrace_607275 : CollatzResearch.WordTrace tailWord_607275 prefixEnd_607275 311823964459216767469699 := by
  unfold tailWord_607275
  simp only [CollatzResearch.WordTrace]
  refine ⟨22149138874953864157991279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14766092583302576105327519 22149138874953864157991279)
  ·
    refine ⟨33223708312430796236986919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22149138874953864157991279 33223708312430796236986919)
    ·
      refine ⟨49835562468646194355480379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33223708312430796236986919 49835562468646194355480379)
      ·
        refine ⟨74753343702969291533220569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49835562468646194355480379 74753343702969291533220569)
        ·
          refine ⟨56065007777226968649915427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74753343702969291533220569 56065007777226968649915427)
          ·
            refine ⟨84097511665840452974873141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56065007777226968649915427 84097511665840452974873141)
            ·
              refine ⟨7884141718672542466394357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84097511665840452974873141 7884141718672542466394357)
              ·
                refine ⟨739138286125550856224471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7884141718672542466394357 739138286125550856224471)
                ·
                  refine ⟨1108707429188326284336707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739138286125550856224471 1108707429188326284336707)
                  ·
                    refine ⟨1663061143782489426505061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1108707429188326284336707 1663061143782489426505061)
                    ·
                      refine ⟨311823964459216767469699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1663061143782489426505061 311823964459216767469699)
                      ·
                        rfl

theorem cell23_607275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 1, 4].length) (baseStart_607275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607275 prefixEnd_607275 := by exact prefixLift 607275
  have htrace : WordTrace (prefixWord ++ tailWord_607275) baseStart_607275 baseEnd_607275 := by
    simpa [prefixWord, tailWord_607275, baseEnd_607275] using wordTrace_append hprefix tailTrace_607275
  have hstable : (prefixWord ++ tailWord_607275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607275).length < 2 ^ (prefixWord ++ tailWord_607275).sum := by decide
  have hdescent : baseEnd_607275 < baseStart_607275 := by decide
  rcases family_descends (prefixWord ++ tailWord_607275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607286 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_607286 : Nat := 118140960795 + 607286 * 2 ^ 59
def prefixEnd_607286 : Nat := 4983230072969 + 3 ^ 40 * 607286 * 2
def baseEnd_607286 : Nat := 311829612746416224432149

theorem tailTrace_607286 : CollatzResearch.WordTrace tailWord_607286 prefixEnd_607286 311829612746416224432149 := by
  unfold tailWord_607286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1384346254869625814790107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14766360051942675357761141 1384346254869625814790107)
  ·
    refine ⟨2076519382304438722185161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1384346254869625814790107 2076519382304438722185161)
    ·
      refine ⟨1557389536728329041638871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2076519382304438722185161 1557389536728329041638871)
      ·
        refine ⟨2336084305092493562458307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1557389536728329041638871 2336084305092493562458307)
        ·
          refine ⟨3504126457638740343687461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2336084305092493562458307 3504126457638740343687461)
          ·
            refine ⟨657023710807263814441399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3504126457638740343687461 657023710807263814441399)
            ·
              refine ⟨985535566210895721662099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657023710807263814441399 985535566210895721662099)
              ·
                refine ⟨1478303349316343582493149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 985535566210895721662099 1478303349316343582493149)
                ·
                  refine ⟨554363755993628843434931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1478303349316343582493149 554363755993628843434931)
                  ·
                    refine ⟨831545633990443265152397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 554363755993628843434931 831545633990443265152397)
                    ·
                      refine ⟨311829612746416224432149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 831545633990443265152397 311829612746416224432149)
                      ·
                        rfl

theorem cell23_607286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_607286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607286 prefixEnd_607286 := by exact prefixLift 607286
  have htrace : WordTrace (prefixWord ++ tailWord_607286) baseStart_607286 baseEnd_607286 := by
    simpa [prefixWord, tailWord_607286, baseEnd_607286] using wordTrace_append hprefix tailTrace_607286
  have hstable : (prefixWord ++ tailWord_607286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607286).length < 2 ^ (prefixWord ++ tailWord_607286).sum := by decide
  have hdescent : baseEnd_607286 < baseStart_607286 := by decide
  rcases family_descends (prefixWord ++ tailWord_607286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607295 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 3]
def baseStart_607295 : Nat := 118140960795 + 607295 * 2 ^ 59
def prefixEnd_607295 : Nat := 4983230072969 + 3 ^ 40 * 607295 * 2
def baseEnd_607295 : Nat := 311834234072306689219607

theorem tailTrace_607295 : CollatzResearch.WordTrace tailWord_607295 prefixEnd_607295 311834234072306689219607 := by
  unfold tailWord_607295
  simp only [CollatzResearch.WordTrace]
  refine ⟨22149868334881407573719339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14766578889920938382479559 22149868334881407573719339)
  ·
    refine ⟨33224802502322111360579009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22149868334881407573719339 33224802502322111360579009)
    ·
      refine ⟨24918601876741583520434257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33224802502322111360579009 24918601876741583520434257)
      ·
        refine ⟨18688951407556187640325693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24918601876741583520434257 18688951407556187640325693)
        ·
          refine ⟨7008356777833570365122135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18688951407556187640325693 7008356777833570365122135)
          ·
            refine ⟨10512535166750355547683203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7008356777833570365122135 10512535166750355547683203)
            ·
              refine ⟨15768802750125533321524805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10512535166750355547683203 15768802750125533321524805)
              ·
                refine ⟨2956650515648537497785901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15768802750125533321524805 2956650515648537497785901)
                ·
                  refine ⟨1108743943368201561669713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2956650515648537497785901 1108743943368201561669713)
                  ·
                    refine ⟨831557957526151171252285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1108743943368201561669713 831557957526151171252285)
                    ·
                      refine ⟨311834234072306689219607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 831557957526151171252285 311834234072306689219607)
                      ·
                        rfl

theorem cell23_607295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_607295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607295 prefixEnd_607295 := by exact prefixLift 607295
  have htrace : WordTrace (prefixWord ++ tailWord_607295) baseStart_607295 baseEnd_607295 := by
    simpa [prefixWord, tailWord_607295, baseEnd_607295] using wordTrace_append hprefix tailTrace_607295
  have hstable : (prefixWord ++ tailWord_607295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607295).length < 2 ^ (prefixWord ++ tailWord_607295).sum := by decide
  have hdescent : baseEnd_607295 < baseStart_607295 := by decide
  rcases family_descends (prefixWord ++ tailWord_607295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607309 : List Nat := [1, 6, 1, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_607309 : Nat := 118140960795 + 607309 * 2 ^ 59
def prefixEnd_607309 : Nat := 4983230072969 + 3 ^ 40 * 607309 * 2
def baseEnd_607309 : Nat := 311841422801469634444543

theorem tailTrace_607309 : CollatzResearch.WordTrace tailWord_607309 prefixEnd_607309 311841422801469634444543 := by
  unfold tailWord_607309
  simp only [CollatzResearch.WordTrace]
  refine ⟨22150378956830687964728981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14766919304553791976485987 22150378956830687964728981)
  ·
    refine ⟨1038299013601438498346671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22150378956830687964728981 1038299013601438498346671)
    ·
      refine ⟨1557448520402157747520007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1038299013601438498346671 1557448520402157747520007)
      ·
        refine ⟨2336172780603236621280011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1557448520402157747520007 2336172780603236621280011)
        ·
          refine ⟨3504259170904854931920017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2336172780603236621280011 3504259170904854931920017)
          ·
            refine ⟨2628194378178641198940013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3504259170904854931920017 2628194378178641198940013)
            ·
              refine ⟨985572891816990449602505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2628194378178641198940013 985572891816990449602505)
              ·
                refine ⟨739179668862742837201879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 985572891816990449602505 739179668862742837201879)
                ·
                  refine ⟨1108769503294114255802819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739179668862742837201879 1108769503294114255802819)
                  ·
                    refine ⟨1663154254941171383704229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1108769503294114255802819 1663154254941171383704229)
                    ·
                      refine ⟨311841422801469634444543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1663154254941171383704229 311841422801469634444543)
                      ·
                        rfl

theorem cell23_607309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_607309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607309 prefixEnd_607309 := by exact prefixLift 607309
  have htrace : WordTrace (prefixWord ++ tailWord_607309) baseStart_607309 baseEnd_607309 := by
    simpa [prefixWord, tailWord_607309, baseEnd_607309] using wordTrace_append hprefix tailTrace_607309
  have hstable : (prefixWord ++ tailWord_607309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607309).length < 2 ^ (prefixWord ++ tailWord_607309).sum := by decide
  have hdescent : baseEnd_607309 < baseStart_607309 := by decide
  rcases family_descends (prefixWord ++ tailWord_607309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607336 : List Nat := [2, 1, 4, 4, 1, 1, 2, 2, 2, 4]
def baseStart_607336 : Nat := 118140960795 + 607336 * 2 ^ 59
def prefixEnd_607336 : Nat := 4983230072969 + 3 ^ 40 * 607336 * 2
def baseEnd_607336 : Nat := 103951762259713676268973

theorem tailTrace_607336 : CollatzResearch.WordTrace tailWord_607336 prefixEnd_607336 103951762259713676268973 := by
  unfold tailWord_607336
  simp only [CollatzResearch.WordTrace]
  refine ⟨11075681863866435787980931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14767575818488581050641241 11075681863866435787980931)
  ·
    refine ⟨16613522795799653681971397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11075681863866435787980931 16613522795799653681971397)
    ·
      refine ⟨3115035524212435065369637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16613522795799653681971397 3115035524212435065369637)
      ·
        refine ⟨584069160789831574756807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3115035524212435065369637 584069160789831574756807)
        ·
          refine ⟨876103741184747362135211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584069160789831574756807 876103741184747362135211)
          ·
            refine ⟨1314155611777121043202817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876103741184747362135211 1314155611777121043202817)
            ·
              refine ⟨985616708832840782402113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1314155611777121043202817 985616708832840782402113)
              ·
                refine ⟨739212531624630586801585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 985616708832840782402113 739212531624630586801585)
                ·
                  refine ⟨554409398718472940101189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 739212531624630586801585 554409398718472940101189)
                  ·
                    refine ⟨103951762259713676268973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 554409398718472940101189 103951762259713676268973)
                    ·
                      rfl

theorem cell23_607336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_607336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607336 prefixEnd_607336 := by exact prefixLift 607336
  have htrace : WordTrace (prefixWord ++ tailWord_607336) baseStart_607336 baseEnd_607336 := by
    simpa [prefixWord, tailWord_607336, baseEnd_607336] using wordTrace_append hprefix tailTrace_607336
  have hstable : (prefixWord ++ tailWord_607336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607336).length < 2 ^ (prefixWord ++ tailWord_607336).sum := by decide
  have hdescent : baseEnd_607336 < baseStart_607336 := by decide
  rcases family_descends (prefixWord ++ tailWord_607336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607349 : List Nat := [1, 3, 4, 3, 1, 2, 1, 8]
def baseStart_607349 : Nat := 118140960795 + 607349 * 2 ^ 59
def prefixEnd_607349 : Nat := 4983230072969 + 3 ^ 40 * 607349 * 2
def baseEnd_607349 : Nat := 11550443038061091775717

theorem tailTrace_607349 : CollatzResearch.WordTrace tailWord_607349 prefixEnd_607349 11550443038061091775717 := by
  unfold tailWord_607349
  simp only [CollatzResearch.WordTrace]
  refine ⟨22151837876685774796185101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14767891917790516530790067 22151837876685774796185101)
  ·
    refine ⟨8306939203757165548569413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22151837876685774796185101 8306939203757165548569413)
    ·
      refine ⟨1557551100704468540356765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8306939203757165548569413 1557551100704468540356765)
      ·
        refine ⟨584081662764175702633787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1557551100704468540356765 584081662764175702633787)
        ·
          refine ⟨876122494146263553950681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584081662764175702633787 876122494146263553950681)
          ·
            refine ⟨657091870609697665463011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 876122494146263553950681 657091870609697665463011)
            ·
              refine ⟨985637805914546498194517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657091870609697665463011 985637805914546498194517)
              ·
                refine ⟨11550443038061091775717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 985637805914546498194517 11550443038061091775717)
                ·
                  rfl

theorem cell23_607349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 8].length) (baseStart_607349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607349 prefixEnd_607349 := by exact prefixLift 607349
  have htrace : WordTrace (prefixWord ++ tailWord_607349) baseStart_607349 baseEnd_607349 := by
    simpa [prefixWord, tailWord_607349, baseEnd_607349] using wordTrace_append hprefix tailTrace_607349
  have hstable : (prefixWord ++ tailWord_607349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607349).length < 2 ^ (prefixWord ++ tailWord_607349).sum := by decide
  have hdescent : baseEnd_607349 < baseStart_607349 := by decide
  rcases family_descends (prefixWord ++ tailWord_607349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607352 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 3, 3, 2]
def baseStart_607352 : Nat := 118140960795 + 607352 * 2 ^ 59
def prefixEnd_607352 : Nat := 4983230072969 + 3 ^ 40 * 607352 * 2
def baseEnd_607352 : Nat := 311863502469612966206845

theorem tailTrace_607352 : CollatzResearch.WordTrace tailWord_607352 prefixEnd_607352 311863502469612966206845 := by
  unfold tailWord_607352
  simp only [CollatzResearch.WordTrace]
  refine ⟨11075973647837453154272155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14767964863783270872362873 11075973647837453154272155)
  ·
    refine ⟨16613960471756179731408233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11075973647837453154272155 16613960471756179731408233)
    ·
      refine ⟨12460470353817134798556175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16613960471756179731408233 12460470353817134798556175)
      ·
        refine ⟨18690705530725702197834263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12460470353817134798556175 18690705530725702197834263)
        ·
          refine ⟨28036058296088553296751395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18690705530725702197834263 28036058296088553296751395)
          ·
            refine ⟨42054087444132829945127093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28036058296088553296751395 42054087444132829945127093)
            ·
              refine ⟨3942570697887452807355665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42054087444132829945127093 3942570697887452807355665)
              ·
                refine ⟨2956928023415589605516749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3942570697887452807355665 2956928023415589605516749)
                ·
                  refine ⟨1108848008780846102068781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2956928023415589605516749 1108848008780846102068781)
                  ·
                    refine ⟨415818003292817288275793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1108848008780846102068781 415818003292817288275793)
                    ·
                      refine ⟨311863502469612966206845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 415818003292817288275793 311863502469612966206845)
                      ·
                        rfl

theorem cell23_607352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 3, 3, 2].length) (baseStart_607352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607352 prefixEnd_607352 := by exact prefixLift 607352
  have htrace : WordTrace (prefixWord ++ tailWord_607352) baseStart_607352 baseEnd_607352 := by
    simpa [prefixWord, tailWord_607352, baseEnd_607352] using wordTrace_append hprefix tailTrace_607352
  have hstable : (prefixWord ++ tailWord_607352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607352).length < 2 ^ (prefixWord ++ tailWord_607352).sum := by decide
  have hdescent : baseEnd_607352 < baseStart_607352 := by decide
  rcases family_descends (prefixWord ++ tailWord_607352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607386 : List Nat := [3, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2]
def baseStart_607386 : Nat := 118140960795 + 607386 * 2 ^ 59
def prefixEnd_607386 : Nat := 4983230072969 + 3 ^ 40 * 607386 * 2
def baseEnd_607386 : Nat := 311880960811865833181689

theorem tailTrace_607386 : CollatzResearch.WordTrace tailWord_607386 prefixEnd_607386 311880960811865833181689 := by
  unfold tailWord_607386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5538296844387932528820503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14768791585034486743521341 5538296844387932528820503)
  ·
    refine ⟨8307445266581898793230755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5538296844387932528820503 8307445266581898793230755)
    ·
      refine ⟨12461167899872848189846133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8307445266581898793230755 12461167899872848189846133)
      ·
        refine ⟨1168234490613079517798075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12461167899872848189846133 1168234490613079517798075)
        ·
          refine ⟨1752351735919619276697113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1168234490613079517798075 1752351735919619276697113)
          ·
            refine ⟨1314263801939714457522835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1752351735919619276697113 1314263801939714457522835)
            ·
              refine ⟨1971395702909571686284253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1314263801939714457522835 1971395702909571686284253)
              ·
                refine ⟨739273388591089382356595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1971395702909571686284253 739273388591089382356595)
                ·
                  refine ⟨1108910082886634073534893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739273388591089382356595 1108910082886634073534893)
                  ·
                    refine ⟨415841281082487777575585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1108910082886634073534893 415841281082487777575585)
                    ·
                      refine ⟨311880960811865833181689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 415841281082487777575585 311880960811865833181689)
                      ·
                        rfl

theorem cell23_607386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_607386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607386 prefixEnd_607386 := by exact prefixLift 607386
  have htrace : WordTrace (prefixWord ++ tailWord_607386) baseStart_607386 baseEnd_607386 := by
    simpa [prefixWord, tailWord_607386, baseEnd_607386] using wordTrace_append hprefix tailTrace_607386
  have hstable : (prefixWord ++ tailWord_607386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607386).length < 2 ^ (prefixWord ++ tailWord_607386).sum := by decide
  have hdescent : baseEnd_607386 < baseStart_607386 := by decide
  rcases family_descends (prefixWord ++ tailWord_607386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607422 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 7]
def baseStart_607422 : Nat := 118140960795 + 607422 * 2 ^ 59
def prefixEnd_607422 : Nat := 4983230072969 + 3 ^ 40 * 607422 * 2
def baseEnd_607422 : Nat := 34655494012825299147947

theorem tailTrace_607422 : CollatzResearch.WordTrace tailWord_607422 prefixEnd_607422 34655494012825299147947 := by
  unfold tailWord_607422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2769312550677663532949065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14769666936947538842395013 2769312550677663532949065)
  ·
    refine ⟨2076984413008247649711799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2769312550677663532949065 2076984413008247649711799)
    ·
      refine ⟨3115476619512371474567699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2076984413008247649711799 3115476619512371474567699)
      ·
        refine ⟨4673214929268557211851549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3115476619512371474567699 4673214929268557211851549)
        ·
          refine ⟨1752455598475708954444331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4673214929268557211851549 1752455598475708954444331)
          ·
            refine ⟨2628683397713563431666497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752455598475708954444331 2628683397713563431666497)
            ·
              refine ⟨1971512548285172573749873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2628683397713563431666497 1971512548285172573749873)
              ·
                refine ⟨1478634411213879430312405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1971512548285172573749873 1478634411213879430312405)
                ·
                  refine ⟨34655494012825299147947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1478634411213879430312405 34655494012825299147947)
                  ·
                    rfl

theorem cell23_607422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_607422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607422 prefixEnd_607422 := by exact prefixLift 607422
  have htrace : WordTrace (prefixWord ++ tailWord_607422) baseStart_607422 baseEnd_607422 := by
    simpa [prefixWord, tailWord_607422, baseEnd_607422] using wordTrace_append hprefix tailTrace_607422
  have hstable : (prefixWord ++ tailWord_607422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607422).length < 2 ^ (prefixWord ++ tailWord_607422).sum := by decide
  have hdescent : baseEnd_607422 < baseStart_607422 := by decide
  rcases family_descends (prefixWord ++ tailWord_607422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607482 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 5, 4]
def baseStart_607482 : Nat := 118140960795 + 607482 * 2 ^ 59
def prefixEnd_607482 : Nat := 4983230072969 + 3 ^ 40 * 607482 * 2
def baseEnd_607482 : Nat := 103976751651565819193749

theorem tailTrace_607482 : CollatzResearch.WordTrace tailWord_607482 prefixEnd_607482 103976751651565819193749 := by
  unfold tailWord_607482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5539172196300984627694175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14771125856802625673851133 5539172196300984627694175)
  ·
    refine ⟨8308758294451476941541263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5539172196300984627694175 8308758294451476941541263)
    ·
      refine ⟨12463137441677215412311895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8308758294451476941541263 12463137441677215412311895)
      ·
        refine ⟨18694706162515823118467843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12463137441677215412311895 18694706162515823118467843)
        ·
          refine ⟨28042059243773734677701765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18694706162515823118467843 28042059243773734677701765)
          ·
            refine ⟨5257886108207575252069081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28042059243773734677701765 5257886108207575252069081)
            ·
              refine ⟨3943414581155681439051811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5257886108207575252069081 3943414581155681439051811)
              ·
                refine ⟨5915121871733522158577717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3943414581155681439051811 5915121871733522158577717)
                ·
                  refine ⟨554542675475017702366661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5915121871733522158577717 554542675475017702366661)
                  ·
                    refine ⟨103976751651565819193749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 554542675475017702366661 103976751651565819193749)
                    ·
                      rfl

theorem cell23_607482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_607482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607482 prefixEnd_607482 := by exact prefixLift 607482
  have htrace : WordTrace (prefixWord ++ tailWord_607482) baseStart_607482 baseEnd_607482 := by
    simpa [prefixWord, tailWord_607482, baseEnd_607482] using wordTrace_append hprefix tailTrace_607482
  have hstable : (prefixWord ++ tailWord_607482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607482).length < 2 ^ (prefixWord ++ tailWord_607482).sum := by decide
  have hdescent : baseEnd_607482 < baseStart_607482 := by decide
  rcases family_descends (prefixWord ++ tailWord_607482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607485 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_607485 : Nat := 118140960795 + 607485 * 2 ^ 59
def prefixEnd_607485 : Nat := 4983230072969 + 3 ^ 40 * 607485 * 2
def baseEnd_607485 : Nat := 311931795396660945843733

theorem tailTrace_607485 : CollatzResearch.WordTrace tailWord_607485 prefixEnd_607485 311931795396660945843733 := by
  unfold tailWord_607485
  simp only [CollatzResearch.WordTrace]
  refine ⟨22156798204193070023135909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14771198802795380015423939 22156798204193070023135909)
  ·
    refine ⟨4154399663286200629337983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22156798204193070023135909 4154399663286200629337983)
    ·
      refine ⟨6231599494929300944006975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4154399663286200629337983 6231599494929300944006975)
      ·
        refine ⟨9347399242393951416010463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6231599494929300944006975 9347399242393951416010463)
        ·
          refine ⟨14021098863590927124015695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9347399242393951416010463 14021098863590927124015695)
          ·
            refine ⟨21031648295386390686023543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14021098863590927124015695 21031648295386390686023543)
            ·
              refine ⟨31547472443079586029035315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21031648295386390686023543 31547472443079586029035315)
              ·
                refine ⟨47321208664619379043552973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31547472443079586029035315 47321208664619379043552973)
                ·
                  refine ⟨17745453249232267141332365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47321208664619379043552973 17745453249232267141332365)
                  ·
                    refine ⟨6654544968462100177999637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17745453249232267141332365 6654544968462100177999637)
                    ·
                      refine ⟨311931795396660945843733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6654544968462100177999637 311931795396660945843733)
                      ·
                        rfl

theorem cell23_607485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_607485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607485 prefixEnd_607485 := by exact prefixLift 607485
  have htrace : WordTrace (prefixWord ++ tailWord_607485) baseStart_607485 baseEnd_607485 := by
    simpa [prefixWord, tailWord_607485, baseEnd_607485] using wordTrace_append hprefix tailTrace_607485
  have hstable : (prefixWord ++ tailWord_607485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607485).length < 2 ^ (prefixWord ++ tailWord_607485).sum := by decide
  have hdescent : baseEnd_607485 < baseStart_607485 := by decide
  rcases family_descends (prefixWord ++ tailWord_607485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607489 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_607489 : Nat := 118140960795 + 607489 * 2 ^ 59
def prefixEnd_607489 : Nat := 4983230072969 + 3 ^ 40 * 607489 * 2
def baseEnd_607489 : Nat := 311933849319278930193715

theorem tailTrace_607489 : CollatzResearch.WordTrace tailWord_607489 prefixEnd_607489 311933849319278930193715 := by
  unfold tailWord_607489
  simp only [CollatzResearch.WordTrace]
  refine ⟨22156944096178578706281521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14771296064119052470854347 22156944096178578706281521)
  ·
    refine ⟨16617708072133934029711141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22156944096178578706281521 16617708072133934029711141)
    ·
      refine ⟨3115820263525112630570839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16617708072133934029711141 3115820263525112630570839)
      ·
        refine ⟨4673730395287668945856259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3115820263525112630570839 4673730395287668945856259)
        ·
          refine ⟨7010595592931503418784389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4673730395287668945856259 7010595592931503418784389)
          ·
            refine ⟨1314486673674656891022073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7010595592931503418784389 1314486673674656891022073)
            ·
              refine ⟨985865005255992668266555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1314486673674656891022073 985865005255992668266555)
              ·
                refine ⟨1478797507883989002399833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 985865005255992668266555 1478797507883989002399833)
                ·
                  refine ⟨1109098130912991751799875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1478797507883989002399833 1109098130912991751799875)
                  ·
                    refine ⟨1663647196369487627699813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1109098130912991751799875 1663647196369487627699813)
                    ·
                      refine ⟨311933849319278930193715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1663647196369487627699813 311933849319278930193715)
                      ·
                        rfl

theorem cell23_607489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_607489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607489 prefixEnd_607489 := by exact prefixLift 607489
  have htrace : WordTrace (prefixWord ++ tailWord_607489) baseStart_607489 baseEnd_607489 := by
    simpa [prefixWord, tailWord_607489, baseEnd_607489] using wordTrace_append hprefix tailTrace_607489
  have hstable : (prefixWord ++ tailWord_607489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607489).length < 2 ^ (prefixWord ++ tailWord_607489).sum := by decide
  have hdescent : baseEnd_607489 < baseStart_607489 := by decide
  rcases family_descends (prefixWord ++ tailWord_607489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607512 : List Nat := [2, 1, 2, 3, 1, 3, 1, 4, 6]
def baseStart_607512 : Nat := 118140960795 + 607512 * 2 ^ 59
def prefixEnd_607512 : Nat := 4983230072969 + 3 ^ 40 * 607512 * 2
def baseEnd_607512 : Nat := 34660628819370260022901

theorem tailTrace_607512 : CollatzResearch.WordTrace tailWord_607512 prefixEnd_607512 34660628819370260022901 := by
  unfold tailWord_607512
  simp only [CollatzResearch.WordTrace]
  refine ⟨11078891487547626817184395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14771855316730169089579193 11078891487547626817184395)
  ·
    refine ⟨16618337231321440225776593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11078891487547626817184395 16618337231321440225776593)
    ·
      refine ⟨12463752923491080169332445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16618337231321440225776593 12463752923491080169332445)
      ·
        refine ⟨4673907346309155063499667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12463752923491080169332445 4673907346309155063499667)
        ·
          refine ⟨7010861019463732595249501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4673907346309155063499667 7010861019463732595249501)
          ·
            refine ⟨2629072882298899723218563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7010861019463732595249501 2629072882298899723218563)
            ·
              refine ⟨3943609323448349584827845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2629072882298899723218563 3943609323448349584827845)
              ·
                refine ⟨739426748146565547155221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3943609323448349584827845 739426748146565547155221)
                ·
                  refine ⟨34660628819370260022901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 739426748146565547155221 34660628819370260022901)
                  ·
                    rfl

theorem cell23_607512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 6].length) (baseStart_607512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607512 prefixEnd_607512 := by exact prefixLift 607512
  have htrace : WordTrace (prefixWord ++ tailWord_607512) baseStart_607512 baseEnd_607512 := by
    simpa [prefixWord, tailWord_607512, baseEnd_607512] using wordTrace_append hprefix tailTrace_607512
  have hstable : (prefixWord ++ tailWord_607512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607512).length < 2 ^ (prefixWord ++ tailWord_607512).sum := by decide
  have hdescent : baseEnd_607512 < baseStart_607512 := by decide
  rcases family_descends (prefixWord ++ tailWord_607512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607515 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 6]
def baseStart_607515 : Nat := 118140960795 + 607515 * 2 ^ 59
def prefixEnd_607515 : Nat := 4983230072969 + 3 ^ 40 * 607515 * 2
def baseEnd_607515 : Nat := 311947199816295828468595

theorem tailTrace_607515 : CollatzResearch.WordTrace tailWord_607515 prefixEnd_607515 311947199816295828468595 := by
  unfold tailWord_607515
  simp only [CollatzResearch.WordTrace]
  refine ⟨22157892394084385146727999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14771928262722923431151999 22157892394084385146727999)
  ·
    refine ⟨33236838591126577720091999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22157892394084385146727999 33236838591126577720091999)
    ·
      refine ⟨49855257886689866580137999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33236838591126577720091999 49855257886689866580137999)
      ·
        refine ⟨74782886830034799870206999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49855257886689866580137999 74782886830034799870206999)
        ·
          refine ⟨112174330245052199805310499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74782886830034799870206999 112174330245052199805310499)
          ·
            refine ⟨168261495367578299707965749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112174330245052199805310499 168261495367578299707965749)
            ·
              refine ⟨15774515190710465597621789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168261495367578299707965749 15774515190710465597621789)
              ·
                refine ⟨5915443196516424599108171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15774515190710465597621789 5915443196516424599108171)
                ·
                  refine ⟨8873164794774636898662257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5915443196516424599108171 8873164794774636898662257)
                  ·
                    refine ⟨6654873596080977673996693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8873164794774636898662257 6654873596080977673996693)
                    ·
                      refine ⟨311947199816295828468595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6654873596080977673996693 311947199816295828468595)
                      ·
                        rfl

theorem cell23_607515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 6].length) (baseStart_607515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607515 prefixEnd_607515 := by exact prefixLift 607515
  have htrace : WordTrace (prefixWord ++ tailWord_607515) baseStart_607515 baseEnd_607515 := by
    simpa [prefixWord, tailWord_607515, baseEnd_607515] using wordTrace_append hprefix tailTrace_607515
  have hstable : (prefixWord ++ tailWord_607515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607515).length < 2 ^ (prefixWord ++ tailWord_607515).sum := by decide
  have hdescent : baseEnd_607515 < baseStart_607515 := by decide
  rcases family_descends (prefixWord ++ tailWord_607515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607535 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 7]
def baseStart_607535 : Nat := 118140960795 + 607535 * 2 ^ 59
def prefixEnd_607535 : Nat := 4983230072969 + 3 ^ 40 * 607535 * 2
def baseEnd_607535 : Nat := 311957469429385750218503

theorem tailTrace_607535 : CollatzResearch.WordTrace tailWord_607535 prefixEnd_607535 311957469429385750218503 := by
  unfold tailWord_607535
  simp only [CollatzResearch.WordTrace]
  refine ⟨22158621854011928562456059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14772414569341285708304039 22158621854011928562456059)
  ·
    refine ⟨33237932781017892843684089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22158621854011928562456059 33237932781017892843684089)
    ·
      refine ⟨24928449585763419632763067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33237932781017892843684089 24928449585763419632763067)
      ·
        refine ⟨37392674378645129449144601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24928449585763419632763067 37392674378645129449144601)
        ·
          refine ⟨28044505783983847086858451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37392674378645129449144601 28044505783983847086858451)
          ·
            refine ⟨42066758675975770630287677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28044505783983847086858451 42066758675975770630287677)
            ·
              refine ⟨15775034503490913986357879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42066758675975770630287677 15775034503490913986357879)
              ·
                refine ⟨23662551755236370979536819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15775034503490913986357879 23662551755236370979536819)
                ·
                  refine ⟨35493827632854556469305229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23662551755236370979536819 35493827632854556469305229)
                  ·
                    refine ⟨13310185362320458675989461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35493827632854556469305229 13310185362320458675989461)
                    ·
                      refine ⟨311957469429385750218503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13310185362320458675989461 311957469429385750218503)
                      ·
                        rfl

theorem cell23_607535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_607535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607535 prefixEnd_607535 := by exact prefixLift 607535
  have htrace : WordTrace (prefixWord ++ tailWord_607535) baseStart_607535 baseEnd_607535 := by
    simpa [prefixWord, tailWord_607535, baseEnd_607535] using wordTrace_append hprefix tailTrace_607535
  have hstable : (prefixWord ++ tailWord_607535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607535).length < 2 ^ (prefixWord ++ tailWord_607535).sum := by decide
  have hdescent : baseEnd_607535 < baseStart_607535 := by decide
  rcases family_descends (prefixWord ++ tailWord_607535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607539 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 5, 1, 3]
def baseStart_607539 : Nat := 118140960795 + 607539 * 2 ^ 59
def prefixEnd_607539 : Nat := 4983230072969 + 3 ^ 40 * 607539 * 2
def baseEnd_607539 : Nat := 311959523352003734568485

theorem tailTrace_607539 : CollatzResearch.WordTrace tailWord_607539 prefixEnd_607539 311959523352003734568485 := by
  unfold tailWord_607539
  simp only [CollatzResearch.WordTrace]
  refine ⟨22158767745997437245601671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14772511830664958163734447 22158767745997437245601671)
  ·
    refine ⟨33238151618996155868402507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22158767745997437245601671 33238151618996155868402507)
    ·
      refine ⟨49857227428494233802603761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33238151618996155868402507 49857227428494233802603761)
      ·
        refine ⟨37392920571370675351952821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49857227428494233802603761 37392920571370675351952821)
        ·
          refine ⟨3505586303566000814245577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37392920571370675351952821 3505586303566000814245577)
          ·
            refine ⟨2629189727674500610684183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3505586303566000814245577 2629189727674500610684183)
            ·
              refine ⟨3943784591511750916026275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2629189727674500610684183 3943784591511750916026275)
              ·
                refine ⟨5915676887267626374039413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3943784591511750916026275 5915676887267626374039413)
                ·
                  refine ⟨554594708181339972566195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5915676887267626374039413 554594708181339972566195)
                  ·
                    refine ⟨831892062272009958849293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 554594708181339972566195 831892062272009958849293)
                    ·
                      refine ⟨311959523352003734568485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 831892062272009958849293 311959523352003734568485)
                      ·
                        rfl

theorem cell23_607539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 1, 3].length) (baseStart_607539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607539 prefixEnd_607539 := by exact prefixLift 607539
  have htrace : WordTrace (prefixWord ++ tailWord_607539) baseStart_607539 baseEnd_607539 := by
    simpa [prefixWord, tailWord_607539, baseEnd_607539] using wordTrace_append hprefix tailTrace_607539
  have hstable : (prefixWord ++ tailWord_607539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607539).length < 2 ^ (prefixWord ++ tailWord_607539).sum := by decide
  have hdescent : baseEnd_607539 < baseStart_607539 := by decide
  rcases family_descends (prefixWord ++ tailWord_607539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607559 : List Nat := [1, 1, 4, 1, 2, 4, 1, 3, 1, 5]
def baseStart_607559 : Nat := 118140960795 + 607559 * 2 ^ 59
def prefixEnd_607559 : Nat := 4983230072969 + 3 ^ 40 * 607559 * 2
def baseEnd_607559 : Nat := 103989930988364552106131

theorem tailTrace_607559 : CollatzResearch.WordTrace tailWord_607559 prefixEnd_607559 103989930988364552106131 := by
  unfold tailWord_607559
  simp only [CollatzResearch.WordTrace]
  refine ⟨22159497205924980661329731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14772998137283320440886487 22159497205924980661329731)
  ·
    refine ⟨33239245808887470991994597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22159497205924980661329731 33239245808887470991994597)
    ·
      refine ⟨6232358589166400810998987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33239245808887470991994597 6232358589166400810998987)
      ·
        refine ⟨9348537883749601216498481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6232358589166400810998987 9348537883749601216498481)
        ·
          refine ⟨7011403412812200912373861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9348537883749601216498481 7011403412812200912373861)
          ·
            refine ⟨1314638139902287671070099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7011403412812200912373861 1314638139902287671070099)
            ·
              refine ⟨1971957209853431506605149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1314638139902287671070099 1971957209853431506605149)
              ·
                refine ⟨739483953695036814976931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1971957209853431506605149 739483953695036814976931)
                ·
                  refine ⟨1109225930542555222465397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739483953695036814976931 1109225930542555222465397)
                  ·
                    refine ⟨103989930988364552106131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1109225930542555222465397 103989930988364552106131)
                    ·
                      rfl

theorem cell23_607559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_607559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607559 prefixEnd_607559 := by exact prefixLift 607559
  have htrace : WordTrace (prefixWord ++ tailWord_607559) baseStart_607559 baseEnd_607559 := by
    simpa [prefixWord, tailWord_607559, baseEnd_607559] using wordTrace_append hprefix tailTrace_607559
  have hstable : (prefixWord ++ tailWord_607559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607559).length < 2 ^ (prefixWord ++ tailWord_607559).sum := by decide
  have hdescent : baseEnd_607559 < baseStart_607559 := by decide
  rcases family_descends (prefixWord ++ tailWord_607559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607573 : List Nat := [1, 3, 2, 2, 3, 1, 2, 4, 1, 1, 3]
def baseStart_607573 : Nat := 118140960795 + 607573 * 2 ^ 59
def prefixEnd_607573 : Nat := 4983230072969 + 3 ^ 40 * 607573 * 2
def baseEnd_607573 : Nat := 311976981694256601543329

theorem tailTrace_607573 : CollatzResearch.WordTrace tailWord_607573 prefixEnd_607573 311976981694256601543329 := by
  unfold tailWord_607573
  simp only [CollatzResearch.WordTrace]
  refine ⟨22160007827874261052339373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14773338551916174034892915 22160007827874261052339373)
  ·
    refine ⟨8310002935452847894627265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22160007827874261052339373 8310002935452847894627265)
    ·
      refine ⟨6232502201589635920970449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8310002935452847894627265 6232502201589635920970449)
      ·
        refine ⟨4674376651192226940727837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6232502201589635920970449 4674376651192226940727837)
        ·
          refine ⟨1752891244197085102772939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4674376651192226940727837 1752891244197085102772939)
          ·
            refine ⟨2629336866295627654159409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752891244197085102772939 2629336866295627654159409)
            ·
              refine ⟨1972002649721720740619557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2629336866295627654159409 1972002649721720740619557)
              ·
                refine ⟨369750496822822638866167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1972002649721720740619557 369750496822822638866167)
                ·
                  refine ⟨554625745234233958299251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 369750496822822638866167 554625745234233958299251)
                  ·
                    refine ⟨831938617851350937448877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 554625745234233958299251 831938617851350937448877)
                    ·
                      refine ⟨311976981694256601543329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 831938617851350937448877 311976981694256601543329)
                      ·
                        rfl

theorem cell23_607573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_607573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607573 prefixEnd_607573 := by exact prefixLift 607573
  have htrace : WordTrace (prefixWord ++ tailWord_607573) baseStart_607573 baseEnd_607573 := by
    simpa [prefixWord, tailWord_607573, baseEnd_607573] using wordTrace_append hprefix tailTrace_607573
  have hstable : (prefixWord ++ tailWord_607573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607573).length < 2 ^ (prefixWord ++ tailWord_607573).sum := by decide
  have hdescent : baseEnd_607573 < baseStart_607573 := by decide
  rcases family_descends (prefixWord ++ tailWord_607573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607596 : List Nat := [2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 4]
def baseStart_607596 : Nat := 118140960795 + 607596 * 2 ^ 59
def prefixEnd_607596 : Nat := 4983230072969 + 3 ^ 40 * 607596 * 2
def baseEnd_607596 : Nat := 311988791749310011555723

theorem tailTrace_607596 : CollatzResearch.WordTrace tailWord_607596 prefixEnd_607596 311988791749310011555723 := by
  unfold tailWord_607596
  simp only [CollatzResearch.WordTrace]
  refine ⟨11080423353395467990213321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14773897804527290653617761 11080423353395467990213321)
  ·
    refine ⟨8310317515046600992659991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11080423353395467990213321 8310317515046600992659991)
    ·
      refine ⟨12465476272569901488989987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8310317515046600992659991 12465476272569901488989987)
      ·
        refine ⟨18698214408854852233484981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12465476272569901488989987 18698214408854852233484981)
        ·
          refine ⟨1752957600830142396889217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18698214408854852233484981 1752957600830142396889217)
          ·
            refine ⟨1314718200622606797666913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1752957600830142396889217 1314718200622606797666913)
            ·
              refine ⟨986038650466955098250185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1314718200622606797666913 986038650466955098250185)
              ·
                refine ⟨739528987850216323687639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 986038650466955098250185 739528987850216323687639)
                ·
                  refine ⟨1109293481775324485531459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739528987850216323687639 1109293481775324485531459)
                  ·
                    refine ⟨1663940222662986728297189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1109293481775324485531459 1663940222662986728297189)
                    ·
                      refine ⟨311988791749310011555723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1663940222662986728297189 311988791749310011555723)
                      ·
                        rfl

theorem cell23_607596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_607596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607596 prefixEnd_607596 := by exact prefixLift 607596
  have htrace : WordTrace (prefixWord ++ tailWord_607596) baseStart_607596 baseEnd_607596 := by
    simpa [prefixWord, tailWord_607596, baseEnd_607596] using wordTrace_append hprefix tailTrace_607596
  have hstable : (prefixWord ++ tailWord_607596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607596).length < 2 ^ (prefixWord ++ tailWord_607596).sum := by decide
  have hdescent : baseEnd_607596 < baseStart_607596 := by decide
  rcases family_descends (prefixWord ++ tailWord_607596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607602 : List Nat := [3, 2, 1, 2, 1, 2, 3, 9]
def baseStart_607602 : Nat := 118140960795 + 607602 * 2 ^ 59
def prefixEnd_607602 : Nat := 4983230072969 + 3 ^ 40 * 607602 * 2
def baseEnd_607602 : Nat := 11555254541971740299285

theorem tailTrace_607602 : CollatzResearch.WordTrace tailWord_607602 prefixEnd_607602 11555254541971740299285 := by
  unfold tailWord_607602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5540266386192299751286265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14774043696512799336763373 5540266386192299751286265)
  ·
    refine ⟨4155199789644224813464699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5540266386192299751286265 4155199789644224813464699)
    ·
      refine ⟨6232799684466337220197049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4155199789644224813464699 6232799684466337220197049)
      ·
        refine ⟨4674599763349752915147787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6232799684466337220197049 4674599763349752915147787)
        ·
          refine ⟨7011899645024629372721681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4674599763349752915147787 7011899645024629372721681)
          ·
            refine ⟨5258924733768472029541261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7011899645024629372721681 5258924733768472029541261)
            ·
              refine ⟨1972096775163177011077973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5258924733768472029541261 1972096775163177011077973)
              ·
                refine ⟨11555254541971740299285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1972096775163177011077973 11555254541971740299285)
                ·
                  rfl

theorem cell23_607602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 9].length) (baseStart_607602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607602 prefixEnd_607602 := by exact prefixLift 607602
  have htrace : WordTrace (prefixWord ++ tailWord_607602) baseStart_607602 baseEnd_607602 := by
    simpa [prefixWord, tailWord_607602, baseEnd_607602] using wordTrace_append hprefix tailTrace_607602
  have hstable : (prefixWord ++ tailWord_607602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607602).length < 2 ^ (prefixWord ++ tailWord_607602).sum := by decide
  have hdescent : baseEnd_607602 < baseStart_607602 := by decide
  rcases family_descends (prefixWord ++ tailWord_607602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607639 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 2, 7, 2]
def baseStart_607639 : Nat := 118140960795 + 607639 * 2 ^ 59
def prefixEnd_607639 : Nat := 4983230072969 + 3 ^ 40 * 607639 * 2
def baseEnd_607639 : Nat := 312010871417453343318025

theorem tailTrace_607639 : CollatzResearch.WordTrace tailWord_607639 prefixEnd_607639 312010871417453343318025 := by
  unfold tailWord_607639
  simp only [CollatzResearch.WordTrace]
  refine ⟨22162415045635154324241971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14774943363756769549494647 22162415045635154324241971)
  ·
    refine ⟨33243622568452731486362957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22162415045635154324241971 33243622568452731486362957)
    ·
      refine ⟨12466358463169774307386109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33243622568452731486362957 12466358463169774307386109)
      ·
        refine ⟨4674884423688665365269791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12466358463169774307386109 4674884423688665365269791)
        ·
          refine ⟨7012326635532998047904687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4674884423688665365269791 7012326635532998047904687)
          ·
            refine ⟨10518489953299497071857031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7012326635532998047904687 10518489953299497071857031)
            ·
              refine ⟨15777734929949245607785547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10518489953299497071857031 15777734929949245607785547)
              ·
                refine ⟨23666602394923868411678321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15777734929949245607785547 23666602394923868411678321)
                ·
                  refine ⟨17749951796192901308758741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23666602394923868411678321 17749951796192901308758741)
                  ·
                    refine ⟨416014495223271124424033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17749951796192901308758741 416014495223271124424033)
                    ·
                      refine ⟨312010871417453343318025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 416014495223271124424033 312010871417453343318025)
                      ·
                        rfl

theorem cell23_607639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_607639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607639 prefixEnd_607639 := by exact prefixLift 607639
  have htrace : WordTrace (prefixWord ++ tailWord_607639) baseStart_607639 baseEnd_607639 := by
    simpa [prefixWord, tailWord_607639, baseEnd_607639] using wordTrace_append hprefix tailTrace_607639
  have hstable : (prefixWord ++ tailWord_607639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607639).length < 2 ^ (prefixWord ++ tailWord_607639).sum := by decide
  have hdescent : baseEnd_607639 < baseStart_607639 := by decide
  rcases family_descends (prefixWord ++ tailWord_607639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607640 : List Nat := [2, 1, 2, 5, 2, 2, 2, 1, 2, 4]
def baseStart_607640 : Nat := 118140960795 + 607640 * 2 ^ 59
def prefixEnd_607640 : Nat := 4983230072969 + 3 ^ 40 * 607640 * 2
def baseEnd_607640 : Nat := 104003794966035946468507

theorem tailTrace_607640 : CollatzResearch.WordTrace tailWord_607640 prefixEnd_607640 104003794966035946468507 := by
  unfold tailWord_607640
  simp only [CollatzResearch.WordTrace]
  refine ⟨11081225759315765747514187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14774967679087687663352249 11081225759315765747514187)
  ·
    refine ⟨16621838638973648621271281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11081225759315765747514187 16621838638973648621271281)
    ·
      refine ⟨12466378979230236465953461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16621838638973648621271281 12466378979230236465953461)
      ·
        refine ⟨1168723029302834668683137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12466378979230236465953461 1168723029302834668683137)
        ·
          refine ⟨876542271977126001512353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1168723029302834668683137 876542271977126001512353)
          ·
            refine ⟨657406703982844501134265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 876542271977126001512353 657406703982844501134265)
            ·
              refine ⟨493055027987133375850699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 657406703982844501134265 493055027987133375850699)
              ·
                refine ⟨739582541980700063776049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493055027987133375850699 739582541980700063776049)
                ·
                  refine ⟨554686906485525047832037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 739582541980700063776049 554686906485525047832037)
                  ·
                    refine ⟨104003794966035946468507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 554686906485525047832037 104003794966035946468507)
                    ·
                      rfl

theorem cell23_607640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_607640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607640 prefixEnd_607640 := by exact prefixLift 607640
  have htrace : WordTrace (prefixWord ++ tailWord_607640) baseStart_607640 baseEnd_607640 := by
    simpa [prefixWord, tailWord_607640, baseEnd_607640] using wordTrace_append hprefix tailTrace_607640
  have hstable : (prefixWord ++ tailWord_607640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607640).length < 2 ^ (prefixWord ++ tailWord_607640).sum := by decide
  have hdescent : baseEnd_607640 < baseStart_607640 := by decide
  rcases family_descends (prefixWord ++ tailWord_607640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607652 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_607652 : Nat := 118140960795 + 607652 * 2 ^ 59
def prefixEnd_607652 : Nat := 4983230072969 + 3 ^ 40 * 607652 * 2
def baseEnd_607652 : Nat := 312017546665961792455465

theorem tailTrace_607652 : CollatzResearch.WordTrace tailWord_607652 prefixEnd_607652 312017546665961792455465 := by
  unfold tailWord_607652
  simp only [CollatzResearch.WordTrace]
  refine ⟨11081444597294028772232605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14775259463058705029643473 11081444597294028772232605)
  ·
    refine ⟨4155541723985260789587227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11081444597294028772232605 4155541723985260789587227)
    ·
      refine ⟨6233312585977891184380841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4155541723985260789587227 6233312585977891184380841)
      ·
        refine ⟨4674984439483418388285631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6233312585977891184380841 4674984439483418388285631)
        ·
          refine ⟨7012476659225127582428447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4674984439483418388285631 7012476659225127582428447)
          ·
            refine ⟨10518714988837691373642671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7012476659225127582428447 10518714988837691373642671)
            ·
              refine ⟨15778072483256537060464007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10518714988837691373642671 15778072483256537060464007)
              ·
                refine ⟨23667108724884805590696011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15778072483256537060464007 23667108724884805590696011)
                ·
                  refine ⟨35500663087327208386044017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23667108724884805590696011 35500663087327208386044017)
                  ·
                    refine ⟨26625497315495406289533013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35500663087327208386044017 26625497315495406289533013)
                    ·
                      refine ⟨312017546665961792455465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 26625497315495406289533013 312017546665961792455465)
                      ·
                        rfl

theorem cell23_607652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_607652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607652 prefixEnd_607652 := by exact prefixLift 607652
  have htrace : WordTrace (prefixWord ++ tailWord_607652) baseStart_607652 baseEnd_607652 := by
    simpa [prefixWord, tailWord_607652, baseEnd_607652] using wordTrace_append hprefix tailTrace_607652
  have hstable : (prefixWord ++ tailWord_607652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607652).length < 2 ^ (prefixWord ++ tailWord_607652).sum := by decide
  have hdescent : baseEnd_607652 < baseStart_607652 := by decide
  rcases family_descends (prefixWord ++ tailWord_607652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607709 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 9]
def baseStart_607709 : Nat := 118140960795 + 607709 * 2 ^ 59
def prefixEnd_607709 : Nat := 4983230072969 + 3 ^ 40 * 607709 * 2
def baseEnd_607709 : Nat := 34671868340363118826967

theorem tailTrace_607709 : CollatzResearch.WordTrace tailWord_607709 prefixEnd_607709 34671868340363118826967 := by
  unfold tailWord_607709
  simp only [CollatzResearch.WordTrace]
  refine ⟨22164968155381556279290181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14776645436921037519526787 22164968155381556279290181)
  ·
    refine ⟨4155931529134041802366909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22164968155381556279290181 4155931529134041802366909)
    ·
      refine ⟨1558474323425265675887591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4155931529134041802366909 1558474323425265675887591)
      ·
        refine ⟨2337711485137898513831387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1558474323425265675887591 2337711485137898513831387)
        ·
          refine ⟨3506567227706847770747081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337711485137898513831387 3506567227706847770747081)
          ·
            refine ⟨2629925420780135828060311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3506567227706847770747081 2629925420780135828060311)
            ·
              refine ⟨3944888131170203742090467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2629925420780135828060311 3944888131170203742090467)
              ·
                refine ⟨5917332196755305613135701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3944888131170203742090467 5917332196755305613135701)
                ·
                  refine ⟨34671868340363118826967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5917332196755305613135701 34671868340363118826967)
                  ·
                    rfl

theorem cell23_607709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_607709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607709 prefixEnd_607709 := by exact prefixLift 607709
  have htrace : WordTrace (prefixWord ++ tailWord_607709) baseStart_607709 baseEnd_607709 := by
    simpa [prefixWord, tailWord_607709, baseEnd_607709] using wordTrace_append hprefix tailTrace_607709
  have hstable : (prefixWord ++ tailWord_607709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607709).length < 2 ^ (prefixWord ++ tailWord_607709).sum := by decide
  have hdescent : baseEnd_607709 < baseStart_607709 := by decide
  rcases family_descends (prefixWord ++ tailWord_607709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607776 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 4]
def baseStart_607776 : Nat := 118140960795 + 607776 * 2 ^ 59
def prefixEnd_607776 : Nat := 4983230072969 + 3 ^ 40 * 607776 * 2
def baseEnd_607776 : Nat := 312081218267119307304895

theorem tailTrace_607776 : CollatzResearch.WordTrace tailWord_607776 prefixEnd_607776 312081218267119307304895 := by
  unfold tailWord_607776
  simp only [CollatzResearch.WordTrace]
  refine ⟨11083705923069413360989591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14778274564092551147986121 11083705923069413360989591)
  ·
    refine ⟨16625558884604120041484387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11083705923069413360989591 16625558884604120041484387)
    ·
      refine ⟨24938338326906180062226581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16625558884604120041484387 24938338326906180062226581)
      ·
        refine ⟨1168984609073727190416871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24938338326906180062226581 1168984609073727190416871)
        ·
          refine ⟨1753476913610590785625307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1168984609073727190416871 1753476913610590785625307)
          ·
            refine ⟨2630215370415886178437961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1753476913610590785625307 2630215370415886178437961)
            ·
              refine ⟨1972661527811914633828471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2630215370415886178437961 1972661527811914633828471)
              ·
                refine ⟨2958992291717871950742707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1972661527811914633828471 2958992291717871950742707)
                ·
                  refine ⟨4438488437576807926114061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2958992291717871950742707 4438488437576807926114061)
                  ·
                    refine ⟨1664433164091302972292773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4438488437576807926114061 1664433164091302972292773)
                    ·
                      refine ⟨312081218267119307304895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1664433164091302972292773 312081218267119307304895)
                      ·
                        rfl

theorem cell23_607776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_607776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607776 prefixEnd_607776 := by exact prefixLift 607776
  have htrace : WordTrace (prefixWord ++ tailWord_607776) baseStart_607776 baseEnd_607776 := by
    simpa [prefixWord, tailWord_607776, baseEnd_607776] using wordTrace_append hprefix tailTrace_607776
  have hstable : (prefixWord ++ tailWord_607776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607776).length < 2 ^ (prefixWord ++ tailWord_607776).sum := by decide
  have hdescent : baseEnd_607776 < baseStart_607776 := by decide
  rcases family_descends (prefixWord ++ tailWord_607776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607799 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 8]
def baseStart_607799 : Nat := 118140960795 + 607799 * 2 ^ 59
def prefixEnd_607799 : Nat := 4983230072969 + 3 ^ 40 * 607799 * 2
def baseEnd_607799 : Nat := 34677003146908079701921

theorem tailTrace_607799 : CollatzResearch.WordTrace tailWord_607799 prefixEnd_607799 34677003146908079701921 := by
  unfold tailWord_607799
  simp only [CollatzResearch.WordTrace]
  refine ⟨22168250725055501650066451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14778833816703667766710967 22168250725055501650066451)
  ·
    refine ⟨33252376087583252475099677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22168250725055501650066451 33252376087583252475099677)
    ·
      refine ⟨12469641032843719678162379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33252376087583252475099677 12469641032843719678162379)
      ·
        refine ⟨18704461549265579517243569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12469641032843719678162379 18704461549265579517243569)
        ·
          refine ⟨14028346161949184637932677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18704461549265579517243569 14028346161949184637932677)
          ·
            refine ⟨2630314905365472119612377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14028346161949184637932677 2630314905365472119612377)
            ·
              refine ⟨1972736179024104089709283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2630314905365472119612377 1972736179024104089709283)
              ·
                refine ⟨2959104268536156134563925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1972736179024104089709283 2959104268536156134563925)
                ·
                  refine ⟨34677003146908079701921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2959104268536156134563925 34677003146908079701921)
                  ·
                    rfl

theorem cell23_607799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 8].length) (baseStart_607799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607799 prefixEnd_607799 := by exact prefixLift 607799
  have htrace : WordTrace (prefixWord ++ tailWord_607799) baseStart_607799 baseEnd_607799 := by
    simpa [prefixWord, tailWord_607799, baseEnd_607799] using wordTrace_append hprefix tailTrace_607799
  have hstable : (prefixWord ++ tailWord_607799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607799).length < 2 ^ (prefixWord ++ tailWord_607799).sum := by decide
  have hdescent : baseEnd_607799 < baseStart_607799 := by decide
  rcases family_descends (prefixWord ++ tailWord_607799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607854 : List Nat := [4, 1, 2, 2, 3, 2, 2, 2, 1, 4]
def baseStart_607854 : Nat := 118140960795 + 607854 * 2 ^ 59
def prefixEnd_607854 : Nat := 4983230072969 + 3 ^ 40 * 607854 * 2
def baseEnd_607854 : Nat := 104040423252723334043179

theorem tailTrace_607854 : CollatzResearch.WordTrace tailWord_607854 prefixEnd_607854 104040423252723334043179 := by
  unfold tailWord_607854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2771282092482030755414827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14780171159904164028879077 2771282092482030755414827)
  ·
    refine ⟨4156923138723046133122241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2771282092482030755414827 4156923138723046133122241)
    ·
      refine ⟨3117692354042284599841681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4156923138723046133122241 3117692354042284599841681)
      ·
        refine ⟨2338269265531713449881261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3117692354042284599841681 2338269265531713449881261)
        ·
          refine ⟨876850974574392543705473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2338269265531713449881261 876850974574392543705473)
          ·
            refine ⟨657638230930794407779105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 876850974574392543705473 657638230930794407779105)
            ·
              refine ⟨493228673198095805834329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 657638230930794407779105 493228673198095805834329)
              ·
                refine ⟨369921504898571854375747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493228673198095805834329 369921504898571854375747)
                ·
                  refine ⟨554882257347857781563621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 369921504898571854375747 554882257347857781563621)
                  ·
                    refine ⟨104040423252723334043179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 554882257347857781563621 104040423252723334043179)
                    ·
                      rfl

theorem cell23_607854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_607854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607854 prefixEnd_607854 := by exact prefixLift 607854
  have htrace : WordTrace (prefixWord ++ tailWord_607854) baseStart_607854 baseEnd_607854 := by
    simpa [prefixWord, tailWord_607854, baseEnd_607854] using wordTrace_append hprefix tailTrace_607854
  have hstable : (prefixWord ++ tailWord_607854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607854).length < 2 ^ (prefixWord ++ tailWord_607854).sum := by decide
  have hdescent : baseEnd_607854 < baseStart_607854 := by decide
  rcases family_descends (prefixWord ++ tailWord_607854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607900 : List Nat := [2, 2, 3, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_607900 : Nat := 118140960795 + 607900 * 2 ^ 59
def prefixEnd_607900 : Nat := 4983230072969 + 3 ^ 40 * 607900 * 2
def baseEnd_607900 : Nat := 312144889868276822154325

theorem tailTrace_607900 : CollatzResearch.WordTrace tailWord_607900 prefixEnd_607900 312144889868276822154325 := by
  unfold tailWord_607900
  simp only [CollatzResearch.WordTrace]
  refine ⟨11085967248844797949746577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14781289665126397266328769 11085967248844797949746577)
  ·
    refine ⟨8314475436633598462309933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11085967248844797949746577 8314475436633598462309933)
    ·
      refine ⟨3117928288737599423366225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8314475436633598462309933 3117928288737599423366225)
      ·
        refine ⟨2338446216553199567524669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3117928288737599423366225 2338446216553199567524669)
        ·
          refine ⟨876917331207449837821751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2338446216553199567524669 876917331207449837821751)
          ·
            refine ⟨1315375996811174756732627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876917331207449837821751 1315375996811174756732627)
            ·
              refine ⟨1973063995216762135098941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315375996811174756732627 1973063995216762135098941)
              ·
                refine ⟨739898998206285800662103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1973063995216762135098941 739898998206285800662103)
                ·
                  refine ⟨1109848497309428700993155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739898998206285800662103 1109848497309428700993155)
                  ·
                    refine ⟨1664772745964143051489733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1109848497309428700993155 1664772745964143051489733)
                    ·
                      refine ⟨312144889868276822154325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1664772745964143051489733 312144889868276822154325)
                      ·
                        rfl

theorem cell23_607900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_607900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607900 prefixEnd_607900 := by exact prefixLift 607900
  have htrace : WordTrace (prefixWord ++ tailWord_607900) baseStart_607900 baseEnd_607900 := by
    simpa [prefixWord, tailWord_607900, baseEnd_607900] using wordTrace_append hprefix tailTrace_607900
  have hstable : (prefixWord ++ tailWord_607900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607900).length < 2 ^ (prefixWord ++ tailWord_607900).sum := by decide
  have hdescent : baseEnd_607900 < baseStart_607900 := by decide
  rcases family_descends (prefixWord ++ tailWord_607900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607917 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_607917 : Nat := 118140960795 + 607917 * 2 ^ 59
def prefixEnd_607917 : Nat := 4983230072969 + 3 ^ 40 * 607917 * 2
def baseEnd_607917 : Nat := 312153619039403255641747

theorem tailTrace_607917 : CollatzResearch.WordTrace tailWord_607917 prefixEnd_607917 312153619039403255641747 := by
  unfold tailWord_607917
  simp only [CollatzResearch.WordTrace]
  refine ⟨22172554538628007802862005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14781703025752005201908003 22172554538628007802862005)
  ·
    refine ⟨2078676987996375731518313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22172554538628007802862005 2078676987996375731518313)
    ·
      refine ⟨1559007740997281798638735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2078676987996375731518313 1559007740997281798638735)
      ·
        refine ⟨2338511611495922697958103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559007740997281798638735 2338511611495922697958103)
        ·
          refine ⟨3507767417243884046937155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2338511611495922697958103 3507767417243884046937155)
          ·
            refine ⟨5261651125865826070405733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3507767417243884046937155 5261651125865826070405733)
            ·
              refine ⟨986559586099842388201075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5261651125865826070405733 986559586099842388201075)
              ·
                refine ⟨1479839379149763582301613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986559586099842388201075 1479839379149763582301613)
                ·
                  refine ⟨554939767181161343363105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1479839379149763582301613 554939767181161343363105)
                  ·
                    refine ⟨416204825385871007522329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 554939767181161343363105 416204825385871007522329)
                    ·
                      refine ⟨312153619039403255641747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 416204825385871007522329 312153619039403255641747)
                      ·
                        rfl

theorem cell23_607917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_607917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607917 prefixEnd_607917 := by exact prefixLift 607917
  have htrace : WordTrace (prefixWord ++ tailWord_607917) baseStart_607917 baseEnd_607917 := by
    simpa [prefixWord, tailWord_607917, baseEnd_607917] using wordTrace_append hprefix tailTrace_607917
  have hstable : (prefixWord ++ tailWord_607917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607917).length < 2 ^ (prefixWord ++ tailWord_607917).sum := by decide
  have hdescent : baseEnd_607917 < baseStart_607917 := by decide
  rcases family_descends (prefixWord ++ tailWord_607917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607960 : List Nat := [2, 1, 2, 2, 3, 1, 1, 5, 1, 3, 2]
def baseStart_607960 : Nat := 118140960795 + 607960 * 2 ^ 59
def prefixEnd_607960 : Nat := 4983230072969 + 3 ^ 40 * 607960 * 2
def baseEnd_607960 : Nat := 312175698707546587404049

theorem tailTrace_607960 : CollatzResearch.WordTrace tailWord_607960 prefixEnd_607960 312175698707546587404049 := by
  unfold tailWord_607960
  simp only [CollatzResearch.WordTrace]
  refine ⟨11087061438736113073338667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14782748584981484097784889 11087061438736113073338667)
  ·
    refine ⟨16630592158104169610008001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11087061438736113073338667 16630592158104169610008001)
    ·
      refine ⟨12472944118578127207506001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16630592158104169610008001 12472944118578127207506001)
      ·
        refine ⟨9354708088933595405629501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12472944118578127207506001 9354708088933595405629501)
        ·
          refine ⟨3508015533350098277111063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9354708088933595405629501 3508015533350098277111063)
          ·
            refine ⟨5262023300025147415666595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3508015533350098277111063 5262023300025147415666595)
            ·
              refine ⟨7893034950037721123499893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5262023300025147415666595 7893034950037721123499893)
              ·
                refine ⟨739972026566036355328115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7893034950037721123499893 739972026566036355328115)
                ·
                  refine ⟨1109958039849054532992173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739972026566036355328115 1109958039849054532992173)
                  ·
                    refine ⟨416234264943395449872065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1109958039849054532992173 416234264943395449872065)
                    ·
                      refine ⟨312175698707546587404049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 416234264943395449872065 312175698707546587404049)
                      ·
                        rfl

theorem cell23_607960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_607960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607960 prefixEnd_607960 := by exact prefixLift 607960
  have htrace : WordTrace (prefixWord ++ tailWord_607960) baseStart_607960 baseEnd_607960 := by
    simpa [prefixWord, tailWord_607960, baseEnd_607960] using wordTrace_append hprefix tailTrace_607960
  have hstable : (prefixWord ++ tailWord_607960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607960).length < 2 ^ (prefixWord ++ tailWord_607960).sum := by decide
  have hdescent : baseEnd_607960 < baseStart_607960 := by decide
  rcases family_descends (prefixWord ++ tailWord_607960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607996 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 9]
def baseStart_607996 : Nat := 118140960795 + 607996 * 2 ^ 59
def prefixEnd_607996 : Nat := 4983230072969 + 3 ^ 40 * 607996 * 2
def baseEnd_607996 : Nat := 34688242667900938505987

theorem tailTrace_607996 : CollatzResearch.WordTrace tailWord_607996 prefixEnd_607996 34688242667900938505987 := by
  unfold tailWord_607996
  simp only [CollatzResearch.WordTrace]
  refine ⟨11087717952670902147493921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14783623936894536196658561 11087717952670902147493921)
  ·
    refine ⟨8315788464503176610620441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11087717952670902147493921 8315788464503176610620441)
    ·
      refine ⟨6236841348377382457965331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8315788464503176610620441 6236841348377382457965331)
      ·
        refine ⟨9355262022566073686947997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6236841348377382457965331 9355262022566073686947997)
        ·
          refine ⟨3508223258462277632605499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9355262022566073686947997 3508223258462277632605499)
          ·
            refine ⟨5262334887693416448908249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3508223258462277632605499 5262334887693416448908249)
            ·
              refine ⟨3946751165770062336681187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5262334887693416448908249 3946751165770062336681187)
              ·
                refine ⟨5920126748655093505021781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3946751165770062336681187 5920126748655093505021781)
                ·
                  refine ⟨34688242667900938505987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5920126748655093505021781 34688242667900938505987)
                  ·
                    rfl

theorem cell23_607996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 9].length) (baseStart_607996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_607996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_607996 prefixEnd_607996 := by exact prefixLift 607996
  have htrace : WordTrace (prefixWord ++ tailWord_607996) baseStart_607996 baseEnd_607996 := by
    simpa [prefixWord, tailWord_607996, baseEnd_607996] using wordTrace_append hprefix tailTrace_607996
  have hstable : (prefixWord ++ tailWord_607996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607996).length < 2 ^ (prefixWord ++ tailWord_607996).sum := by decide
  have hdescent : baseEnd_607996 < baseStart_607996 := by decide
  rcases family_descends (prefixWord ++ tailWord_607996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608007 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 1, 4, 2]
def baseStart_608007 : Nat := 118140960795 + 608007 * 2 ^ 59
def prefixEnd_608007 : Nat := 4983230072969 + 3 ^ 40 * 608007 * 2
def baseEnd_608007 : Nat := 312199832298307903516333

theorem tailTrace_608007 : CollatzResearch.WordTrace tailWord_608007 prefixEnd_608007 312199832298307903516333 := by
  unfold tailWord_608007
  simp only [CollatzResearch.WordTrace]
  refine ⟨22175837108301953173638275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14783891405534635449092183 22175837108301953173638275)
  ·
    refine ⟨33263755662452929760457413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22175837108301953173638275 33263755662452929760457413)
    ·
      refine ⟨6236954186709924330085765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33263755662452929760457413 6236954186709924330085765)
      ·
        refine ⟨1169428910008110811891081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6236954186709924330085765 1169428910008110811891081)
        ·
          refine ⟨877071682506083108918311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1169428910008110811891081 877071682506083108918311)
          ·
            refine ⟨1315607523759124663377467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877071682506083108918311 1315607523759124663377467)
            ·
              refine ⟨1973411285638686995066201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315607523759124663377467 1973411285638686995066201)
              ·
                refine ⟨1480058464229015246299651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1973411285638686995066201 1480058464229015246299651)
                ·
                  refine ⟨2220087696343522869449477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480058464229015246299651 2220087696343522869449477)
                  ·
                    refine ⟨416266443064410538021777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2220087696343522869449477 416266443064410538021777)
                    ·
                      refine ⟨312199832298307903516333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 416266443064410538021777 312199832298307903516333)
                      ·
                        rfl

theorem cell23_608007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_608007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608007 prefixEnd_608007 := by exact prefixLift 608007
  have htrace : WordTrace (prefixWord ++ tailWord_608007) baseStart_608007 baseEnd_608007 := by
    simpa [prefixWord, tailWord_608007, baseEnd_608007] using wordTrace_append hprefix tailTrace_608007
  have hstable : (prefixWord ++ tailWord_608007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608007).length < 2 ^ (prefixWord ++ tailWord_608007).sum := by decide
  have hdescent : baseEnd_608007 < baseStart_608007 := by decide
  rcases family_descends (prefixWord ++ tailWord_608007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608040 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_608040 : Nat := 118140960795 + 608040 * 2 ^ 59
def prefixEnd_608040 : Nat := 4983230072969 + 3 ^ 40 * 608040 * 2
def baseEnd_608040 : Nat := 312216777159906274403681

theorem tailTrace_608040 : CollatzResearch.WordTrace tailWord_608040 prefixEnd_608040 312216777159906274403681 := by
  unfold tailWord_608040
  simp only [CollatzResearch.WordTrace]
  refine ⟨11088520358591199904794787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14784693811454933206393049 11088520358591199904794787)
  ·
    refine ⟨16632780537886799857192181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11088520358591199904794787 16632780537886799857192181)
    ·
      refine ⟨1559323175426887486611767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16632780537886799857192181 1559323175426887486611767)
      ·
        refine ⟨2338984763140331229917651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559323175426887486611767 2338984763140331229917651)
        ·
          refine ⟨3508477144710496844876477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2338984763140331229917651 3508477144710496844876477)
          ·
            refine ⟨1315678929266436316828679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3508477144710496844876477 1315678929266436316828679)
            ·
              refine ⟨1973518393899654475243019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315678929266436316828679 1973518393899654475243019)
              ·
                refine ⟨2960277590849481712864529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1973518393899654475243019 2960277590849481712864529)
                ·
                  refine ⟨2220208193137111284648397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2960277590849481712864529 2220208193137111284648397)
                  ·
                    refine ⟨832578072426416731743149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2220208193137111284648397 832578072426416731743149)
                    ·
                      refine ⟨312216777159906274403681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 832578072426416731743149 312216777159906274403681)
                      ·
                        rfl

theorem cell23_608040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_608040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608040 prefixEnd_608040 := by exact prefixLift 608040
  have htrace : WordTrace (prefixWord ++ tailWord_608040) baseStart_608040 baseEnd_608040 := by
    simpa [prefixWord, tailWord_608040, baseEnd_608040] using wordTrace_append hprefix tailTrace_608040
  have hstable : (prefixWord ++ tailWord_608040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608040).length < 2 ^ (prefixWord ++ tailWord_608040).sum := by decide
  have hdescent : baseEnd_608040 < baseStart_608040 := by decide
  rcases family_descends (prefixWord ++ tailWord_608040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608073 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 5, 4]
def baseStart_608073 : Nat := 118140960795 + 608073 * 2 ^ 59
def prefixEnd_608073 : Nat := 4983230072969 + 3 ^ 40 * 608073 * 2
def baseEnd_608073 : Nat := 104077907340501548430343

theorem tailTrace_608073 : CollatzResearch.WordTrace tailWord_608073 prefixEnd_608073 104077907340501548430343 := by
  unfold tailWord_608073
  simp only [CollatzResearch.WordTrace]
  refine ⟨22178244326062846445540873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14785496217375230963693915 22178244326062846445540873)
  ·
    refine ⟨16633683244547134834155655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22178244326062846445540873 16633683244547134834155655)
    ·
      refine ⟨24950524866820702251233483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16633683244547134834155655 24950524866820702251233483)
      ·
        refine ⟨37425787300231053376850225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24950524866820702251233483 37425787300231053376850225)
        ·
          refine ⟨28069340475173290032637669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37425787300231053376850225 28069340475173290032637669)
          ·
            refine ⟨5263001339094991881119563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28069340475173290032637669 5263001339094991881119563)
            ·
              refine ⟨7894502008642487821679345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5263001339094991881119563 7894502008642487821679345)
              ·
                refine ⟨5920876506481865866259509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7894502008642487821679345 5920876506481865866259509)
                ·
                  refine ⟨555082172482674924961829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5920876506481865866259509 555082172482674924961829)
                  ·
                    refine ⟨104077907340501548430343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 555082172482674924961829 104077907340501548430343)
                    ·
                      rfl

theorem cell23_608073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 4].length) (baseStart_608073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608073 prefixEnd_608073 := by exact prefixLift 608073
  have htrace : WordTrace (prefixWord ++ tailWord_608073) baseStart_608073 baseEnd_608073 := by
    simpa [prefixWord, tailWord_608073, baseEnd_608073] using wordTrace_append hprefix tailTrace_608073
  have hstable : (prefixWord ++ tailWord_608073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608073).length < 2 ^ (prefixWord ++ tailWord_608073).sum := by decide
  have hdescent : baseEnd_608073 < baseStart_608073 := by decide
  rcases family_descends (prefixWord ++ tailWord_608073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608090 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 3, 4]
def baseStart_608090 : Nat := 118140960795 + 608090 * 2 ^ 59
def prefixEnd_608090 : Nat := 4983230072969 + 3 ^ 40 * 608090 * 2
def baseEnd_608090 : Nat := 104080817064210359592817

theorem tailTrace_608090 : CollatzResearch.WordTrace tailWord_608090 prefixEnd_608090 104080817064210359592817 := by
  unfold tailWord_608090
  simp only [CollatzResearch.WordTrace]
  refine ⟨5544716091750314587227431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14785909578000838899273149 5544716091750314587227431)
  ·
    refine ⟨8317074137625471880841147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5544716091750314587227431 8317074137625471880841147)
    ·
      refine ⟨12475611206438207821261721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8317074137625471880841147 12475611206438207821261721)
      ·
        refine ⟨9356708404828655865946291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12475611206438207821261721 9356708404828655865946291)
        ·
          refine ⟨14035062607242983798919437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9356708404828655865946291 14035062607242983798919437)
          ·
            refine ⟨5263148477716118924594789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14035062607242983798919437 5263148477716118924594789)
            ·
              refine ⟨986840339571772298361523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5263148477716118924594789 986840339571772298361523)
              ·
                refine ⟨1480260509357658447542285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986840339571772298361523 1480260509357658447542285)
                ·
                  refine ⟨555097691009121917828357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1480260509357658447542285 555097691009121917828357)
                  ·
                    refine ⟨104080817064210359592817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 555097691009121917828357 104080817064210359592817)
                    ·
                      rfl

theorem cell23_608090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_608090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608090 prefixEnd_608090 := by exact prefixLift 608090
  have htrace : WordTrace (prefixWord ++ tailWord_608090) baseStart_608090 baseEnd_608090 := by
    simpa [prefixWord, tailWord_608090, baseEnd_608090] using wordTrace_append hprefix tailTrace_608090
  have hstable : (prefixWord ++ tailWord_608090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608090).length < 2 ^ (prefixWord ++ tailWord_608090).sum := by decide
  have hdescent : baseEnd_608090 < baseStart_608090 := by decide
  rcases family_descends (prefixWord ++ tailWord_608090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608113 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 2, 5, 3]
def baseStart_608113 : Nat := 118140960795 + 608113 * 2 ^ 59
def prefixEnd_608113 : Nat := 4983230072969 + 3 ^ 40 * 608113 * 2
def baseEnd_608113 : Nat := 312254261247684488790845

theorem tailTrace_608113 : CollatzResearch.WordTrace tailWord_608113 prefixEnd_608113 312254261247684488790845 := by
  unfold tailWord_608113
  simp only [CollatzResearch.WordTrace]
  refine ⟨22179703245917933276996993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14786468830611955517997995 22179703245917933276996993)
  ·
    refine ⟨16634777434438449957747745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22179703245917933276996993 16634777434438449957747745)
    ·
      refine ⟨12476083075828837468310809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16634777434438449957747745 12476083075828837468310809)
      ·
        refine ⟨9357062306871628101233107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12476083075828837468310809 9357062306871628101233107)
        ·
          refine ⟨14035593460307442151849661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9357062306871628101233107 14035593460307442151849661)
          ·
            refine ⟨5263347547615290806943623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14035593460307442151849661 5263347547615290806943623)
            ·
              refine ⟨7895021321422936210415435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5263347547615290806943623 7895021321422936210415435)
              ·
                refine ⟨11842531982134404315623153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7895021321422936210415435 11842531982134404315623153)
                ·
                  refine ⟨8881898986600803236717365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11842531982134404315623153 8881898986600803236717365)
                  ·
                    refine ⟨832678029993825303442253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8881898986600803236717365 832678029993825303442253)
                    ·
                      refine ⟨312254261247684488790845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 832678029993825303442253 312254261247684488790845)
                      ·
                        rfl

theorem cell23_608113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_608113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608113 prefixEnd_608113 := by exact prefixLift 608113
  have htrace : WordTrace (prefixWord ++ tailWord_608113) baseStart_608113 baseEnd_608113 := by
    simpa [prefixWord, tailWord_608113, baseEnd_608113] using wordTrace_append hprefix tailTrace_608113
  have hstable : (prefixWord ++ tailWord_608113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608113).length < 2 ^ (prefixWord ++ tailWord_608113).sum := by decide
  have hdescent : baseEnd_608113 < baseStart_608113 := by decide
  rcases family_descends (prefixWord ++ tailWord_608113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608163 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 1, 6]
def baseStart_608163 : Nat := 118140960795 + 608163 * 2 ^ 59
def prefixEnd_608163 : Nat := 4983230072969 + 3 ^ 40 * 608163 * 2
def baseEnd_608163 : Nat := 104093311760136431055205

theorem tailTrace_608163 : CollatzResearch.WordTrace tailWord_608163 prefixEnd_608163 104093311760136431055205 := by
  unfold tailWord_608163
  simp only [CollatzResearch.WordTrace]
  refine ⟨22181526895736791816317143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14787684597157861210878095 22181526895736791816317143)
  ·
    refine ⟨33272290343605187724475715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22181526895736791816317143 33272290343605187724475715)
    ·
      refine ⟨49908435515407781586713573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33272290343605187724475715 49908435515407781586713573)
      ·
        refine ⟨9357831659138959047508795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49908435515407781586713573 9357831659138959047508795)
        ·
          refine ⟨14036747488708438571263193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9357831659138959047508795 14036747488708438571263193)
          ·
            refine ⟨10527560616531328928447395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14036747488708438571263193 10527560616531328928447395)
            ·
              refine ⟨15791340924796993392671093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10527560616531328928447395 15791340924796993392671093)
              ·
                refine ⟨1480438211699718130562915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15791340924796993392671093 1480438211699718130562915)
                ·
                  refine ⟨2220657317549577195844373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480438211699718130562915 2220657317549577195844373)
                  ·
                    refine ⟨104093311760136431055205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2220657317549577195844373 104093311760136431055205)
                    ·
                      rfl

theorem cell23_608163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 6].length) (baseStart_608163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608163 prefixEnd_608163 := by exact prefixLift 608163
  have htrace : WordTrace (prefixWord ++ tailWord_608163) baseStart_608163 baseEnd_608163 := by
    simpa [prefixWord, tailWord_608163, baseEnd_608163] using wordTrace_append hprefix tailTrace_608163
  have hstable : (prefixWord ++ tailWord_608163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608163).length < 2 ^ (prefixWord ++ tailWord_608163).sum := by decide
  have hdescent : baseEnd_608163 < baseStart_608163 := by decide
  rcases family_descends (prefixWord ++ tailWord_608163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608167 : List Nat := [1, 1, 6, 1, 2, 1, 3, 2, 1, 5]
def baseStart_608167 : Nat := 118140960795 + 608167 * 2 ^ 59
def prefixEnd_608167 : Nat := 4983230072969 + 3 ^ 40 * 608167 * 2
def baseEnd_608167 : Nat := 104093996401009092505199

theorem tailTrace_608167 : CollatzResearch.WordTrace tailWord_608167 prefixEnd_608167 104093996401009092505199 := by
  unfold tailWord_608167
  simp only [CollatzResearch.WordTrace]
  refine ⟨22181672787722300499462755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14787781858481533666308503 22181672787722300499462755)
  ·
    refine ⟨33272509181583450749194133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22181672787722300499462755 33272509181583450749194133)
    ·
      refine ⟨1559648867886724253868475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33272509181583450749194133 1559648867886724253868475)
      ·
        refine ⟨2339473301830086380802713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559648867886724253868475 2339473301830086380802713)
        ·
          refine ⟨1754604976372564785602035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2339473301830086380802713 1754604976372564785602035)
          ·
            refine ⟨2631907464558847178403053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1754604976372564785602035 2631907464558847178403053)
            ·
              refine ⟨986965299209567691901145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2631907464558847178403053 986965299209567691901145)
              ·
                refine ⟨740223974407175768925859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 986965299209567691901145 740223974407175768925859)
                ·
                  refine ⟨1110335961610763653388789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740223974407175768925859 1110335961610763653388789)
                  ·
                    refine ⟨104093996401009092505199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1110335961610763653388789 104093996401009092505199)
                    ·
                      rfl

theorem cell23_608167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_608167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608167 prefixEnd_608167 := by exact prefixLift 608167
  have htrace : WordTrace (prefixWord ++ tailWord_608167) baseStart_608167 baseEnd_608167 := by
    simpa [prefixWord, tailWord_608167, baseEnd_608167] using wordTrace_append hprefix tailTrace_608167
  have hstable : (prefixWord ++ tailWord_608167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608167).length < 2 ^ (prefixWord ++ tailWord_608167).sum := by decide
  have hdescent : baseEnd_608167 < baseStart_608167 := by decide
  rcases family_descends (prefixWord ++ tailWord_608167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608214 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_608214 : Nat := 118140960795 + 608214 * 2 ^ 59
def prefixEnd_608214 : Nat := 4983230072969 + 3 ^ 40 * 608214 * 2
def baseEnd_608214 : Nat := 104102040931262864542627

theorem tailTrace_608214 : CollatzResearch.WordTrace tailWord_608214 prefixEnd_608214 104102040931262864542627 := by
  unfold tailWord_608214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1386461688659501720401481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14788924679034685017615797 1386461688659501720401481)
  ·
    refine ⟨1039846266494626290301111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1386461688659501720401481 1039846266494626290301111)
    ·
      refine ⟨1559769399741939435451667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1039846266494626290301111 1559769399741939435451667)
      ·
        refine ⟨2339654099612909153177501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559769399741939435451667 2339654099612909153177501)
        ·
          refine ⟨877370287354840932441563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2339654099612909153177501 877370287354840932441563)
          ·
            refine ⟨1316055431032261398662345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877370287354840932441563 1316055431032261398662345)
            ·
              refine ⟨987041573274196048996759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1316055431032261398662345 987041573274196048996759)
              ·
                refine ⟨1480562359911294073495139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987041573274196048996759 1480562359911294073495139)
                ·
                  refine ⟨2220843539866941110242709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480562359911294073495139 2220843539866941110242709)
                  ·
                    refine ⟨104102040931262864542627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2220843539866941110242709 104102040931262864542627)
                    ·
                      rfl

theorem cell23_608214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_608214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608214 prefixEnd_608214 := by exact prefixLift 608214
  have htrace : WordTrace (prefixWord ++ tailWord_608214) baseStart_608214 baseEnd_608214 := by
    simpa [prefixWord, tailWord_608214, baseEnd_608214] using wordTrace_append hprefix tailTrace_608214
  have hstable : (prefixWord ++ tailWord_608214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608214).length < 2 ^ (prefixWord ++ tailWord_608214).sum := by decide
  have hdescent : baseEnd_608214 < baseStart_608214 := by decide
  rcases family_descends (prefixWord ++ tailWord_608214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608217 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 1, 2, 4]
def baseStart_608217 : Nat := 118140960795 + 608217 * 2 ^ 59
def prefixEnd_608217 : Nat := 4983230072969 + 3 ^ 40 * 608217 * 2
def baseEnd_608217 : Nat := 312307663235752081890367

theorem tailTrace_608217 : CollatzResearch.WordTrace tailWord_608217 prefixEnd_608217 312307663235752081890367 := by
  unfold tailWord_608217
  simp only [CollatzResearch.WordTrace]
  refine ⟨22183496437541159038782905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14788997625027439359188603 22183496437541159038782905)
  ·
    refine ⟨16637622328155869279087179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22183496437541159038782905 16637622328155869279087179)
    ·
      refine ⟨24956433492233803918630769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16637622328155869279087179 24956433492233803918630769)
      ·
        refine ⟨18717325119175352938973077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24956433492233803918630769 18717325119175352938973077)
        ·
          refine ⟨877374614961344669014363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18717325119175352938973077 877374614961344669014363)
          ·
            refine ⟨1316061922442017003521545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877374614961344669014363 1316061922442017003521545)
            ·
              refine ⟨987046441831512752641159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1316061922442017003521545 987046441831512752641159)
              ·
                refine ⟨1480569662747269128961739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987046441831512752641159 1480569662747269128961739)
                ·
                  refine ⟨2220854494120903693442609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480569662747269128961739 2220854494120903693442609)
                  ·
                    refine ⟨1665640870590677770081957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2220854494120903693442609 1665640870590677770081957)
                    ·
                      refine ⟨312307663235752081890367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1665640870590677770081957 312307663235752081890367)
                      ·
                        rfl

theorem cell23_608217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_608217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608217 prefixEnd_608217 := by exact prefixLift 608217
  have htrace : WordTrace (prefixWord ++ tailWord_608217) baseStart_608217 baseEnd_608217 := by
    simpa [prefixWord, tailWord_608217, baseEnd_608217] using wordTrace_append hprefix tailTrace_608217
  have hstable : (prefixWord ++ tailWord_608217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608217).length < 2 ^ (prefixWord ++ tailWord_608217).sum := by decide
  have hdescent : baseEnd_608217 < baseStart_608217 := by decide
  rcases family_descends (prefixWord ++ tailWord_608217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608221 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_608221 : Nat := 118140960795 + 608221 * 2 ^ 59
def prefixEnd_608221 : Nat := 4983230072969 + 3 ^ 40 * 608221 * 2
def baseEnd_608221 : Nat := 312309717158370066240349

theorem tailTrace_608221 : CollatzResearch.WordTrace tailWord_608221 prefixEnd_608221 312309717158370066240349 := by
  unfold tailWord_608221
  simp only [CollatzResearch.WordTrace]
  refine ⟨22183642329526667721928517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14789094886351111814619011 22183642329526667721928517)
  ·
    refine ⟨4159432936786250197861597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22183642329526667721928517 4159432936786250197861597)
    ·
      refine ⟨1559787351294843824198099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4159432936786250197861597 1559787351294843824198099)
      ·
        refine ⟨2339681026942265736297149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559787351294843824198099 2339681026942265736297149)
        ·
          refine ⟨877380385103349651111431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2339681026942265736297149 877380385103349651111431)
          ·
            refine ⟨1316070577655024476667147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877380385103349651111431 1316070577655024476667147)
            ·
              refine ⟨1974105866482536715000721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1316070577655024476667147 1974105866482536715000721)
              ·
                refine ⟨1480579399861902536250541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1974105866482536715000721 1480579399861902536250541)
                ·
                  refine ⟨555217274948213451093953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1480579399861902536250541 555217274948213451093953)
                  ·
                    refine ⟨416412956211160088320465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 555217274948213451093953 416412956211160088320465)
                    ·
                      refine ⟨312309717158370066240349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 416412956211160088320465 312309717158370066240349)
                      ·
                        rfl

theorem cell23_608221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_608221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608221 prefixEnd_608221 := by exact prefixLift 608221
  have htrace : WordTrace (prefixWord ++ tailWord_608221) baseStart_608221 baseEnd_608221 := by
    simpa [prefixWord, tailWord_608221, baseEnd_608221] using wordTrace_append hprefix tailTrace_608221
  have hstable : (prefixWord ++ tailWord_608221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608221).length < 2 ^ (prefixWord ++ tailWord_608221).sum := by decide
  have hdescent : baseEnd_608221 < baseStart_608221 := by decide
  rcases family_descends (prefixWord ++ tailWord_608221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608238 : List Nat := [4, 1, 2, 1, 3, 2, 2, 3, 1, 2, 2]
def baseStart_608238 : Nat := 118140960795 + 608238 * 2 ^ 59
def prefixEnd_608238 : Nat := 4983230072969 + 3 ^ 40 * 608238 * 2
def baseEnd_608238 : Nat := 312318446329496499727771

theorem tailTrace_608238 : CollatzResearch.WordTrace tailWord_608238 prefixEnd_608238 312318446329496499727771 := by
  unfold tailWord_608238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2773032796308134953162171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14789508246976719750198245 2773032796308134953162171)
  ·
    refine ⟨4159549194462202429743257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2773032796308134953162171 4159549194462202429743257)
    ·
      refine ⟨3119661895846651822307443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4159549194462202429743257 3119661895846651822307443)
      ·
        refine ⟨4679492843769977733461165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3119661895846651822307443 4679492843769977733461165)
        ·
          refine ⟨1754809816413741650047937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4679492843769977733461165 1754809816413741650047937)
          ·
            refine ⟨1316107362310306237535953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1754809816413741650047937 1316107362310306237535953)
            ·
              refine ⟨987080521732729678151965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1316107362310306237535953 987080521732729678151965)
              ·
                refine ⟨370155195649773629306987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 987080521732729678151965 370155195649773629306987)
                ·
                  refine ⟨555232793474660443960481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370155195649773629306987 555232793474660443960481)
                  ·
                    refine ⟨416424595105995332970361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 555232793474660443960481 416424595105995332970361)
                    ·
                      refine ⟨312318446329496499727771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 416424595105995332970361 312318446329496499727771)
                      ·
                        rfl

theorem cell23_608238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_608238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608238 prefixEnd_608238 := by exact prefixLift 608238
  have htrace : WordTrace (prefixWord ++ tailWord_608238) baseStart_608238 baseEnd_608238 := by
    simpa [prefixWord, tailWord_608238, baseEnd_608238] using wordTrace_append hprefix tailTrace_608238
  have hstable : (prefixWord ++ tailWord_608238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608238).length < 2 ^ (prefixWord ++ tailWord_608238).sum := by decide
  have hdescent : baseEnd_608238 < baseStart_608238 := by decide
  rcases family_descends (prefixWord ++ tailWord_608238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608241 : List Nat := [1, 2, 2, 2, 5, 2, 2, 1, 1, 2, 3]
def baseStart_608241 : Nat := 118140960795 + 608241 * 2 ^ 59
def prefixEnd_608241 : Nat := 4983230072969 + 3 ^ 40 * 608241 * 2
def baseEnd_608241 : Nat := 312319986771459987990257

theorem tailTrace_608241 : CollatzResearch.WordTrace tailWord_608241 prefixEnd_608241 312319986771459987990257 := by
  unfold tailWord_608241
  simp only [CollatzResearch.WordTrace]
  refine ⟨22184371789454211137656577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14789581192969474091771051 22184371789454211137656577)
  ·
    refine ⟨16638278842090658353242433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22184371789454211137656577 16638278842090658353242433)
    ·
      refine ⟨12478709131567993764931825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16638278842090658353242433 12478709131567993764931825)
      ·
        refine ⟨9359031848675995323698869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12478709131567993764931825 9359031848675995323698869)
        ·
          refine ⟨877409235813374561596769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9359031848675995323698869 877409235813374561596769)
          ·
            refine ⟨658056926860030921197577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 877409235813374561596769 658056926860030921197577)
            ·
              refine ⟨493542695145023190898183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658056926860030921197577 493542695145023190898183)
              ·
                refine ⟨740314042717534786347275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493542695145023190898183 740314042717534786347275)
                ·
                  refine ⟨1110471064076302179520913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740314042717534786347275 1110471064076302179520913)
                  ·
                    refine ⟨832853298057226634640685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1110471064076302179520913 832853298057226634640685)
                    ·
                      refine ⟨312319986771459987990257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 832853298057226634640685 312319986771459987990257)
                      ·
                        rfl

theorem cell23_608241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_608241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608241 prefixEnd_608241 := by exact prefixLift 608241
  have htrace : WordTrace (prefixWord ++ tailWord_608241) baseStart_608241 baseEnd_608241 := by
    simpa [prefixWord, tailWord_608241, baseEnd_608241] using wordTrace_append hprefix tailTrace_608241
  have hstable : (prefixWord ++ tailWord_608241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608241).length < 2 ^ (prefixWord ++ tailWord_608241).sum := by decide
  have hdescent : baseEnd_608241 < baseStart_608241 := by decide
  rcases family_descends (prefixWord ++ tailWord_608241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608270 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 2, 6]
def baseStart_608270 : Nat := 118140960795 + 608270 * 2 ^ 59
def prefixEnd_608270 : Nat := 4983230072969 + 3 ^ 40 * 608270 * 2
def baseEnd_608270 : Nat := 104111625903480124842541

theorem tailTrace_608270 : CollatzResearch.WordTrace tailWord_608270 prefixEnd_608270 104111625903480124842541 := by
  unfold tailWord_608270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2773178688293643636307783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14790286337566099393641509 2773178688293643636307783)
  ·
    refine ⟨4159768032440465454461675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2773178688293643636307783 4159768032440465454461675)
    ·
      refine ⟨6239652048660698181692513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4159768032440465454461675 6239652048660698181692513)
      ·
        refine ⟨4679739036495523636269385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6239652048660698181692513 4679739036495523636269385)
        ·
          refine ⟨3509804277371642727202039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4679739036495523636269385 3509804277371642727202039)
          ·
            refine ⟨5264706416057464090803059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3509804277371642727202039 5264706416057464090803059)
            ·
              refine ⟨7897059624086196136204589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5264706416057464090803059 7897059624086196136204589)
              ·
                refine ⟨2961397359032323551076721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7897059624086196136204589 2961397359032323551076721)
                ·
                  refine ⟨2221048019274242663307541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2961397359032323551076721 2221048019274242663307541)
                  ·
                    refine ⟨104111625903480124842541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2221048019274242663307541 104111625903480124842541)
                    ·
                      rfl

theorem cell23_608270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_608270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608270 prefixEnd_608270 := by exact prefixLift 608270
  have htrace : WordTrace (prefixWord ++ tailWord_608270) baseStart_608270 baseEnd_608270 := by
    simpa [prefixWord, tailWord_608270, baseEnd_608270] using wordTrace_append hprefix tailTrace_608270
  have hstable : (prefixWord ++ tailWord_608270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608270).length < 2 ^ (prefixWord ++ tailWord_608270).sum := by decide
  have hdescent : baseEnd_608270 < baseStart_608270 := by decide
  rcases family_descends (prefixWord ++ tailWord_608270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608280 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 2, 1, 5]
def baseStart_608280 : Nat := 118140960795 + 608280 * 2 ^ 59
def prefixEnd_608280 : Nat := 4983230072969 + 3 ^ 40 * 608280 * 2
def baseEnd_608280 : Nat := 312340012516985335402577

theorem tailTrace_608280 : CollatzResearch.WordTrace tailWord_608280 prefixEnd_608280 312340012516985335402577 := by
  unfold tailWord_608280
  simp only [CollatzResearch.WordTrace]
  refine ⟨11092897118156460399163147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14790529490875280532217529 11092897118156460399163147)
  ·
    refine ⟨16639345677234690598744721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11092897118156460399163147 16639345677234690598744721)
    ·
      refine ⟨12479509257926017949058541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16639345677234690598744721 12479509257926017949058541)
      ·
        refine ⟨4679815971722256730896953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12479509257926017949058541 4679815971722256730896953)
        ·
          refine ⟨3509861978791692548172715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4679815971722256730896953 3509861978791692548172715)
          ·
            refine ⟨5264792968187538822259073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3509861978791692548172715 5264792968187538822259073)
            ·
              refine ⟨3948594726140654116694305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5264792968187538822259073 3948594726140654116694305)
              ·
                refine ⟨2961446044605490587520729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3948594726140654116694305 2961446044605490587520729)
                ·
                  refine ⟨2221084533454117940640547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2961446044605490587520729 2221084533454117940640547)
                  ·
                    refine ⟨3331626800181176910960821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2221084533454117940640547 3331626800181176910960821)
                    ·
                      refine ⟨312340012516985335402577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3331626800181176910960821 312340012516985335402577)
                      ·
                        rfl

theorem cell23_608280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_608280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608280 prefixEnd_608280 := by exact prefixLift 608280
  have htrace : WordTrace (prefixWord ++ tailWord_608280) baseStart_608280 baseEnd_608280 := by
    simpa [prefixWord, tailWord_608280, baseEnd_608280] using wordTrace_append hprefix tailTrace_608280
  have hstable : (prefixWord ++ tailWord_608280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608280).length < 2 ^ (prefixWord ++ tailWord_608280).sum := by decide
  have hdescent : baseEnd_608280 < baseStart_608280 := by decide
  rcases family_descends (prefixWord ++ tailWord_608280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608283 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 9]
def baseStart_608283 : Nat := 118140960795 + 608283 * 2 ^ 59
def prefixEnd_608283 : Nat := 4983230072969 + 3 ^ 40 * 608283 * 2
def baseEnd_608283 : Nat := 34704616995438758185007

theorem tailTrace_608283 : CollatzResearch.WordTrace tailWord_608283 prefixEnd_608283 34704616995438758185007 := by
  unfold tailWord_608283
  simp only [CollatzResearch.WordTrace]
  refine ⟨22185903655302052310685503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14790602436868034873790335 22185903655302052310685503)
  ·
    refine ⟨33278855482953078466028255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22185903655302052310685503 33278855482953078466028255)
    ·
      refine ⟨49918283224429617699042383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33278855482953078466028255 49918283224429617699042383)
      ·
        refine ⟨74877424836644426548563575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49918283224429617699042383 74877424836644426548563575)
        ·
          refine ⟨112316137254966639822845363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74877424836644426548563575 112316137254966639822845363)
          ·
            refine ⟨168474205882449959734268045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112316137254966639822845363 168474205882449959734268045)
            ·
              refine ⟨63177827205918734900350517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168474205882449959734268045 63177827205918734900350517)
              ·
                refine ⟨5922921300554881396907861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63177827205918734900350517 5922921300554881396907861)
                ·
                  refine ⟨34704616995438758185007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5922921300554881396907861 34704616995438758185007)
                  ·
                    rfl

theorem cell23_608283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 9].length) (baseStart_608283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608283 prefixEnd_608283 := by exact prefixLift 608283
  have htrace : WordTrace (prefixWord ++ tailWord_608283) baseStart_608283 baseEnd_608283 := by
    simpa [prefixWord, tailWord_608283, baseEnd_608283] using wordTrace_append hprefix tailTrace_608283
  have hstable : (prefixWord ++ tailWord_608283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608283).length < 2 ^ (prefixWord ++ tailWord_608283).sum := by decide
  have hdescent : baseEnd_608283 < baseStart_608283 := by decide
  rcases family_descends (prefixWord ++ tailWord_608283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608330 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 6, 5]
def baseStart_608330 : Nat := 118140960795 + 608330 * 2 ^ 59
def prefixEnd_608330 : Nat := 4983230072969 + 3 ^ 40 * 608330 * 2
def baseEnd_608330 : Nat := 104121895516570046592449

theorem tailTrace_608330 : CollatzResearch.WordTrace tailWord_608330 prefixEnd_608330 104121895516570046592449 := by
  unfold tailWord_608330
  simp only [CollatzResearch.WordTrace]
  refine ⟨5546904471532944834411611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14791745257421186225097629 5546904471532944834411611)
  ·
    refine ⟨8320356707299417251617417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5546904471532944834411611 8320356707299417251617417)
    ·
      refine ⟨6240267530474562938713063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8320356707299417251617417 6240267530474562938713063)
      ·
        refine ⟨9360401295711844408069595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6240267530474562938713063 9360401295711844408069595)
        ·
          refine ⟨14040601943567766612104393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9360401295711844408069595 14040601943567766612104393)
          ·
            refine ⟨10530451457675824959078295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14040601943567766612104393 10530451457675824959078295)
            ·
              refine ⟨15795677186513737438617443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10530451457675824959078295 15795677186513737438617443)
              ·
                refine ⟨23693515779770606157926165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15795677186513737438617443 23693515779770606157926165)
                ·
                  refine ⟨1110633552176747163652789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23693515779770606157926165 1110633552176747163652789)
                  ·
                    refine ⟨104121895516570046592449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1110633552176747163652789 104121895516570046592449)
                    ·
                      rfl

theorem cell23_608330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_608330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608330 prefixEnd_608330 := by exact prefixLift 608330
  have htrace : WordTrace (prefixWord ++ tailWord_608330) baseStart_608330 baseEnd_608330 := by
    simpa [prefixWord, tailWord_608330, baseEnd_608330] using wordTrace_append hprefix tailTrace_608330
  have hstable : (prefixWord ++ tailWord_608330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608330).length < 2 ^ (prefixWord ++ tailWord_608330).sum := by decide
  have hdescent : baseEnd_608330 < baseStart_608330 := by decide
  rcases family_descends (prefixWord ++ tailWord_608330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608340 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_608340 : Nat := 118140960795 + 608340 * 2 ^ 59
def prefixEnd_608340 : Nat := 4983230072969 + 3 ^ 40 * 608340 * 2
def baseEnd_608340 : Nat := 312370821356255100652301

theorem tailTrace_608340 : CollatzResearch.WordTrace tailWord_608340 prefixEnd_608340 312370821356255100652301 := by
  unfold tailWord_608340
  simp only [CollatzResearch.WordTrace]
  refine ⟨11093991308047775522755237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14791988410730367363673649 11093991308047775522755237)
  ·
    refine ⟨2080123370258957910516607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11093991308047775522755237 2080123370258957910516607)
    ·
      refine ⟨3120185055388436865774911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2080123370258957910516607 3120185055388436865774911)
      ·
        refine ⟨4680277583082655298662367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3120185055388436865774911 4680277583082655298662367)
        ·
          refine ⟨7020416374623982947993551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4680277583082655298662367 7020416374623982947993551)
          ·
            refine ⟨10530624561935974421990327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7020416374623982947993551 10530624561935974421990327)
            ·
              refine ⟨15795936842903961632985491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10530624561935974421990327 15795936842903961632985491)
              ·
                refine ⟨23693905264355942449478237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15795936842903961632985491 23693905264355942449478237)
                ·
                  refine ⟨8885214474133478418554339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23693905264355942449478237 8885214474133478418554339)
                  ·
                    refine ⟨13327821711200217627831509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8885214474133478418554339 13327821711200217627831509)
                    ·
                      refine ⟨312370821356255100652301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13327821711200217627831509 312370821356255100652301)
                      ·
                        rfl

theorem cell23_608340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_608340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608340 prefixEnd_608340 := by exact prefixLift 608340
  have htrace : WordTrace (prefixWord ++ tailWord_608340) baseStart_608340 baseEnd_608340 := by
    simpa [prefixWord, tailWord_608340, baseEnd_608340] using wordTrace_append hprefix tailTrace_608340
  have hstable : (prefixWord ++ tailWord_608340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608340).length < 2 ^ (prefixWord ++ tailWord_608340).sum := by decide
  have hdescent : baseEnd_608340 < baseStart_608340 := by decide
  rcases family_descends (prefixWord ++ tailWord_608340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608367 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 4]
def baseStart_608367 : Nat := 118140960795 + 608367 * 2 ^ 59
def prefixEnd_608367 : Nat := 4983230072969 + 3 ^ 40 * 608367 * 2
def baseEnd_608367 : Nat := 312384685333926495014677

theorem tailTrace_608367 : CollatzResearch.WordTrace tailWord_608367 prefixEnd_608367 312384685333926495014677 := by
  unfold tailWord_608367
  simp only [CollatzResearch.WordTrace]
  refine ⟨22188967386997734656743355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14792644924665156437828903 22188967386997734656743355)
  ·
    refine ⟨33283451080496601985115033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22188967386997734656743355 33283451080496601985115033)
    ·
      refine ⟨24962588310372451488836275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33283451080496601985115033 24962588310372451488836275)
      ·
        refine ⟨37443882465558677233254413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24962588310372451488836275 37443882465558677233254413)
        ·
          refine ⟨14041455924584503962470405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37443882465558677233254413 14041455924584503962470405)
          ·
            refine ⟨2632772985859594492963201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14041455924584503962470405 2632772985859594492963201)
            ·
              refine ⟨1974579739394695869722401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2632772985859594492963201 1974579739394695869722401)
              ·
                refine ⟨1480934804546021902291801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1974579739394695869722401 1480934804546021902291801)
                ·
                  refine ⟨1110701103409516426718851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1480934804546021902291801 1110701103409516426718851)
                  ·
                    refine ⟨1666051655114274640078277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1110701103409516426718851 1666051655114274640078277)
                    ·
                      refine ⟨312384685333926495014677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1666051655114274640078277 312384685333926495014677)
                      ·
                        rfl

theorem cell23_608367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 4].length) (baseStart_608367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608367 prefixEnd_608367 := by exact prefixLift 608367
  have htrace : WordTrace (prefixWord ++ tailWord_608367) baseStart_608367 baseEnd_608367 := by
    simpa [prefixWord, tailWord_608367, baseEnd_608367] using wordTrace_append hprefix tailTrace_608367
  have hstable : (prefixWord ++ tailWord_608367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608367).length < 2 ^ (prefixWord ++ tailWord_608367).sum := by decide
  have hdescent : baseEnd_608367 < baseStart_608367 := by decide
  rcases family_descends (prefixWord ++ tailWord_608367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608394 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 3, 4]
def baseStart_608394 : Nat := 118140960795 + 608394 * 2 ^ 59
def prefixEnd_608394 : Nat := 4983230072969 + 3 ^ 40 * 608394 * 2
def baseEnd_608394 : Nat := 104132849770532629792351

theorem tailTrace_608394 : CollatzResearch.WordTrace tailWord_608394 prefixEnd_608394 104132849770532629792351 := by
  unfold tailWord_608394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5547488039474979566994059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14793301438599945511984157 5547488039474979566994059)
  ·
    refine ⟨8321232059212469350491089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5547488039474979566994059 8321232059212469350491089)
    ·
      refine ⟨6240924044409352012868317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8321232059212469350491089 6240924044409352012868317)
      ·
        refine ⟨2340346516653507004825619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6240924044409352012868317 2340346516653507004825619)
        ·
          refine ⟨3510519774980260507238429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2340346516653507004825619 3510519774980260507238429)
          ·
            refine ⟨1316444915617597690214411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3510519774980260507238429 1316444915617597690214411)
            ·
              refine ⟨1974667373426396535321617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1316444915617597690214411 1974667373426396535321617)
              ·
                refine ⟨1481000530069797401491213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1974667373426396535321617 1481000530069797401491213)
                ·
                  refine ⟨555375198776174025559205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1481000530069797401491213 555375198776174025559205)
                  ·
                    refine ⟨104132849770532629792351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 555375198776174025559205 104132849770532629792351)
                    ·
                      rfl

theorem cell23_608394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_608394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608394 prefixEnd_608394 := by exact prefixLift 608394
  have htrace : WordTrace (prefixWord ++ tailWord_608394) baseStart_608394 baseEnd_608394 := by
    simpa [prefixWord, tailWord_608394, baseEnd_608394] using wordTrace_append hprefix tailTrace_608394
  have hstable : (prefixWord ++ tailWord_608394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608394).length < 2 ^ (prefixWord ++ tailWord_608394).sum := by decide
  have hdescent : baseEnd_608394 < baseStart_608394 := by decide
  rcases family_descends (prefixWord ++ tailWord_608394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608474 : List Nat := [3, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4]
def baseStart_608474 : Nat := 118140960795 + 608474 * 2 ^ 59
def prefixEnd_608474 : Nat := 4983230072969 + 3 ^ 40 * 608474 * 2
def baseEnd_608474 : Nat := 312439627763957576376685

theorem tailTrace_608474 : CollatzResearch.WordTrace tailWord_608474 prefixEnd_608474 312439627763957576376685 := by
  unfold tailWord_608474
  simp only [CollatzResearch.WordTrace]
  refine ⟨5548217499402522982722119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14795246665073394620592317 5548217499402522982722119)
  ·
    refine ⟨8322326249103784474083179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5548217499402522982722119 8322326249103784474083179)
    ·
      refine ⟨12483489373655676711124769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8322326249103784474083179 12483489373655676711124769)
      ·
        refine ⟨9362617030241757533343577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12483489373655676711124769 9362617030241757533343577)
        ·
          refine ⟨7021962772681318150007683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9362617030241757533343577 7021962772681318150007683)
          ·
            refine ⟨10532944159021977225011525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7021962772681318150007683 10532944159021977225011525)
            ·
              refine ⟨1974927029816620729689661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10532944159021977225011525 1974927029816620729689661)
              ·
                refine ⟨740597636181232773633623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1974927029816620729689661 740597636181232773633623)
                ·
                  refine ⟨1110896454271849160450435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740597636181232773633623 1110896454271849160450435)
                  ·
                    refine ⟨1666344681407773740675653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1110896454271849160450435 1666344681407773740675653)
                    ·
                      refine ⟨312439627763957576376685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1666344681407773740675653 312439627763957576376685)
                      ·
                        rfl

theorem cell23_608474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_608474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608474 prefixEnd_608474 := by exact prefixLift 608474
  have htrace : WordTrace (prefixWord ++ tailWord_608474) baseStart_608474 baseEnd_608474 := by
    simpa [prefixWord, tailWord_608474, baseEnd_608474] using wordTrace_append hprefix tailTrace_608474
  have hstable : (prefixWord ++ tailWord_608474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608474).length < 2 ^ (prefixWord ++ tailWord_608474).sum := by decide
  have hdescent : baseEnd_608474 < baseStart_608474 := by decide
  rcases family_descends (prefixWord ++ tailWord_608474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608484 : List Nat := [2, 3, 1, 1, 1, 2, 1, 6, 2, 4]
def baseStart_608484 : Nat := 118140960795 + 608484 * 2 ^ 59
def prefixEnd_608484 : Nat := 4983230072969 + 3 ^ 40 * 608484 * 2
def baseEnd_608484 : Nat := 104148254190167512417213

theorem tailTrace_608484 : CollatzResearch.WordTrace tailWord_608484 prefixEnd_608484 104148254190167512417213 := by
  unfold tailWord_608484
  simp only [CollatzResearch.WordTrace]
  refine ⟨11096617363786931819376253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14795489818382575759168337 11096617363786931819376253)
  ·
    refine ⟨4161231511420099432266095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11096617363786931819376253 4161231511420099432266095)
    ·
      refine ⟨6241847267130149148399143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4161231511420099432266095 6241847267130149148399143)
      ·
        refine ⟨9362770900695223722598715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6241847267130149148399143 9362770900695223722598715)
        ·
          refine ⟨14044156351042835583898073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9362770900695223722598715 14044156351042835583898073)
          ·
            refine ⟨10533117263282126687923555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14044156351042835583898073 10533117263282126687923555)
            ·
              refine ⟨15799675894923190031885333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10533117263282126687923555 15799675894923190031885333)
              ·
                refine ⟨740609807574524532744625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15799675894923190031885333 740609807574524532744625)
                ·
                  refine ⟨555457355680893399558469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 740609807574524532744625 555457355680893399558469)
                  ·
                    refine ⟨104148254190167512417213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 555457355680893399558469 104148254190167512417213)
                    ·
                      rfl

theorem cell23_608484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_608484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608484 prefixEnd_608484 := by exact prefixLift 608484
  have htrace : WordTrace (prefixWord ++ tailWord_608484) baseStart_608484 baseEnd_608484 := by
    simpa [prefixWord, tailWord_608484, baseEnd_608484] using wordTrace_append hprefix tailTrace_608484
  have hstable : (prefixWord ++ tailWord_608484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608484).length < 2 ^ (prefixWord ++ tailWord_608484).sum := by decide
  have hdescent : baseEnd_608484 < baseStart_608484 := by decide
  rcases family_descends (prefixWord ++ tailWord_608484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608485 : List Nat := [1, 3, 1, 4, 2, 2, 3, 2, 1, 1, 3]
def baseStart_608485 : Nat := 118140960795 + 608485 * 2 ^ 59
def prefixEnd_608485 : Nat := 4983230072969 + 3 ^ 40 * 608485 * 2
def baseEnd_608485 : Nat := 312445276051157033339135

theorem tailTrace_608485 : CollatzResearch.WordTrace tailWord_608485 prefixEnd_608485 312445276051157033339135 := by
  unfold tailWord_608485
  simp only [CollatzResearch.WordTrace]
  refine ⟨22193271200570240809538909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14795514133713493873025939 22193271200570240809538909)
  ·
    refine ⟨8322476700213840303577091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22193271200570240809538909 8322476700213840303577091)
    ·
      refine ⟨12483715050320760455365637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8322476700213840303577091 12483715050320760455365637)
      ·
        refine ⟨2340696571935142585381057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12483715050320760455365637 2340696571935142585381057)
        ·
          refine ⟨1755522428951356939035793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2340696571935142585381057 1755522428951356939035793)
          ·
            refine ⟨1316641821713517704276845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1755522428951356939035793 1316641821713517704276845)
            ·
              refine ⟨493740683142569139103817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1316641821713517704276845 493740683142569139103817)
              ·
                refine ⟨370305512356926854327863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493740683142569139103817 370305512356926854327863)
                ·
                  refine ⟨555458268535390281491795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370305512356926854327863 555458268535390281491795)
                  ·
                    refine ⟨833187402803085422237693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 555458268535390281491795 833187402803085422237693)
                    ·
                      refine ⟨312445276051157033339135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 833187402803085422237693 312445276051157033339135)
                      ·
                        rfl

theorem cell23_608485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_608485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608485 prefixEnd_608485 := by exact prefixLift 608485
  have htrace : WordTrace (prefixWord ++ tailWord_608485) baseStart_608485 baseEnd_608485 := by
    simpa [prefixWord, tailWord_608485, baseEnd_608485] using wordTrace_append hprefix tailTrace_608485
  have hstable : (prefixWord ++ tailWord_608485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608485).length < 2 ^ (prefixWord ++ tailWord_608485).sum := by decide
  have hdescent : baseEnd_608485 < baseStart_608485 := by decide
  rcases family_descends (prefixWord ++ tailWord_608485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608494 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_608494 : Nat := 118140960795 + 608494 * 2 ^ 59
def prefixEnd_608494 : Nat := 4983230072969 + 3 ^ 40 * 608494 * 2
def baseEnd_608494 : Nat := 312449897377047498126593

theorem tailTrace_608494 : CollatzResearch.WordTrace tailWord_608494 prefixEnd_608494 312449897377047498126593 := by
  unfold tailWord_608494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2774199932192204418327067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14795732971691756897744357 2774199932192204418327067)
  ·
    refine ⟨4161299898288306627490601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2774199932192204418327067 4161299898288306627490601)
    ·
      refine ⟨3120974923716229970617951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4161299898288306627490601 3120974923716229970617951)
      ·
        refine ⟨4681462385574344955926927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3120974923716229970617951 4681462385574344955926927)
        ·
          refine ⟨7022193578361517433890391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4681462385574344955926927 7022193578361517433890391)
          ·
            refine ⟨10533290367542276150835587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7022193578361517433890391 10533290367542276150835587)
            ·
              refine ⟨15799935551313414226253381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10533290367542276150835587 15799935551313414226253381)
              ·
                refine ⟨2962487915871265167422509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15799935551313414226253381 2962487915871265167422509)
                ·
                  refine ⟨1110932968451724437783441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2962487915871265167422509 1110932968451724437783441)
                  ·
                    refine ⟨833199726338793328337581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1110932968451724437783441 833199726338793328337581)
                    ·
                      refine ⟨312449897377047498126593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 833199726338793328337581 312449897377047498126593)
                      ·
                        rfl

theorem cell23_608494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_608494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608494 prefixEnd_608494 := by exact prefixLift 608494
  have htrace : WordTrace (prefixWord ++ tailWord_608494) baseStart_608494 baseEnd_608494 := by
    simpa [prefixWord, tailWord_608494, baseEnd_608494] using wordTrace_append hprefix tailTrace_608494
  have hstable : (prefixWord ++ tailWord_608494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608494).length < 2 ^ (prefixWord ++ tailWord_608494).sum := by decide
  have hdescent : baseEnd_608494 < baseStart_608494 := by decide
  rcases family_descends (prefixWord ++ tailWord_608494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608507 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 3]
def baseStart_608507 : Nat := 118140960795 + 608507 * 2 ^ 59
def prefixEnd_608507 : Nat := 4983230072969 + 3 ^ 40 * 608507 * 2
def baseEnd_608507 : Nat := 312456572625555947264033

theorem tailTrace_608507 : CollatzResearch.WordTrace tailWord_608507 prefixEnd_608507 312456572625555947264033 := by
  unfold tailWord_608507
  simp only [CollatzResearch.WordTrace]
  refine ⟨22194073606490538566839775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14796049070993692377893183 22194073606490538566839775)
  ·
    refine ⟨33291110409735807850259663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22194073606490538566839775 33291110409735807850259663)
    ·
      refine ⟨49936665614603711775389495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33291110409735807850259663 49936665614603711775389495)
      ·
        refine ⟨74904998421905567663084243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49936665614603711775389495 74904998421905567663084243)
        ·
          refine ⟨112357497632858351494626365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74904998421905567663084243 112357497632858351494626365)
          ·
            refine ⟨42134061612321881810484887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112357497632858351494626365 42134061612321881810484887)
            ·
              refine ⟨63201092418482822715727331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42134061612321881810484887 63201092418482822715727331)
              ·
                refine ⟨94801638627724234073590997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63201092418482822715727331 94801638627724234073590997)
                ·
                  refine ⟨2221913405337286736099789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 94801638627724234073590997 2221913405337286736099789)
                  ·
                    refine ⟨833217527001482526037421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2221913405337286736099789 833217527001482526037421)
                    ·
                      refine ⟨312456572625555947264033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 833217527001482526037421 312456572625555947264033)
                      ·
                        rfl

theorem cell23_608507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 3].length) (baseStart_608507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608507 prefixEnd_608507 := by exact prefixLift 608507
  have htrace : WordTrace (prefixWord ++ tailWord_608507) baseStart_608507 baseEnd_608507 := by
    simpa [prefixWord, tailWord_608507, baseEnd_608507] using wordTrace_append hprefix tailTrace_608507
  have hstable : (prefixWord ++ tailWord_608507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608507).length < 2 ^ (prefixWord ++ tailWord_608507).sum := by decide
  have hdescent : baseEnd_608507 < baseStart_608507 := by decide
  rcases family_descends (prefixWord ++ tailWord_608507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608514 : List Nat := [3, 4, 1, 1, 2, 1, 2, 9]
def baseStart_608514 : Nat := 118140960795 + 608514 * 2 ^ 59
def prefixEnd_608514 : Nat := 4983230072969 + 3 ^ 40 * 608514 * 2
def baseEnd_608514 : Nat := 11572598777412497032463

theorem tailTrace_608514 : CollatzResearch.WordTrace tailWord_608514 prefixEnd_608514 11572598777412497032463 := by
  unfold tailWord_608514
  simp only [CollatzResearch.WordTrace]
  refine ⟨5548582229366294690586149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14796219278310119174896397 5548582229366294690586149)
  ·
    refine ⟨1040359168006180254484903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5548582229366294690586149 1040359168006180254484903)
    ·
      refine ⟨1560538752009270381727355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1040359168006180254484903 1560538752009270381727355)
      ·
        refine ⟨2340808128013905572591033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1560538752009270381727355 2340808128013905572591033)
        ·
          refine ⟨1755606096010429179443275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2340808128013905572591033 1755606096010429179443275)
          ·
            refine ⟨2633409144015643769164913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755606096010429179443275 2633409144015643769164913)
            ·
              refine ⟨1975056858011732826873685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2633409144015643769164913 1975056858011732826873685)
              ·
                refine ⟨11572598777412497032463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1975056858011732826873685 11572598777412497032463)
                ·
                  rfl

theorem cell23_608514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 9].length) (baseStart_608514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608514 prefixEnd_608514 := by exact prefixLift 608514
  have htrace : WordTrace (prefixWord ++ tailWord_608514) baseStart_608514 baseEnd_608514 := by
    simpa [prefixWord, tailWord_608514, baseEnd_608514] using wordTrace_append hprefix tailTrace_608514
  have hstable : (prefixWord ++ tailWord_608514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608514).length < 2 ^ (prefixWord ++ tailWord_608514).sum := by decide
  have hdescent : baseEnd_608514 < baseStart_608514 := by decide
  rcases family_descends (prefixWord ++ tailWord_608514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608524 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 1, 3, 3]
def baseStart_608524 : Nat := 118140960795 + 608524 * 2 ^ 59
def prefixEnd_608524 : Nat := 4983230072969 + 3 ^ 40 * 608524 * 2
def baseEnd_608524 : Nat := 312465301796682380751455

theorem tailTrace_608524 : CollatzResearch.WordTrace tailWord_608524 prefixEnd_608524 312465301796682380751455 := by
  unfold tailWord_608524
  simp only [CollatzResearch.WordTrace]
  refine ⟨11097346823714475235104313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14796462431619300313472417 11097346823714475235104313)
  ·
    refine ⟨8323010117785856426328235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11097346823714475235104313 8323010117785856426328235)
    ·
      refine ⟨12484515176678784639492353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8323010117785856426328235 12484515176678784639492353)
      ·
        refine ⟨9363386382509088479619265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12484515176678784639492353 9363386382509088479619265)
        ·
          refine ⟨7022539786881816359714449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9363386382509088479619265 7022539786881816359714449)
          ·
            refine ⟨5266904840161362269785837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7022539786881816359714449 5266904840161362269785837)
            ·
              refine ⟨1975089315060510851169689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5266904840161362269785837 1975089315060510851169689)
              ·
                refine ⟨1481316986295383138377267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1975089315060510851169689 1481316986295383138377267)
                ·
                  refine ⟨2221975479443074707565901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481316986295383138377267 2221975479443074707565901)
                  ·
                    refine ⟨833240804791153015337213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2221975479443074707565901 833240804791153015337213)
                    ·
                      refine ⟨312465301796682380751455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 833240804791153015337213 312465301796682380751455)
                      ·
                        rfl

theorem cell23_608524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_608524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608524 prefixEnd_608524 := by exact prefixLift 608524
  have htrace : WordTrace (prefixWord ++ tailWord_608524) baseStart_608524 baseEnd_608524 := by
    simpa [prefixWord, tailWord_608524, baseEnd_608524] using wordTrace_append hprefix tailTrace_608524
  have hstable : (prefixWord ++ tailWord_608524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608524).length < 2 ^ (prefixWord ++ tailWord_608524).sum := by decide
  have hdescent : baseEnd_608524 < baseStart_608524 := by decide
  rcases family_descends (prefixWord ++ tailWord_608524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608547 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 4]
def baseStart_608547 : Nat := 118140960795 + 608547 * 2 ^ 59
def prefixEnd_608547 : Nat := 4983230072969 + 3 ^ 40 * 608547 * 2
def baseEnd_608547 : Nat := 312477111851735790763849

theorem tailTrace_608547 : CollatzResearch.WordTrace tailWord_608547 prefixEnd_608547 312477111851735790763849 := by
  unfold tailWord_608547
  simp only [CollatzResearch.WordTrace]
  refine ⟨22195532526345625398295895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14797021684230416932197263 22195532526345625398295895)
  ·
    refine ⟨33293298789518438097443843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22195532526345625398295895 33293298789518438097443843)
    ·
      refine ⟨49939948184277657146165765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33293298789518438097443843 49939948184277657146165765)
      ·
        refine ⟨9363740284552060714906081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49939948184277657146165765 9363740284552060714906081)
        ·
          refine ⟨7022805213414045536179561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9363740284552060714906081 7022805213414045536179561)
          ·
            refine ⟨5267103910060534152134671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7022805213414045536179561 5267103910060534152134671)
            ·
              refine ⟨7900655865090801228202007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5267103910060534152134671 7900655865090801228202007)
              ·
                refine ⟨11850983797636201842303011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7900655865090801228202007 11850983797636201842303011)
                ·
                  refine ⟨17776475696454302763454517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11850983797636201842303011 17776475696454302763454517)
                  ·
                    refine ⟨1666544596542590884073861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17776475696454302763454517 1666544596542590884073861)
                    ·
                      refine ⟨312477111851735790763849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1666544596542590884073861 312477111851735790763849)
                      ·
                        rfl

theorem cell23_608547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_608547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608547 prefixEnd_608547 := by exact prefixLift 608547
  have htrace : WordTrace (prefixWord ++ tailWord_608547) baseStart_608547 baseEnd_608547 := by
    simpa [prefixWord, tailWord_608547, baseEnd_608547] using wordTrace_append hprefix tailTrace_608547
  have hstable : (prefixWord ++ tailWord_608547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608547).length < 2 ^ (prefixWord ++ tailWord_608547).sum := by decide
  have hdescent : baseEnd_608547 < baseStart_608547 := by decide
  rcases family_descends (prefixWord ++ tailWord_608547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608567 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 5]
def baseStart_608567 : Nat := 118140960795 + 608567 * 2 ^ 59
def prefixEnd_608567 : Nat := 4983230072969 + 3 ^ 40 * 608567 * 2
def baseEnd_608567 : Nat := 312487381464825712513757

theorem tailTrace_608567 : CollatzResearch.WordTrace tailWord_608567 prefixEnd_608567 312487381464825712513757 := by
  unfold tailWord_608567
  simp only [CollatzResearch.WordTrace]
  refine ⟨22196261986273168814023955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14797507990848779209349303 22196261986273168814023955)
  ·
    refine ⟨33294392979409753221035933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22196261986273168814023955 33294392979409753221035933)
    ·
      refine ⟨12485397367278657457888475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33294392979409753221035933 12485397367278657457888475)
      ·
        refine ⟨18728096050917986186832713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12485397367278657457888475 18728096050917986186832713)
        ·
          refine ⟨14046072038188489640124535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18728096050917986186832713 14046072038188489640124535)
          ·
            refine ⟨21069108057282734460186803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14046072038188489640124535 21069108057282734460186803)
            ·
              refine ⟨31603662085924101690280205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21069108057282734460186803 31603662085924101690280205)
              ·
                refine ⟨11851373282221538133855077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31603662085924101690280205 11851373282221538133855077)
                ·
                  refine ⟨2222132490416538400097827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11851373282221538133855077 2222132490416538400097827)
                  ·
                    refine ⟨3333198735624807600146741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2222132490416538400097827 3333198735624807600146741)
                    ·
                      refine ⟨312487381464825712513757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3333198735624807600146741 312487381464825712513757)
                      ·
                        rfl

theorem cell23_608567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_608567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608567 prefixEnd_608567 := by exact prefixLift 608567
  have htrace : WordTrace (prefixWord ++ tailWord_608567) baseStart_608567 baseEnd_608567 := by
    simpa [prefixWord, tailWord_608567, baseEnd_608567] using wordTrace_append hprefix tailTrace_608567
  have hstable : (prefixWord ++ tailWord_608567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608567).length < 2 ^ (prefixWord ++ tailWord_608567).sum := by decide
  have hdescent : baseEnd_608567 < baseStart_608567 := by decide
  rcases family_descends (prefixWord ++ tailWord_608567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608594 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_608594 : Nat := 118140960795 + 608594 * 2 ^ 59
def prefixEnd_608594 : Nat := 4983230072969 + 3 ^ 40 * 608594 * 2
def baseEnd_608594 : Nat := 312501245442497106876133

theorem tailTrace_608594 : CollatzResearch.WordTrace tailWord_608594 prefixEnd_608594 312501245442497106876133 := by
  unfold tailWord_608594
  simp only [CollatzResearch.WordTrace]
  refine ⟨5549311689293838106314209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14798164504783568283504557 5549311689293838106314209)
  ·
    refine ⟨4161983766970378579735657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5549311689293838106314209 4161983766970378579735657)
    ·
      refine ⟨3121487825227783934801743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4161983766970378579735657 3121487825227783934801743)
      ·
        refine ⟨4682231737841675902202615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3121487825227783934801743 4682231737841675902202615)
        ·
          refine ⟨7023347606762513853303923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4682231737841675902202615 7023347606762513853303923)
          ·
            refine ⟨10535021410143770779955885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7023347606762513853303923 10535021410143770779955885)
            ·
              refine ⟨3950633028803914042483457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10535021410143770779955885 3950633028803914042483457)
              ·
                refine ⟨2962974771602935531862593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3950633028803914042483457 2962974771602935531862593)
                ·
                  refine ⟨2222231078702201648896945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2962974771602935531862593 2222231078702201648896945)
                  ·
                    refine ⟨1666673309026651236672709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2222231078702201648896945 1666673309026651236672709)
                    ·
                      refine ⟨312501245442497106876133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1666673309026651236672709 312501245442497106876133)
                      ·
                        rfl

theorem cell23_608594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_608594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608594 prefixEnd_608594 := by exact prefixLift 608594
  have htrace : WordTrace (prefixWord ++ tailWord_608594) baseStart_608594 baseEnd_608594 := by
    simpa [prefixWord, tailWord_608594, baseEnd_608594] using wordTrace_append hprefix tailTrace_608594
  have hstable : (prefixWord ++ tailWord_608594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608594).length < 2 ^ (prefixWord ++ tailWord_608594).sum := by decide
  have hdescent : baseEnd_608594 < baseStart_608594 := by decide
  rcases family_descends (prefixWord ++ tailWord_608594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608617 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 3, 7]
def baseStart_608617 : Nat := 118140960795 + 608617 * 2 ^ 59
def prefixEnd_608617 : Nat := 4983230072969 + 3 ^ 40 * 608617 * 2
def baseEnd_608617 : Nat := 104171018499183505629509

theorem tailTrace_608617 : CollatzResearch.WordTrace tailWord_608617 prefixEnd_608617 104171018499183505629509 := by
  unfold tailWord_608617
  simp only [CollatzResearch.WordTrace]
  refine ⟨22198085636092027353344105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14798723757394684902229403 22198085636092027353344105)
  ·
    refine ⟨16648564227069020515008079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22198085636092027353344105 16648564227069020515008079)
    ·
      refine ⟨24972846340603530772512119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16648564227069020515008079 24972846340603530772512119)
      ·
        refine ⟨37459269510905296158768179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24972846340603530772512119 37459269510905296158768179)
        ·
          refine ⟨56188904266357944238152269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37459269510905296158768179 56188904266357944238152269)
          ·
            refine ⟨21070839099884229089307101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56188904266357944238152269 21070839099884229089307101)
            ·
              refine ⟨7901564662456585908490163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21070839099884229089307101 7901564662456585908490163)
              ·
                refine ⟨11852346993684878862735245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7901564662456585908490163 11852346993684878862735245)
                ·
                  refine ⟨4444630122631829573525717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11852346993684878862735245 4444630122631829573525717)
                  ·
                    refine ⟨104171018499183505629509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4444630122631829573525717 104171018499183505629509)
                    ·
                      rfl

theorem cell23_608617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 7].length) (baseStart_608617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608617 prefixEnd_608617 := by exact prefixLift 608617
  have htrace : WordTrace (prefixWord ++ tailWord_608617) baseStart_608617 baseEnd_608617 := by
    simpa [prefixWord, tailWord_608617, baseEnd_608617] using wordTrace_append hprefix tailTrace_608617
  have hstable : (prefixWord ++ tailWord_608617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608617).length < 2 ^ (prefixWord ++ tailWord_608617).sum := by decide
  have hdescent : baseEnd_608617 < baseStart_608617 := by decide
  rcases family_descends (prefixWord ++ tailWord_608617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608627 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 7]
def baseStart_608627 : Nat := 118140960795 + 608627 * 2 ^ 59
def prefixEnd_608627 : Nat := 4983230072969 + 3 ^ 40 * 608627 * 2
def baseEnd_608627 : Nat := 312518190304095477763481

theorem tailTrace_608627 : CollatzResearch.WordTrace tailWord_608627 prefixEnd_608627 312518190304095477763481 := by
  unfold tailWord_608627
  simp only [CollatzResearch.WordTrace]
  refine ⟨22198450366055799061208135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14798966910703866040805423 22198450366055799061208135)
  ·
    refine ⟨33297675549083698591812203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22198450366055799061208135 33297675549083698591812203)
    ·
      refine ⟨49946513323625547887718305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33297675549083698591812203 49946513323625547887718305)
      ·
        refine ⟨37459884992719160915788729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49946513323625547887718305 37459884992719160915788729)
        ·
          refine ⟨28094913744539370686841547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37459884992719160915788729 28094913744539370686841547)
          ·
            refine ⟨42142370616809056030262321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28094913744539370686841547 42142370616809056030262321)
            ·
              refine ⟨31606777962606792022696741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42142370616809056030262321 31606777962606792022696741)
              ·
                refine ⟨5926270867988773504255639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31606777962606792022696741 5926270867988773504255639)
                ·
                  refine ⟨8889406301983160256383459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5926270867988773504255639 8889406301983160256383459)
                  ·
                    refine ⟨13334109452974740384575189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8889406301983160256383459 13334109452974740384575189)
                    ·
                      refine ⟨312518190304095477763481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13334109452974740384575189 312518190304095477763481)
                      ·
                        rfl

theorem cell23_608627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_608627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608627 prefixEnd_608627 := by exact prefixLift 608627
  have htrace : WordTrace (prefixWord ++ tailWord_608627) baseStart_608627 baseEnd_608627 := by
    simpa [prefixWord, tailWord_608627, baseEnd_608627] using wordTrace_append hprefix tailTrace_608627
  have hstable : (prefixWord ++ tailWord_608627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608627).length < 2 ^ (prefixWord ++ tailWord_608627).sum := by decide
  have hdescent : baseEnd_608627 < baseStart_608627 := by decide
  rcases family_descends (prefixWord ++ tailWord_608627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608644 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_608644 : Nat := 118140960795 + 608644 * 2 ^ 59
def prefixEnd_608644 : Nat := 4983230072969 + 3 ^ 40 * 608644 * 2
def baseEnd_608644 : Nat := 312526919475221911250903

theorem tailTrace_608644 : CollatzResearch.WordTrace tailWord_608644 prefixEnd_608644 312526919475221911250903 := by
  unfold tailWord_608644
  simp only [CollatzResearch.WordTrace]
  refine ⟨11099535203497105482288493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14799380271329473976384657 11099535203497105482288493)
  ·
    refine ⟨4162325701311414555858185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11099535203497105482288493 4162325701311414555858185)
    ·
      refine ⟨3121744275983560916893639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4162325701311414555858185 3121744275983560916893639)
      ·
        refine ⟨4682616413975341375340459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3121744275983560916893639 4682616413975341375340459)
        ·
          refine ⟨7023924620963012063010689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4682616413975341375340459 7023924620963012063010689)
          ·
            refine ⟨5267943465722259047258017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7023924620963012063010689 5267943465722259047258017)
            ·
              refine ⟨3950957599291694285443513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5267943465722259047258017 3950957599291694285443513)
              ·
                refine ⟨2963218199468770714082635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3950957599291694285443513 2963218199468770714082635)
                ·
                  refine ⟨4444827299203156071123953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2963218199468770714082635 4444827299203156071123953)
                  ·
                    refine ⟨3333620474402367053342965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4444827299203156071123953 3333620474402367053342965)
                    ·
                      refine ⟨312526919475221911250903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3333620474402367053342965 312526919475221911250903)
                      ·
                        rfl

theorem cell23_608644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_608644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608644 prefixEnd_608644 := by exact prefixLift 608644
  have htrace : WordTrace (prefixWord ++ tailWord_608644) baseStart_608644 baseEnd_608644 := by
    simpa [prefixWord, tailWord_608644, baseEnd_608644] using wordTrace_append hprefix tailTrace_608644
  have hstable : (prefixWord ++ tailWord_608644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608644).length < 2 ^ (prefixWord ++ tailWord_608644).sum := by decide
  have hdescent : baseEnd_608644 < baseStart_608644 := by decide
  rcases family_descends (prefixWord ++ tailWord_608644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608667 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 10]
def baseStart_608667 : Nat := 118140960795 + 608667 * 2 ^ 59
def prefixEnd_608667 : Nat := 4983230072969 + 3 ^ 40 * 608667 * 2
def baseEnd_608667 : Nat := 312538729530275321263297

theorem tailTrace_608667 : CollatzResearch.WordTrace tailWord_608667 prefixEnd_608667 312538729530275321263297 := by
  unfold tailWord_608667
  simp only [CollatzResearch.WordTrace]
  refine ⟨22199909285910885892664255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14799939523940590595109503 22199909285910885892664255)
  ·
    refine ⟨33299863928866328838996383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22199909285910885892664255 33299863928866328838996383)
    ·
      refine ⟨49949795893299493258494575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33299863928866328838996383 49949795893299493258494575)
      ·
        refine ⟨74924693839949239887741863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49949795893299493258494575 74924693839949239887741863)
        ·
          refine ⟨112387040759923859831612795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74924693839949239887741863 112387040759923859831612795)
          ·
            refine ⟨168580561139885789747419193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112387040759923859831612795 168580561139885789747419193)
            ·
              refine ⟨126435420854914342310564395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168580561139885789747419193 126435420854914342310564395)
              ·
                refine ⟨189653131282371513465846593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126435420854914342310564395 189653131282371513465846593)
                ·
                  refine ⟨142239848461778635099384945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189653131282371513465846593 142239848461778635099384945)
                  ·
                    refine ⟨106679886346333976324538709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 142239848461778635099384945 106679886346333976324538709)
                    ·
                      refine ⟨312538729530275321263297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 106679886346333976324538709 312538729530275321263297)
                      ·
                        rfl

theorem cell23_608667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 10].length) (baseStart_608667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608667 prefixEnd_608667 := by exact prefixLift 608667
  have htrace : WordTrace (prefixWord ++ tailWord_608667) baseStart_608667 baseEnd_608667 := by
    simpa [prefixWord, tailWord_608667, baseEnd_608667] using wordTrace_append hprefix tailTrace_608667
  have hstable : (prefixWord ++ tailWord_608667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608667).length < 2 ^ (prefixWord ++ tailWord_608667).sum := by decide
  have hdescent : baseEnd_608667 < baseStart_608667 := by decide
  rcases family_descends (prefixWord ++ tailWord_608667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608671 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 1, 6, 2]
def baseStart_608671 : Nat := 118140960795 + 608671 * 2 ^ 59
def prefixEnd_608671 : Nat := 4983230072969 + 3 ^ 40 * 608671 * 2
def baseEnd_608671 : Nat := 312540783452893305613279

theorem tailTrace_608671 : CollatzResearch.WordTrace tailWord_608671 prefixEnd_608671 312540783452893305613279 := by
  unfold tailWord_608671
  simp only [CollatzResearch.WordTrace]
  refine ⟨22200055177896394575809867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14800036785264263050539911 22200055177896394575809867)
  ·
    refine ⟨33300082766844591863714801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22200055177896394575809867 33300082766844591863714801)
    ·
      refine ⟨24975062075133443897786101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33300082766844591863714801 24975062075133443897786101)
      ·
        refine ⟨2341412069543760365417447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24975062075133443897786101 2341412069543760365417447)
        ·
          refine ⟨3512118104315640548126171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2341412069543760365417447 3512118104315640548126171)
          ·
            refine ⟨5268177156473460822189257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3512118104315640548126171 5268177156473460822189257)
            ·
              refine ⟨3951132867355095616641943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5268177156473460822189257 3951132867355095616641943)
              ·
                refine ⟨5926699301032643424962915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3951132867355095616641943 5926699301032643424962915)
                ·
                  refine ⟨8890048951548965137444373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5926699301032643424962915 8890048951548965137444373)
                  ·
                    refine ⟨416721044603857740817705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8890048951548965137444373 416721044603857740817705)
                    ·
                      refine ⟨312540783452893305613279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 416721044603857740817705 312540783452893305613279)
                      ·
                        rfl

theorem cell23_608671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_608671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608671 prefixEnd_608671 := by exact prefixLift 608671
  have htrace : WordTrace (prefixWord ++ tailWord_608671) baseStart_608671 baseEnd_608671 := by
    simpa [prefixWord, tailWord_608671, baseEnd_608671] using wordTrace_append hprefix tailTrace_608671
  have hstable : (prefixWord ++ tailWord_608671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608671).length < 2 ^ (prefixWord ++ tailWord_608671).sum := by decide
  have hdescent : baseEnd_608671 < baseStart_608671 := by decide
  rcases family_descends (prefixWord ++ tailWord_608671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608711 : List Nat := [1, 1, 4, 1, 1, 5, 2, 2, 6]
def baseStart_608711 : Nat := 118140960795 + 608711 * 2 ^ 59
def prefixEnd_608711 : Nat := 4983230072969 + 3 ^ 40 * 608711 * 2
def baseEnd_608711 : Nat := 34729035853230349901455

theorem tailTrace_608711 : CollatzResearch.WordTrace tailWord_608711 prefixEnd_608711 34729035853230349901455 := by
  unfold tailWord_608711
  simp only [CollatzResearch.WordTrace]
  refine ⟨22201514097751481407265987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14801009398500987604843991 22201514097751481407265987)
  ·
    refine ⟨33302271146627222110898981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22201514097751481407265987 33302271146627222110898981)
    ·
      refine ⟨6244175839992604145793559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33302271146627222110898981 6244175839992604145793559)
      ·
        refine ⟨9366263759988906218690339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6244175839992604145793559 9366263759988906218690339)
        ·
          refine ⟨14049395639983359328035509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9366263759988906218690339 14049395639983359328035509)
          ·
            refine ⟨1317130841248439937003329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14049395639983359328035509 1317130841248439937003329)
            ·
              refine ⟨987848130936329952752497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317130841248439937003329 987848130936329952752497)
              ·
                refine ⟨740886098202247464564373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 987848130936329952752497 740886098202247464564373)
                ·
                  refine ⟨34729035853230349901455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 740886098202247464564373 34729035853230349901455)
                  ·
                    rfl

theorem cell23_608711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 6].length) (baseStart_608711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608711 prefixEnd_608711 := by exact prefixLift 608711
  have htrace : WordTrace (prefixWord ++ tailWord_608711) baseStart_608711 baseEnd_608711 := by
    simpa [prefixWord, tailWord_608711, baseEnd_608711] using wordTrace_append hprefix tailTrace_608711
  have hstable : (prefixWord ++ tailWord_608711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608711).length < 2 ^ (prefixWord ++ tailWord_608711).sum := by decide
  have hdescent : baseEnd_608711 < baseStart_608711 := by decide
  rcases family_descends (prefixWord ++ tailWord_608711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608714 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_608714 : Nat := 118140960795 + 608714 * 2 ^ 59
def prefixEnd_608714 : Nat := 4983230072969 + 3 ^ 40 * 608714 * 2
def baseEnd_608714 : Nat := 312562863121036637375581

theorem tailTrace_608714 : CollatzResearch.WordTrace tailWord_608714 prefixEnd_608714 312562863121036637375581 := by
  unfold tailWord_608714
  simp only [CollatzResearch.WordTrace]
  refine ⟨5550405879185153229906299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14801082344493741946416797 5550405879185153229906299)
  ·
    refine ⟨8325608818777729844859449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5550405879185153229906299 8325608818777729844859449)
    ·
      refine ⟨6244206614083297383644587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8325608818777729844859449 6244206614083297383644587)
      ·
        refine ⟨9366309921124946075466881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6244206614083297383644587 9366309921124946075466881)
        ·
          refine ⟨7024732440843709556600161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9366309921124946075466881 7024732440843709556600161)
          ·
            refine ⟨5268549330632782167450121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7024732440843709556600161 5268549330632782167450121)
            ·
              refine ⟨3951411997974586625587591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5268549330632782167450121 3951411997974586625587591)
              ·
                refine ⟨5927117996961879938381387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3951411997974586625587591 5927117996961879938381387)
                ·
                  refine ⟨8890676995442819907572081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5927117996961879938381387 8890676995442819907572081)
                  ·
                    refine ⟨6668007746582114930679061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8890676995442819907572081 6668007746582114930679061)
                    ·
                      refine ⟨312562863121036637375581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6668007746582114930679061 312562863121036637375581)
                      ·
                        rfl

theorem cell23_608714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_608714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608714 prefixEnd_608714 := by exact prefixLift 608714
  have htrace : WordTrace (prefixWord ++ tailWord_608714) baseStart_608714 baseEnd_608714 := by
    simpa [prefixWord, tailWord_608714, baseEnd_608714] using wordTrace_append hprefix tailTrace_608714
  have hstable : (prefixWord ++ tailWord_608714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608714).length < 2 ^ (prefixWord ++ tailWord_608714).sum := by decide
  have hdescent : baseEnd_608714 < baseStart_608714 := by decide
  rcases family_descends (prefixWord ++ tailWord_608714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608721 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 7, 1, 3]
def baseStart_608721 : Nat := 118140960795 + 608721 * 2 ^ 59
def prefixEnd_608721 : Nat := 4983230072969 + 3 ^ 40 * 608721 * 2
def baseEnd_608721 : Nat := 312566457485618109988049

theorem tailTrace_608721 : CollatzResearch.WordTrace tailWord_608721 prefixEnd_608721 312566457485618109988049 := by
  unfold tailWord_608721
  simp only [CollatzResearch.WordTrace]
  refine ⟨22201878827715253115130017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14801252551810168743420011 22201878827715253115130017)
  ·
    refine ⟨16651409120786439836347513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22201878827715253115130017 16651409120786439836347513)
    ·
      refine ⟨12488556840589829877260635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16651409120786439836347513 12488556840589829877260635)
      ·
        refine ⟨18732835260884744815890953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12488556840589829877260635 18732835260884744815890953)
        ·
          refine ⟨14049626445663558611918215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18732835260884744815890953 14049626445663558611918215)
          ·
            refine ⟨21074439668495337917877323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14049626445663558611918215 21074439668495337917877323)
            ·
              refine ⟨31611659502743006876815985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21074439668495337917877323 31611659502743006876815985)
              ·
                refine ⟨23708744627057255157611989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31611659502743006876815985 23708744627057255157611989)
                ·
                  refine ⟨555673702196654417756531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 23708744627057255157611989 555673702196654417756531)
                  ·
                    refine ⟨833510553294981626634797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 555673702196654417756531 833510553294981626634797)
                    ·
                      refine ⟨312566457485618109988049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 833510553294981626634797 312566457485618109988049)
                      ·
                        rfl

theorem cell23_608721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_608721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608721 prefixEnd_608721 := by exact prefixLift 608721
  have htrace : WordTrace (prefixWord ++ tailWord_608721) baseStart_608721 baseEnd_608721 := by
    simpa [prefixWord, tailWord_608721, baseEnd_608721] using wordTrace_append hprefix tailTrace_608721
  have hstable : (prefixWord ++ tailWord_608721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608721).length < 2 ^ (prefixWord ++ tailWord_608721).sum := by decide
  have hdescent : baseEnd_608721 < baseStart_608721 := by decide
  rcases family_descends (prefixWord ++ tailWord_608721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608755 : List Nat := [1, 1, 1, 2, 2, 2, 6, 3, 1, 1, 3]
def baseStart_608755 : Nat := 118140960795 + 608755 * 2 ^ 59
def prefixEnd_608755 : Nat := 4983230072969 + 3 ^ 40 * 608755 * 2
def baseEnd_608755 : Nat := 312583915827870976962893

theorem tailTrace_608755 : CollatzResearch.WordTrace tailWord_608755 prefixEnd_608755 312583915827870976962893 := by
  unfold tailWord_608755
  simp only [CollatzResearch.WordTrace]
  refine ⟨22203118909592076921867719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14802079273061384614578479 22203118909592076921867719)
  ·
    refine ⟨33304678364388115382801579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22203118909592076921867719 33304678364388115382801579)
    ·
      refine ⟨49957017546582173074202369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33304678364388115382801579 49957017546582173074202369)
      ·
        refine ⟨37467763159936629805651777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49957017546582173074202369 37467763159936629805651777)
        ·
          refine ⟨28100822369952472354238833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37467763159936629805651777 28100822369952472354238833)
          ·
            refine ⟨21075616777464354265679125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28100822369952472354238833 21075616777464354265679125)
            ·
              refine ⟨987919536443641606203709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21075616777464354265679125 987919536443641606203709)
              ·
                refine ⟨370469826166365602326391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 987919536443641606203709 370469826166365602326391)
                ·
                  refine ⟨555704739249548403489587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370469826166365602326391 555704739249548403489587)
                  ·
                    refine ⟨833557108874322605234381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 555704739249548403489587 833557108874322605234381)
                    ·
                      refine ⟨312583915827870976962893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 833557108874322605234381 312583915827870976962893)
                      ·
                        rfl

theorem cell23_608755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 1, 1, 3].length) (baseStart_608755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608755 prefixEnd_608755 := by exact prefixLift 608755
  have htrace : WordTrace (prefixWord ++ tailWord_608755) baseStart_608755 baseEnd_608755 := by
    simpa [prefixWord, tailWord_608755, baseEnd_608755] using wordTrace_append hprefix tailTrace_608755
  have hstable : (prefixWord ++ tailWord_608755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608755).length < 2 ^ (prefixWord ++ tailWord_608755).sum := by decide
  have hdescent : baseEnd_608755 < baseStart_608755 := by decide
  rcases family_descends (prefixWord ++ tailWord_608755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608758 : List Nat := [5, 1, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_608758 : Nat := 118140960795 + 608758 * 2 ^ 59
def prefixEnd_608758 : Nat := 4983230072969 + 3 ^ 40 * 608758 * 2
def baseEnd_608758 : Nat := 104195152089944821741793

theorem tailTrace_608758 : CollatzResearch.WordTrace tailWord_608758 prefixEnd_608758 104195152089944821741793 := by
  unfold tailWord_608758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1387701770536325527139183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14802152219054138956151285 1387701770536325527139183)
  ·
    refine ⟨2081552655804488290708775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1387701770536325527139183 2081552655804488290708775)
    ·
      refine ⟨3122328983706732436063163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2081552655804488290708775 3122328983706732436063163)
      ·
        refine ⟨4683493475560098654094745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3122328983706732436063163 4683493475560098654094745)
        ·
          refine ⟨3512620106670073990571059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4683493475560098654094745 3512620106670073990571059)
          ·
            refine ⟨5268930160005110985856589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3512620106670073990571059 5268930160005110985856589)
            ·
              refine ⟨1975848810001916619696221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5268930160005110985856589 1975848810001916619696221)
              ·
                refine ⟨740943303750718732386083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1975848810001916619696221 740943303750718732386083)
                ·
                  refine ⟨1111414955626078098579125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740943303750718732386083 1111414955626078098579125)
                  ·
                    refine ⟨104195152089944821741793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1111414955626078098579125 104195152089944821741793)
                    ·
                      rfl

theorem cell23_608758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_608758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608758 prefixEnd_608758 := by exact prefixLift 608758
  have htrace : WordTrace (prefixWord ++ tailWord_608758) baseStart_608758 baseEnd_608758 := by
    simpa [prefixWord, tailWord_608758, baseEnd_608758] using wordTrace_append hprefix tailTrace_608758
  have hstable : (prefixWord ++ tailWord_608758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608758).length < 2 ^ (prefixWord ++ tailWord_608758).sum := by decide
  have hdescent : baseEnd_608758 < baseStart_608758 := by decide
  rcases family_descends (prefixWord ++ tailWord_608758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608771 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 4, 4]
def baseStart_608771 : Nat := 118140960795 + 608771 * 2 ^ 59
def prefixEnd_608771 : Nat := 4983230072969 + 3 ^ 40 * 608771 * 2
def baseEnd_608771 : Nat := 104197377172780971454273

theorem tailTrace_608771 : CollatzResearch.WordTrace tailWord_608771 prefixEnd_608771 104197377172780971454273 := by
  unfold tailWord_608771
  simp only [CollatzResearch.WordTrace]
  refine ⟨22203702477534111654450167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14802468318356074436300111 22203702477534111654450167)
  ·
    refine ⟨33305553716301167481675251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22203702477534111654450167 33305553716301167481675251)
    ·
      refine ⟨49958330574451751222512877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33305553716301167481675251 49958330574451751222512877)
      ·
        refine ⟨18734373965419406708442329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49958330574451751222512877 18734373965419406708442329)
        ·
          refine ⟨14050780474064555031331747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18734373965419406708442329 14050780474064555031331747)
          ·
            refine ⟨21076170711096832546997621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14050780474064555031331747 21076170711096832546997621)
            ·
              refine ⟨1975891004165328051281027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21076170711096832546997621 1975891004165328051281027)
              ·
                refine ⟨2963836506247992076921541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975891004165328051281027 2963836506247992076921541)
                ·
                  refine ⟨555719344921498514422789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2963836506247992076921541 555719344921498514422789)
                  ·
                    refine ⟨104197377172780971454273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 555719344921498514422789 104197377172780971454273)
                    ·
                      rfl

theorem cell23_608771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 4].length) (baseStart_608771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608771 prefixEnd_608771 := by exact prefixLift 608771
  have htrace : WordTrace (prefixWord ++ tailWord_608771) baseStart_608771 baseEnd_608771 := by
    simpa [prefixWord, tailWord_608771, baseEnd_608771] using wordTrace_append hprefix tailTrace_608771
  have hstable : (prefixWord ++ tailWord_608771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608771).length < 2 ^ (prefixWord ++ tailWord_608771).sum := by decide
  have hdescent : baseEnd_608771 < baseStart_608771 := by decide
  rcases family_descends (prefixWord ++ tailWord_608771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608772 : List Nat := [2, 3, 2, 3, 1, 1, 2, 4, 1, 1, 3]
def baseStart_608772 : Nat := 118140960795 + 608772 * 2 ^ 59
def prefixEnd_608772 : Nat := 4983230072969 + 3 ^ 40 * 608772 * 2
def baseEnd_608772 : Nat := 312592644998997410450315

theorem tailTrace_608772 : CollatzResearch.WordTrace tailWord_608772 prefixEnd_608772 312592644998997410450315 := by
  unfold tailWord_608772
  simp only [CollatzResearch.WordTrace]
  refine ⟨11101869475265244412618285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14802492633686992550157713 11101869475265244412618285)
  ·
    refine ⟨4163201053224466654731857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11101869475265244412618285 4163201053224466654731857)
    ·
      refine ⟨3122400789918349991048893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4163201053224466654731857 3122400789918349991048893)
      ·
        refine ⟨1170900296219381246643335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3122400789918349991048893 1170900296219381246643335)
        ·
          refine ⟨1756350444329071869965003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170900296219381246643335 1756350444329071869965003)
          ·
            refine ⟨2634525666493607804947505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756350444329071869965003 2634525666493607804947505)
            ·
              refine ⟨1975894249870205853710629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2634525666493607804947505 1975894249870205853710629)
              ·
                refine ⟨370480171850663597570743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1975894249870205853710629 370480171850663597570743)
                ·
                  refine ⟨555720257775995396356115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370480171850663597570743 555720257775995396356115)
                  ·
                    refine ⟨833580386663993094534173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 555720257775995396356115 833580386663993094534173)
                    ·
                      refine ⟨312592644998997410450315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 833580386663993094534173 312592644998997410450315)
                      ·
                        rfl

theorem cell23_608772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_608772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608772 prefixEnd_608772 := by exact prefixLift 608772
  have htrace : WordTrace (prefixWord ++ tailWord_608772) baseStart_608772 baseEnd_608772 := by
    simpa [prefixWord, tailWord_608772, baseEnd_608772] using wordTrace_append hprefix tailTrace_608772
  have hstable : (prefixWord ++ tailWord_608772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608772).length < 2 ^ (prefixWord ++ tailWord_608772).sum := by decide
  have hdescent : baseEnd_608772 < baseStart_608772 := by decide
  rcases family_descends (prefixWord ++ tailWord_608772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608811 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 3]
def baseStart_608811 : Nat := 118140960795 + 608811 * 2 ^ 59
def prefixEnd_608811 : Nat := 4983230072969 + 3 ^ 40 * 608811 * 2
def baseEnd_608811 : Nat := 312612670744522757862635

theorem tailTrace_608811 : CollatzResearch.WordTrace tailWord_608811 prefixEnd_608811 312612670744522757862635 := by
  unfold tailWord_608811
  simp only [CollatzResearch.WordTrace]
  refine ⟨22205161397389198485906287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14803440931592798990604191 22205161397389198485906287)
  ·
    refine ⟨33307742096083797728859431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22205161397389198485906287 33307742096083797728859431)
    ·
      refine ⟨49961613144125696593289147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33307742096083797728859431 49961613144125696593289147)
      ·
        refine ⟨74942419716188544889933721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49961613144125696593289147 74942419716188544889933721)
        ·
          refine ⟨56206814787141408667450291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74942419716188544889933721 56206814787141408667450291)
          ·
            refine ⟨84310222180712113001175437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56206814787141408667450291 84310222180712113001175437)
            ·
              refine ⟨31616333317767042375440789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84310222180712113001175437 31616333317767042375440789)
              ·
                refine ⟨1482015624270330111348787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31616333317767042375440789 1482015624270330111348787)
                ·
                  refine ⟨2223023436405495167023181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482015624270330111348787 2223023436405495167023181)
                  ·
                    refine ⟨833633788652060687633693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2223023436405495167023181 833633788652060687633693)
                    ·
                      refine ⟨312612670744522757862635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 833633788652060687633693 312612670744522757862635)
                      ·
                        rfl

theorem cell23_608811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 3].length) (baseStart_608811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608811 prefixEnd_608811 := by exact prefixLift 608811
  have htrace : WordTrace (prefixWord ++ tailWord_608811) baseStart_608811 baseEnd_608811 := by
    simpa [prefixWord, tailWord_608811, baseEnd_608811] using wordTrace_append hprefix tailTrace_608811
  have hstable : (prefixWord ++ tailWord_608811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608811).length < 2 ^ (prefixWord ++ tailWord_608811).sum := by decide
  have hdescent : baseEnd_608811 < baseStart_608811 := by decide
  rcases family_descends (prefixWord ++ tailWord_608811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608921 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 1, 7]
def baseStart_608921 : Nat := 118140960795 + 608921 * 2 ^ 59
def prefixEnd_608921 : Nat := 4983230072969 + 3 ^ 40 * 608921 * 2
def baseEnd_608921 : Nat := 104223051205505775829043

theorem tailTrace_608921 : CollatzResearch.WordTrace tailWord_608921 prefixEnd_608921 104223051205505775829043 := by
  unfold tailWord_608921
  simp only [CollatzResearch.WordTrace]
  refine ⟨22209173426990687272410617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14806115617993791514940411 22209173426990687272410617)
  ·
    refine ⟨16656880070243015454307963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22209173426990687272410617 16656880070243015454307963)
    ·
      refine ⟨24985320105364523181461945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16656880070243015454307963 24985320105364523181461945)
      ·
        refine ⟨18738990079023392386096459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24985320105364523181461945 18738990079023392386096459)
        ·
          refine ⟨28108485118535088579144689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18738990079023392386096459 28108485118535088579144689)
          ·
            refine ⟨21081363838901316434358517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28108485118535088579144689 21081363838901316434358517)
            ·
              refine ⟨1976377859896998415721111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21081363838901316434358517 1976377859896998415721111)
              ·
                refine ⟨2964566789845497623581667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1976377859896998415721111 2964566789845497623581667)
                ·
                  refine ⟨4446850184768246435372501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2964566789845497623581667 4446850184768246435372501)
                  ·
                    refine ⟨104223051205505775829043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4446850184768246435372501 104223051205505775829043)
                    ·
                      rfl

theorem cell23_608921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 7].length) (baseStart_608921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608921 prefixEnd_608921 := by exact prefixLift 608921
  have htrace : WordTrace (prefixWord ++ tailWord_608921) baseStart_608921 baseEnd_608921 := by
    simpa [prefixWord, tailWord_608921, baseEnd_608921] using wordTrace_append hprefix tailTrace_608921
  have hstable : (prefixWord ++ tailWord_608921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608921).length < 2 ^ (prefixWord ++ tailWord_608921).sum := by decide
  have hdescent : baseEnd_608921 < baseStart_608921 := by decide
  rcases family_descends (prefixWord ++ tailWord_608921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608931 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 5]
def baseStart_608931 : Nat := 118140960795 + 608931 * 2 ^ 59
def prefixEnd_608931 : Nat := 4983230072969 + 3 ^ 40 * 608931 * 2
def baseEnd_608931 : Nat := 312674288423062288362083

theorem tailTrace_608931 : CollatzResearch.WordTrace tailWord_608931 prefixEnd_608931 312674288423062288362083 := by
  unfold tailWord_608931
  simp only [CollatzResearch.WordTrace]
  refine ⟨22209538156954458980274647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14806358771302972653516431 22209538156954458980274647)
  ·
    refine ⟨33314307235431688470411971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22209538156954458980274647 33314307235431688470411971)
    ·
      refine ⟨49971460853147532705617957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33314307235431688470411971 49971460853147532705617957)
      ·
        refine ⟨9369648909965162382303367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49971460853147532705617957 9369648909965162382303367)
        ·
          refine ⟨14054473364947743573455051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9369648909965162382303367 14054473364947743573455051)
          ·
            refine ⟨21081710047421615360182577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14054473364947743573455051 21081710047421615360182577)
            ·
              refine ⟨15811282535566211520136933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21081710047421615360182577 15811282535566211520136933)
              ·
                refine ⟨2964615475418664660025675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15811282535566211520136933 2964615475418664660025675)
                ·
                  refine ⟨4446923213127996990038513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2964615475418664660025675 4446923213127996990038513)
                  ·
                    refine ⟨3335192409845997742528885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4446923213127996990038513 3335192409845997742528885)
                    ·
                      refine ⟨312674288423062288362083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3335192409845997742528885 312674288423062288362083)
                      ·
                        rfl

theorem cell23_608931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_608931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608931 prefixEnd_608931 := by exact prefixLift 608931
  have htrace : WordTrace (prefixWord ++ tailWord_608931) baseStart_608931 baseEnd_608931 := by
    simpa [prefixWord, tailWord_608931, baseEnd_608931] using wordTrace_append hprefix tailTrace_608931
  have hstable : (prefixWord ++ tailWord_608931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608931).length < 2 ^ (prefixWord ++ tailWord_608931).sum := by decide
  have hdescent : baseEnd_608931 < baseStart_608931 := by decide
  rcases family_descends (prefixWord ++ tailWord_608931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608942 : List Nat := [4, 1, 4, 1, 1, 1, 2, 4, 5]
def baseStart_608942 : Nat := 118140960795 + 608942 * 2 ^ 59
def prefixEnd_608942 : Nat := 4983230072969 + 3 ^ 40 * 608942 * 2
def baseEnd_608942 : Nat := 34742215190029082813837

theorem tailTrace_608942 : CollatzResearch.WordTrace tailWord_608942 prefixEnd_608942 34742215190029082813837 := by
  unfold tailWord_608942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2776242419989325982365635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14806626239943071905950053 2776242419989325982365635)
  ·
    refine ⟨4164363629983988973548453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2776242419989325982365635 4164363629983988973548453)
    ·
      refine ⟨780818180621997932540335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4164363629983988973548453 780818180621997932540335)
      ·
        refine ⟨1171227270932996898810503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 780818180621997932540335 1171227270932996898810503)
        ·
          refine ⟨1756840906399495348215755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1171227270932996898810503 1756840906399495348215755)
          ·
            refine ⟨2635261359599243022323633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756840906399495348215755 2635261359599243022323633)
            ·
              refine ⟨1976446019699432266742725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2635261359599243022323633 1976446019699432266742725)
              ·
                refine ⟨370583628693643550014261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1976446019699432266742725 370583628693643550014261)
                ·
                  refine ⟨34742215190029082813837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 370583628693643550014261 34742215190029082813837)
                  ·
                    rfl

theorem cell23_608942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_608942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608942 prefixEnd_608942 := by exact prefixLift 608942
  have htrace : WordTrace (prefixWord ++ tailWord_608942) baseStart_608942 baseEnd_608942 := by
    simpa [prefixWord, tailWord_608942, baseEnd_608942] using wordTrace_append hprefix tailTrace_608942
  have hstable : (prefixWord ++ tailWord_608942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608942).length < 2 ^ (prefixWord ++ tailWord_608942).sum := by decide
  have hdescent : baseEnd_608942 < baseStart_608942 := by decide
  rcases family_descends (prefixWord ++ tailWord_608942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608958 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_608958 : Nat := 118140960795 + 608958 * 2 ^ 59
def prefixEnd_608958 : Nat := 4983230072969 + 3 ^ 40 * 608958 * 2
def baseEnd_608958 : Nat := 312688152400733682724459

theorem tailTrace_608958 : CollatzResearch.WordTrace tailWord_608958 prefixEnd_608958 312688152400733682724459 := by
  unfold tailWord_608958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2776315365982080323938441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14807015285237761727671685 2776315365982080323938441)
  ·
    refine ⟨2082236524486560242953831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2776315365982080323938441 2082236524486560242953831)
    ·
      refine ⟨3123354786729840364430747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2082236524486560242953831 3123354786729840364430747)
      ·
        refine ⟨4685032180094760546646121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3123354786729840364430747 4685032180094760546646121)
        ·
          refine ⟨3513774135071070409984591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4685032180094760546646121 3513774135071070409984591)
          ·
            refine ⟨5270661202606605614976887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3513774135071070409984591 5270661202606605614976887)
            ·
              refine ⟨7905991803909908422465331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5270661202606605614976887 7905991803909908422465331)
              ·
                refine ⟨11858987705864862633697997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7905991803909908422465331 11858987705864862633697997)
                ·
                  refine ⟨4447120389699323487636749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11858987705864862633697997 4447120389699323487636749)
                  ·
                    refine ⟨1667670146137246307863781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4447120389699323487636749 1667670146137246307863781)
                    ·
                      refine ⟨312688152400733682724459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1667670146137246307863781 312688152400733682724459)
                      ·
                        rfl

theorem cell23_608958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_608958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608958 prefixEnd_608958 := by exact prefixLift 608958
  have htrace : WordTrace (prefixWord ++ tailWord_608958) baseStart_608958 baseEnd_608958 := by
    simpa [prefixWord, tailWord_608958, baseEnd_608958] using wordTrace_append hprefix tailTrace_608958
  have hstable : (prefixWord ++ tailWord_608958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608958).length < 2 ^ (prefixWord ++ tailWord_608958).sum := by decide
  have hdescent : baseEnd_608958 < baseStart_608958 := by decide
  rcases family_descends (prefixWord ++ tailWord_608958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608995 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 3]
def baseStart_608995 : Nat := 118140960795 + 608995 * 2 ^ 59
def prefixEnd_608995 : Nat := 4983230072969 + 3 ^ 40 * 608995 * 2
def baseEnd_608995 : Nat := 312707151184950037961789

theorem tailTrace_608995 : CollatzResearch.WordTrace tailWord_608995 prefixEnd_608995 312707151184950037961789 := by
  unfold tailWord_608995
  simp only [CollatzResearch.WordTrace]
  refine ⟨22211872428722597910604439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14807914952481731940402959 22211872428722597910604439)
  ·
    refine ⟨33317808643083896865906659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22211872428722597910604439 33317808643083896865906659)
    ·
      refine ⟨49976712964625845298859989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33317808643083896865906659 49976712964625845298859989)
      ·
        refine ⟨1171329210108418249192031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 49976712964625845298859989 1171329210108418249192031)
        ·
          refine ⟨1756993815162627373788047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1171329210108418249192031 1756993815162627373788047)
          ·
            refine ⟨2635490722743941060682071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756993815162627373788047 2635490722743941060682071)
            ·
              refine ⟨3953236084115911591023107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2635490722743941060682071 3953236084115911591023107)
              ·
                refine ⟨5929854126173867386534661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3953236084115911591023107 5929854126173867386534661)
                ·
                  refine ⟨1111847648657600134975249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5929854126173867386534661 1111847648657600134975249)
                  ·
                    refine ⟨833885736493200101231437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1111847648657600134975249 833885736493200101231437)
                    ·
                      refine ⟨312707151184950037961789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 833885736493200101231437 312707151184950037961789)
                      ·
                        rfl

theorem cell23_608995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_608995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_608995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_608995 prefixEnd_608995 := by exact prefixLift 608995
  have htrace : WordTrace (prefixWord ++ tailWord_608995) baseStart_608995 baseEnd_608995 := by
    simpa [prefixWord, tailWord_608995, baseEnd_608995] using wordTrace_append hprefix tailTrace_608995
  have hstable : (prefixWord ++ tailWord_608995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608995).length < 2 ^ (prefixWord ++ tailWord_608995).sum := by decide
  have hdescent : baseEnd_608995 < baseStart_608995 := by decide
  rcases family_descends (prefixWord ++ tailWord_608995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609001 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 8]
def baseStart_609001 : Nat := 118140960795 + 609001 * 2 ^ 59
def prefixEnd_609001 : Nat := 4983230072969 + 3 ^ 40 * 609001 * 2
def baseEnd_609001 : Nat := 312710232068877014486761

theorem tailTrace_609001 : CollatzResearch.WordTrace tailWord_609001 prefixEnd_609001 312710232068877014486761 := by
  unfold tailWord_609001
  simp only [CollatzResearch.WordTrace]
  refine ⟨22212091266700860935322857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14808060844467240623548571 22212091266700860935322857)
  ·
    refine ⟨16659068450025645701492143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22212091266700860935322857 16659068450025645701492143)
    ·
      refine ⟨24988602675038468552238215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16659068450025645701492143 24988602675038468552238215)
      ·
        refine ⟨37482904012557702828357323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24988602675038468552238215 37482904012557702828357323)
        ·
          refine ⟨56224356018836554242535985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37482904012557702828357323 56224356018836554242535985)
          ·
            refine ⟨42168267014127415681901989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56224356018836554242535985 42168267014127415681901989)
            ·
              refine ⟨7906550065148890440356623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42168267014127415681901989 7906550065148890440356623)
              ·
                refine ⟨11859825097723335660534935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7906550065148890440356623 11859825097723335660534935)
                ·
                  refine ⟨17789737646585003490802403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11859825097723335660534935 17789737646585003490802403)
                  ·
                    refine ⟨26684606469877505236203605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17789737646585003490802403 26684606469877505236203605)
                    ·
                      refine ⟨312710232068877014486761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 26684606469877505236203605 312710232068877014486761)
                      ·
                        rfl

theorem cell23_609001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_609001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609001 prefixEnd_609001 := by exact prefixLift 609001
  have htrace : WordTrace (prefixWord ++ tailWord_609001) baseStart_609001 baseEnd_609001 := by
    simpa [prefixWord, tailWord_609001, baseEnd_609001] using wordTrace_append hprefix tailTrace_609001
  have hstable : (prefixWord ++ tailWord_609001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609001).length < 2 ^ (prefixWord ++ tailWord_609001).sum := by decide
  have hdescent : baseEnd_609001 < baseStart_609001 := by decide
  rcases family_descends (prefixWord ++ tailWord_609001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609011 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 2, 9]
def baseStart_609011 : Nat := 118140960795 + 609011 * 2 ^ 59
def prefixEnd_609011 : Nat := 4983230072969 + 3 ^ 40 * 609011 * 2
def baseEnd_609011 : Nat := 104238455625140658453905

theorem tailTrace_609011 : CollatzResearch.WordTrace tailWord_609011 prefixEnd_609011 104238455625140658453905 := by
  unfold tailWord_609011
  simp only [CollatzResearch.WordTrace]
  refine ⟨22212455996664632643186887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14808303997776421762124591 22212455996664632643186887)
  ·
    refine ⟨33318683994996948964780331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22212455996664632643186887 33318683994996948964780331)
    ·
      refine ⟨49978025992495423447170497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33318683994996948964780331 49978025992495423447170497)
      ·
        refine ⟨37483519494371567585377873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49978025992495423447170497 37483519494371567585377873)
        ·
          refine ⟨28112639620778675689033405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37483519494371567585377873 28112639620778675689033405)
          ·
            refine ⟨10542239857792003383387527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28112639620778675689033405 10542239857792003383387527)
            ·
              refine ⟨15813359786688005075081291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10542239857792003383387527 15813359786688005075081291)
              ·
                refine ⟨23720039680032007612621937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15813359786688005075081291 23720039680032007612621937)
                ·
                  refine ⟨17790029760024005709466453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23720039680032007612621937 17790029760024005709466453)
                  ·
                    refine ⟨104238455625140658453905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 17790029760024005709466453 104238455625140658453905)
                    ·
                      rfl

theorem cell23_609011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 9].length) (baseStart_609011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609011 prefixEnd_609011 := by exact prefixLift 609011
  have htrace : WordTrace (prefixWord ++ tailWord_609011) baseStart_609011 baseEnd_609011 := by
    simpa [prefixWord, tailWord_609011, baseEnd_609011] using wordTrace_append hprefix tailTrace_609011
  have hstable : (prefixWord ++ tailWord_609011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609011).length < 2 ^ (prefixWord ++ tailWord_609011).sum := by decide
  have hdescent : baseEnd_609011 < baseStart_609011 := by decide
  rcases family_descends (prefixWord ++ tailWord_609011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609025 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_609025 : Nat := 118140960795 + 609025 * 2 ^ 59
def prefixEnd_609025 : Nat := 4983230072969 + 3 ^ 40 * 609025 * 2
def baseEnd_609025 : Nat := 312722555604584920586651

theorem tailTrace_609025 : CollatzResearch.WordTrace tailWord_609025 prefixEnd_609025 312722555604584920586651 := by
  unfold tailWord_609025
  simp only [CollatzResearch.WordTrace]
  refine ⟨22212966618613913034196529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14808644412409275356131019 22212966618613913034196529)
  ·
    refine ⟨16659724963960434775647397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22212966618613913034196529 16659724963960434775647397)
    ·
      refine ⟨3123698430742581520433887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16659724963960434775647397 3123698430742581520433887)
      ·
        refine ⟨4685547646113872280650831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3123698430742581520433887 4685547646113872280650831)
        ·
          refine ⟨7028321469170808420976247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4685547646113872280650831 7028321469170808420976247)
          ·
            refine ⟨10542482203756212631464371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7028321469170808420976247 10542482203756212631464371)
            ·
              refine ⟨15813723305634318947196557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10542482203756212631464371 15813723305634318947196557)
              ·
                refine ⟨5930146239612869605198709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15813723305634318947196557 5930146239612869605198709)
                ·
                  refine ⟨555951209963706525487379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5930146239612869605198709 555951209963706525487379)
                  ·
                    refine ⟨833926814945559788231069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 555951209963706525487379 833926814945559788231069)
                    ·
                      refine ⟨312722555604584920586651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 833926814945559788231069 312722555604584920586651)
                      ·
                        rfl

theorem cell23_609025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_609025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609025 prefixEnd_609025 := by exact prefixLift 609025
  have htrace : WordTrace (prefixWord ++ tailWord_609025) baseStart_609025 baseEnd_609025 := by
    simpa [prefixWord, tailWord_609025, baseEnd_609025] using wordTrace_append hprefix tailTrace_609025
  have hstable : (prefixWord ++ tailWord_609025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609025).length < 2 ^ (prefixWord ++ tailWord_609025).sum := by decide
  have hdescent : baseEnd_609025 < baseStart_609025 := by decide
  rcases family_descends (prefixWord ++ tailWord_609025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609052 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 2, 3, 2]
def baseStart_609052 : Nat := 118140960795 + 609052 * 2 ^ 59
def prefixEnd_609052 : Nat := 4983230072969 + 3 ^ 40 * 609052 * 2
def baseEnd_609052 : Nat := 312736419582256314949027

theorem tailTrace_609052 : CollatzResearch.WordTrace tailWord_609052 prefixEnd_609052 312736419582256314949027 := by
  unfold tailWord_609052
  simp only [CollatzResearch.WordTrace]
  refine ⟨11106975694758048322714705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14809300926344064430286273 11106975694758048322714705)
  ·
    refine ⟨8330231771068536242036029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11106975694758048322714705 8330231771068536242036029)
    ·
      refine ⟨3123836914150701090763511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8330231771068536242036029 3123836914150701090763511)
      ·
        refine ⟨4685755371226051636145267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3123836914150701090763511 4685755371226051636145267)
        ·
          refine ⟨7028633056839077454217901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4685755371226051636145267 7028633056839077454217901)
          ·
            refine ⟨2635737396314654045331713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7028633056839077454217901 2635737396314654045331713)
            ·
              refine ⟨1976803047235990533998785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2635737396314654045331713 1976803047235990533998785)
              ·
                refine ⟨1482602285426992900499089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1976803047235990533998785 1482602285426992900499089)
                ·
                  refine ⟨1111951714070244675374317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1482602285426992900499089 1111951714070244675374317)
                  ·
                    refine ⟨416981892776341753265369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1111951714070244675374317 416981892776341753265369)
                    ·
                      refine ⟨312736419582256314949027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 416981892776341753265369 312736419582256314949027)
                      ·
                        rfl

theorem cell23_609052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_609052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609052 prefixEnd_609052 := by exact prefixLift 609052
  have htrace : WordTrace (prefixWord ++ tailWord_609052) baseStart_609052 baseEnd_609052 := by
    simpa [prefixWord, tailWord_609052, baseEnd_609052] using wordTrace_append hprefix tailTrace_609052
  have hstable : (prefixWord ++ tailWord_609052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609052).length < 2 ^ (prefixWord ++ tailWord_609052).sum := by decide
  have hdescent : baseEnd_609052 < baseStart_609052 := by decide
  rcases family_descends (prefixWord ++ tailWord_609052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609053 : List Nat := [1, 4, 2, 4, 1, 2, 2, 2, 1, 4]
def baseStart_609053 : Nat := 118140960795 + 609053 * 2 ^ 59
def prefixEnd_609053 : Nat := 4983230072969 + 3 ^ 40 * 609053 * 2
def baseEnd_609053 : Nat := 104245644354303603678841

theorem tailTrace_609053 : CollatzResearch.WordTrace tailWord_609053 prefixEnd_609053 104245644354303603678841 := by
  unfold tailWord_609053
  simp only [CollatzResearch.WordTrace]
  refine ⟨22213987862512473816215813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14809325241674982544143875 22213987862512473816215813)
  ·
    refine ⟨4165122724221088840540465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22213987862512473816215813 4165122724221088840540465)
    ·
      refine ⟨3123842043165816630405349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4165122724221088840540465 3123842043165816630405349)
      ·
        refine ⟨585720383093590618201003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3123842043165816630405349 585720383093590618201003)
        ·
          refine ⟨878580574640385927301505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585720383093590618201003 878580574640385927301505)
          ·
            refine ⟨658935430980289445476129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 878580574640385927301505 658935430980289445476129)
            ·
              refine ⟨494201573235217084107097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658935430980289445476129 494201573235217084107097)
              ·
                refine ⟨370651179926412813080323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 494201573235217084107097 370651179926412813080323)
                ·
                  refine ⟨555976769889619219620485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370651179926412813080323 555976769889619219620485)
                  ·
                    refine ⟨104245644354303603678841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 555976769889619219620485 104245644354303603678841)
                    ·
                      rfl

theorem cell23_609053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_609053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609053 prefixEnd_609053 := by exact prefixLift 609053
  have htrace : WordTrace (prefixWord ++ tailWord_609053) baseStart_609053 baseEnd_609053 := by
    simpa [prefixWord, tailWord_609053, baseEnd_609053] using wordTrace_append hprefix tailTrace_609053
  have hstable : (prefixWord ++ tailWord_609053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609053).length < 2 ^ (prefixWord ++ tailWord_609053).sum := by decide
  have hdescent : baseEnd_609053 < baseStart_609053 := by decide
  rcases family_descends (prefixWord ++ tailWord_609053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609068 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 5]
def baseStart_609068 : Nat := 118140960795 + 609068 * 2 ^ 59
def prefixEnd_609068 : Nat := 4983230072969 + 3 ^ 40 * 609068 * 2
def baseEnd_609068 : Nat := 312744635272728252348953

theorem tailTrace_609068 : CollatzResearch.WordTrace tailWord_609068 prefixEnd_609068 312744635272728252348953 := by
  unfold tailWord_609068
  simp only [CollatzResearch.WordTrace]
  refine ⟨11107267478729065689005929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14809689971638754252007905 11107267478729065689005929)
  ·
    refine ⟨8330450609046799266754447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11107267478729065689005929 8330450609046799266754447)
    ·
      refine ⟨12495675913570198900131671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8330450609046799266754447 12495675913570198900131671)
      ·
        refine ⟨18743513870355298350197507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12495675913570198900131671 18743513870355298350197507)
        ·
          refine ⟨28115270805532947525296261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18743513870355298350197507 28115270805532947525296261)
          ·
            refine ⟨5271613276037427660993049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28115270805532947525296261 5271613276037427660993049)
            ·
              refine ⟨3953709957028070745744787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5271613276037427660993049 3953709957028070745744787)
              ·
                refine ⟨5930564935542106118617181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3953709957028070745744787 5930564935542106118617181)
                ·
                  refine ⟨2223961850828289794481443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5930564935542106118617181 2223961850828289794481443)
                  ·
                    refine ⟨3335942776242434691722165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2223961850828289794481443 3335942776242434691722165)
                    ·
                      refine ⟨312744635272728252348953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3335942776242434691722165 312744635272728252348953)
                      ·
                        rfl

theorem cell23_609068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_609068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609068 prefixEnd_609068 := by exact prefixLift 609068
  have htrace : WordTrace (prefixWord ++ tailWord_609068) baseStart_609068 baseEnd_609068 := by
    simpa [prefixWord, tailWord_609068, baseEnd_609068] using wordTrace_append hprefix tailTrace_609068
  have hstable : (prefixWord ++ tailWord_609068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609068).length < 2 ^ (prefixWord ++ tailWord_609068).sum := by decide
  have hdescent : baseEnd_609068 < baseStart_609068 := by decide
  rcases family_descends (prefixWord ++ tailWord_609068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609075 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 1, 6]
def baseStart_609075 : Nat := 118140960795 + 609075 * 2 ^ 59
def prefixEnd_609075 : Nat := 4983230072969 + 3 ^ 40 * 609075 * 2
def baseEnd_609075 : Nat := 104249409879103241653807

theorem tailTrace_609075 : CollatzResearch.WordTrace tailWord_609075 prefixEnd_609075 104249409879103241653807 := by
  unfold tailWord_609075
  simp only [CollatzResearch.WordTrace]
  refine ⟨22214790268432771573516679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14809860178955181049011119 22214790268432771573516679)
  ·
    refine ⟨33322185402649157360275019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22214790268432771573516679 33322185402649157360275019)
    ·
      refine ⟨49983278103973736040412529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33322185402649157360275019 49983278103973736040412529)
      ·
        refine ⟨37487458577980302030309397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49983278103973736040412529 37487458577980302030309397)
        ·
          refine ⟨1757224620842826657670753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37487458577980302030309397 1757224620842826657670753)
          ·
            refine ⟨1317918465632119993253065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1757224620842826657670753 1317918465632119993253065)
            ·
              refine ⟨988438849224089994939799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317918465632119993253065 988438849224089994939799)
              ·
                refine ⟨1482658273836134992409699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988438849224089994939799 1482658273836134992409699)
                ·
                  refine ⟨2223987410754202488614549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482658273836134992409699 2223987410754202488614549)
                  ·
                    refine ⟨104249409879103241653807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2223987410754202488614549 104249409879103241653807)
                    ·
                      rfl

theorem cell23_609075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 6].length) (baseStart_609075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609075 prefixEnd_609075 := by exact prefixLift 609075
  have htrace : WordTrace (prefixWord ++ tailWord_609075) baseStart_609075 baseEnd_609075 := by
    simpa [prefixWord, tailWord_609075, baseEnd_609075] using wordTrace_append hprefix tailTrace_609075
  have hstable : (prefixWord ++ tailWord_609075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609075).length < 2 ^ (prefixWord ++ tailWord_609075).sum := by decide
  have hdescent : baseEnd_609075 < baseStart_609075 := by decide
  rcases family_descends (prefixWord ++ tailWord_609075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609086 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 2, 3, 2]
def baseStart_609086 : Nat := 118140960795 + 609086 * 2 ^ 59
def prefixEnd_609086 : Nat := 4983230072969 + 3 ^ 40 * 609086 * 2
def baseEnd_609086 : Nat := 312753877924509181923871

theorem tailTrace_609086 : CollatzResearch.WordTrace tailWord_609086 prefixEnd_609086 312753877924509181923871 := by
  unfold tailWord_609086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2776898933924115056520889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14810127647595280301444741 2776898933924115056520889)
  ·
    refine ⟨2082674200443086292390667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2776898933924115056520889 2082674200443086292390667)
    ·
      refine ⟨3124011300664629438586001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2082674200443086292390667 3124011300664629438586001)
      ·
        refine ⟨2343008475498472078939501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3124011300664629438586001 2343008475498472078939501)
        ·
          refine ⟨878628178311927029602313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2343008475498472078939501 878628178311927029602313)
          ·
            refine ⟨658971133733945272201735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 878628178311927029602313 658971133733945272201735)
            ·
              refine ⟨988456700600917908302603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658971133733945272201735 988456700600917908302603)
              ·
                refine ⟨1482685050901376862453905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988456700600917908302603 1482685050901376862453905)
                ·
                  refine ⟨1112013788176032646840429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1482685050901376862453905 1112013788176032646840429)
                  ·
                    refine ⟨417005170566012242565161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1112013788176032646840429 417005170566012242565161)
                    ·
                      refine ⟨312753877924509181923871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 417005170566012242565161 312753877924509181923871)
                      ·
                        rfl

theorem cell23_609086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_609086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609086 prefixEnd_609086 := by exact prefixLift 609086
  have htrace : WordTrace (prefixWord ++ tailWord_609086) baseStart_609086 baseEnd_609086 := by
    simpa [prefixWord, tailWord_609086, baseEnd_609086] using wordTrace_append hprefix tailTrace_609086
  have hstable : (prefixWord ++ tailWord_609086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609086).length < 2 ^ (prefixWord ++ tailWord_609086).sum := by decide
  have hdescent : baseEnd_609086 < baseStart_609086 := by decide
  rcases family_descends (prefixWord ++ tailWord_609086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609116 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_609116 : Nat := 118140960795 + 609116 * 2 ^ 59
def prefixEnd_609116 : Nat := 4983230072969 + 3 ^ 40 * 609116 * 2
def baseEnd_609116 : Nat := 312769282344144064548733

theorem tailTrace_609116 : CollatzResearch.WordTrace tailWord_609116 prefixEnd_609116 312769282344144064548733 := by
  unfold tailWord_609116
  simp only [CollatzResearch.WordTrace]
  refine ⟨11108142830642117787879601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14810857107522823717172801 11108142830642117787879601)
  ·
    refine ⟨8331107122981588340909701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11108142830642117787879601 8331107122981588340909701)
    ·
      refine ⟨1562082585559047813920569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8331107122981588340909701 1562082585559047813920569)
      ·
        refine ⟨1171561939169285860440427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1562082585559047813920569 1171561939169285860440427)
        ·
          refine ⟨1757342908753928790660641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1171561939169285860440427 1757342908753928790660641)
          ·
            refine ⟨1318007181565446592995481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1757342908753928790660641 1318007181565446592995481)
            ·
              refine ⟨988505386174084944746611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1318007181565446592995481 988505386174084944746611)
              ·
                refine ⟨1482758079261127417119917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988505386174084944746611 1482758079261127417119917)
                ·
                  refine ⟨556034279722922781419969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1482758079261127417119917 556034279722922781419969)
                  ·
                    refine ⟨417025709792192086064977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 556034279722922781419969 417025709792192086064977)
                    ·
                      refine ⟨312769282344144064548733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 417025709792192086064977 312769282344144064548733)
                      ·
                        rfl

theorem cell23_609116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_609116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609116 prefixEnd_609116 := by exact prefixLift 609116
  have htrace : WordTrace (prefixWord ++ tailWord_609116) baseStart_609116 baseEnd_609116 := by
    simpa [prefixWord, tailWord_609116, baseEnd_609116] using wordTrace_append hprefix tailTrace_609116
  have hstable : (prefixWord ++ tailWord_609116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609116).length < 2 ^ (prefixWord ++ tailWord_609116).sum := by decide
  have hdescent : baseEnd_609116 < baseStart_609116 := by decide
  rcases family_descends (prefixWord ++ tailWord_609116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609148 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 1, 8]
def baseStart_609148 : Nat := 118140960795 + 609148 * 2 ^ 59
def prefixEnd_609148 : Nat := 4983230072969 + 3 ^ 40 * 609148 * 2
def baseEnd_609148 : Nat := 104261904575029313116195

theorem tailTrace_609148 : CollatzResearch.WordTrace tailWord_609148 prefixEnd_609148 104261904575029313116195 := by
  unfold tailWord_609148
  simp only [CollatzResearch.WordTrace]
  refine ⟨11108726398584152520462049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14811635198112203360616065 11108726398584152520462049)
  ·
    refine ⟨8331544798938114390346537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11108726398584152520462049 8331544798938114390346537)
    ·
      refine ⟨6248658599203585792759903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8331544798938114390346537 6248658599203585792759903)
      ·
        refine ⟨9372987898805378689139855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6248658599203585792759903 9372987898805378689139855)
        ·
          refine ⟨14059481848208068033709783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9372987898805378689139855 14059481848208068033709783)
          ·
            refine ⟨21089222772312102050564675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14059481848208068033709783 21089222772312102050564675)
            ·
              refine ⟨31633834158468153075847013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21089222772312102050564675 31633834158468153075847013)
              ·
                refine ⟨5931343904712778701721315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31633834158468153075847013 5931343904712778701721315)
                ·
                  refine ⟨8897015857069168052581973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5931343904712778701721315 8897015857069168052581973)
                  ·
                    refine ⟨104261904575029313116195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8897015857069168052581973 104261904575029313116195)
                    ·
                      rfl

theorem cell23_609148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_609148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609148 prefixEnd_609148 := by exact prefixLift 609148
  have htrace : WordTrace (prefixWord ++ tailWord_609148) baseStart_609148 baseEnd_609148 := by
    simpa [prefixWord, tailWord_609148, baseEnd_609148] using wordTrace_append hprefix tailTrace_609148
  have hstable : (prefixWord ++ tailWord_609148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609148).length < 2 ^ (prefixWord ++ tailWord_609148).sum := by decide
  have hdescent : baseEnd_609148 < baseStart_609148 := by decide
  rcases family_descends (prefixWord ++ tailWord_609148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609159 : List Nat := [1, 1, 4, 2, 3, 1, 2, 3, 1, 3, 2]
def baseStart_609159 : Nat := 118140960795 + 609159 * 2 ^ 59
def prefixEnd_609159 : Nat := 4983230072969 + 3 ^ 40 * 609159 * 2
def baseEnd_609159 : Nat := 312791362012287396311035

theorem tailTrace_609159 : CollatzResearch.WordTrace tailWord_609159 prefixEnd_609159 312791362012287396311035 := by
  unfold tailWord_609159
  simp only [CollatzResearch.WordTrace]
  refine ⟨22217854000128453919574531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14811902666752302613049687 22217854000128453919574531)
  ·
    refine ⟨33326781000192680879361797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22217854000128453919574531 33326781000192680879361797)
    ·
      refine ⟨6248771437536127664880337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33326781000192680879361797 6248771437536127664880337)
      ·
        refine ⟨4686578578152095748660253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6248771437536127664880337 4686578578152095748660253)
        ·
          refine ⟨1757466966807035905747595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4686578578152095748660253 1757466966807035905747595)
          ·
            refine ⟨2636200450210553858621393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757466966807035905747595 2636200450210553858621393)
            ·
              refine ⟨1977150337657915393966045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2636200450210553858621393 1977150337657915393966045)
              ·
                refine ⟨741431376621718272737267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1977150337657915393966045 741431376621718272737267)
                ·
                  refine ⟨1112147064932577409105901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 741431376621718272737267 1112147064932577409105901)
                  ·
                    refine ⟨417055149349716528414713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1112147064932577409105901 417055149349716528414713)
                    ·
                      refine ⟨312791362012287396311035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 417055149349716528414713 312791362012287396311035)
                      ·
                        rfl

theorem cell23_609159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_609159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609159 prefixEnd_609159 := by exact prefixLift 609159
  have htrace : WordTrace (prefixWord ++ tailWord_609159) baseStart_609159 baseEnd_609159 := by
    simpa [prefixWord, tailWord_609159, baseEnd_609159] using wordTrace_append hprefix tailTrace_609159
  have hstable : (prefixWord ++ tailWord_609159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609159).length < 2 ^ (prefixWord ++ tailWord_609159).sum := by decide
  have hdescent : baseEnd_609159 < baseStart_609159 := by decide
  rcases family_descends (prefixWord ++ tailWord_609159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609175 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 3]
def baseStart_609175 : Nat := 118140960795 + 609175 * 2 ^ 59
def prefixEnd_609175 : Nat := 4983230072969 + 3 ^ 40 * 609175 * 2
def baseEnd_609175 : Nat := 312799577702759333710961

theorem tailTrace_609175 : CollatzResearch.WordTrace tailWord_609175 prefixEnd_609175 312799577702759333710961 := by
  unfold tailWord_609175
  simp only [CollatzResearch.WordTrace]
  refine ⟨22218437568070488652156979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14812291712046992434771319 22218437568070488652156979)
  ·
    refine ⟨33327656352105732978235469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22218437568070488652156979 33327656352105732978235469)
    ·
      refine ⟨12497871132039649866838301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33327656352105732978235469 12497871132039649866838301)
      ·
        refine ⟨4686701674514868700064363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12497871132039649866838301 4686701674514868700064363)
        ·
          refine ⟨7030052511772303050096545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4686701674514868700064363 7030052511772303050096545)
          ·
            refine ⟨5272539383829227287572409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7030052511772303050096545 5272539383829227287572409)
            ·
              refine ⟨3954404537871920465679307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5272539383829227287572409 3954404537871920465679307)
              ·
                refine ⟨5931606806807880698518961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3954404537871920465679307 5931606806807880698518961)
                ·
                  refine ⟨4448705105105910523889221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5931606806807880698518961 4448705105105910523889221)
                  ·
                    refine ⟨834132207207358223229229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4448705105105910523889221 834132207207358223229229)
                    ·
                      refine ⟨312799577702759333710961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 834132207207358223229229 312799577702759333710961)
                      ·
                        rfl

theorem cell23_609175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_609175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609175 prefixEnd_609175 := by exact prefixLift 609175
  have htrace : WordTrace (prefixWord ++ tailWord_609175) baseStart_609175 baseEnd_609175 := by
    simpa [prefixWord, tailWord_609175, baseEnd_609175] using wordTrace_append hprefix tailTrace_609175
  have hstable : (prefixWord ++ tailWord_609175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609175).length < 2 ^ (prefixWord ++ tailWord_609175).sum := by decide
  have hdescent : baseEnd_609175 < baseStart_609175 := by decide
  rcases family_descends (prefixWord ++ tailWord_609175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609285 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 8]
def baseStart_609285 : Nat := 118140960795 + 609285 * 2 ^ 59
def prefixEnd_609285 : Nat := 4983230072969 + 3 ^ 40 * 609285 * 2
def baseEnd_609285 : Nat := 34761784508305989259495

theorem tailTrace_609285 : CollatzResearch.WordTrace tailWord_609285 prefixEnd_609285 34761784508305989259495 := by
  unfold tailWord_609285
  simp only [CollatzResearch.WordTrace]
  refine ⟨22222449597671977438661309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14814966398447984959107539 22222449597671977438661309)
  ·
    refine ⟨8333418599126991539497991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22222449597671977438661309 8333418599126991539497991)
    ·
      refine ⟨12500127898690487309246987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8333418599126991539497991 12500127898690487309246987)
      ·
        refine ⟨18750191848035730963870481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12500127898690487309246987 18750191848035730963870481)
        ·
          refine ⟨14062643886026798222902861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18750191848035730963870481 14062643886026798222902861)
          ·
            refine ⟨5273491457260049333588573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14062643886026798222902861 5273491457260049333588573)
            ·
              refine ⟨1977559296472518500095715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5273491457260049333588573 1977559296472518500095715)
              ·
                refine ⟨2966338944708777750143573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977559296472518500095715 2966338944708777750143573)
                ·
                  refine ⟨34761784508305989259495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2966338944708777750143573 34761784508305989259495)
                  ·
                    rfl

theorem cell23_609285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 8].length) (baseStart_609285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609285 prefixEnd_609285 := by exact prefixLift 609285
  have htrace : WordTrace (prefixWord ++ tailWord_609285) baseStart_609285 baseEnd_609285 := by
    simpa [prefixWord, tailWord_609285, baseEnd_609285] using wordTrace_append hprefix tailTrace_609285
  have hstable : (prefixWord ++ tailWord_609285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609285).length < 2 ^ (prefixWord ++ tailWord_609285).sum := by decide
  have hdescent : baseEnd_609285 < baseStart_609285 := by decide
  rcases family_descends (prefixWord ++ tailWord_609285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609352 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_609352 : Nat := 118140960795 + 609352 * 2 ^ 59
def prefixEnd_609352 : Nat := 4983230072969 + 3 ^ 40 * 609352 * 2
def baseEnd_609352 : Nat := 312890463778605141197647

theorem tailTrace_609352 : CollatzResearch.WordTrace tailWord_609352 prefixEnd_609352 312890463778605141197647 := by
  unfold tailWord_609352
  simp only [CollatzResearch.WordTrace]
  refine ⟨11112446644214623940675155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14816595525619498587566873 11112446644214623940675155)
  ·
    refine ⟨16668669966321935911012733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11112446644214623940675155 16668669966321935911012733)
    ·
      refine ⟨6250751237370725966629775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16668669966321935911012733 6250751237370725966629775)
      ·
        refine ⟨9376126856056088949944663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6250751237370725966629775 9376126856056088949944663)
        ·
          refine ⟨14064190284084133424916995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9376126856056088949944663 14064190284084133424916995)
          ·
            refine ⟨21096285426126200137375493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14064190284084133424916995 21096285426126200137375493)
            ·
              refine ⟨3955553517398662525757905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21096285426126200137375493 3955553517398662525757905)
              ·
                refine ⟨2966665138048996894318429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3955553517398662525757905 2966665138048996894318429)
                ·
                  refine ⟨1112499426768373835369411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2966665138048996894318429 1112499426768373835369411)
                  ·
                    refine ⟨1668749140152560753054117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1112499426768373835369411 1668749140152560753054117)
                    ·
                      refine ⟨312890463778605141197647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1668749140152560753054117 312890463778605141197647)
                      ·
                        rfl

theorem cell23_609352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_609352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609352 prefixEnd_609352 := by exact prefixLift 609352
  have htrace : WordTrace (prefixWord ++ tailWord_609352) baseStart_609352 baseEnd_609352 := by
    simpa [prefixWord, tailWord_609352, baseEnd_609352] using wordTrace_append hprefix tailTrace_609352
  have hstable : (prefixWord ++ tailWord_609352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609352).length < 2 ^ (prefixWord ++ tailWord_609352).sum := by decide
  have hdescent : baseEnd_609352 < baseStart_609352 := by decide
  rcases family_descends (prefixWord ++ tailWord_609352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609375 : List Nat := [1, 1, 2, 3, 1, 1, 3, 11]
def baseStart_609375 : Nat := 118140960795 + 609375 * 2 ^ 59
def prefixEnd_609375 : Nat := 4983230072969 + 3 ^ 40 * 609375 * 2
def baseEnd_609375 : Nat := 11588973104950316711483

theorem tailTrace_609375 : CollatzResearch.WordTrace tailWord_609375 prefixEnd_609375 11588973104950316711483 := by
  unfold tailWord_609375
  simp only [CollatzResearch.WordTrace]
  refine ⟨22225732167345922809437579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14817154778230615206291719 22225732167345922809437579)
  ·
    refine ⟨33338598251018884214156369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22225732167345922809437579 33338598251018884214156369)
    ·
      refine ⟨25003948688264163160617277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33338598251018884214156369 25003948688264163160617277)
      ·
        refine ⟨9376480758099061185231479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25003948688264163160617277 9376480758099061185231479)
        ·
          refine ⟨14064721137148591777847219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9376480758099061185231479 14064721137148591777847219)
          ·
            refine ⟨21097081705722887666770829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14064721137148591777847219 21097081705722887666770829)
            ·
              refine ⟨7911405639646082875039061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21097081705722887666770829 7911405639646082875039061)
              ·
                refine ⟨11588973104950316711483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 7911405639646082875039061 11588973104950316711483)
                ·
                  rfl

theorem cell23_609375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 11].length) (baseStart_609375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609375 prefixEnd_609375 := by exact prefixLift 609375
  have htrace : WordTrace (prefixWord ++ tailWord_609375) baseStart_609375 baseEnd_609375 := by
    simpa [prefixWord, tailWord_609375, baseEnd_609375] using wordTrace_append hprefix tailTrace_609375
  have hstable : (prefixWord ++ tailWord_609375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609375).length < 2 ^ (prefixWord ++ tailWord_609375).sum := by decide
  have hdescent : baseEnd_609375 < baseStart_609375 := by decide
  rcases family_descends (prefixWord ++ tailWord_609375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609389 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_609389 : Nat := 118140960795 + 609389 * 2 ^ 59
def prefixEnd_609389 : Nat := 4983230072969 + 3 ^ 40 * 609389 * 2
def baseEnd_609389 : Nat := 312909462562821496434977

theorem tailTrace_609389 : CollatzResearch.WordTrace tailWord_609389 prefixEnd_609389 312909462562821496434977 := by
  unfold tailWord_609389
  simp only [CollatzResearch.WordTrace]
  refine ⟨22226242789295203200447221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14817495192863468800298147 22226242789295203200447221)
  ·
    refine ⟨2083710261496425300041927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22226242789295203200447221 2083710261496425300041927)
    ·
      refine ⟨3125565392244637950062891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2083710261496425300041927 3125565392244637950062891)
      ·
        refine ⟨4688348088366956925094337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3125565392244637950062891 4688348088366956925094337)
        ·
          refine ⟨3516261066275217693820753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4688348088366956925094337 3516261066275217693820753)
          ·
            refine ⟨2637195799706413270365565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3516261066275217693820753 2637195799706413270365565)
            ·
              refine ⟨988948424889904976387087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2637195799706413270365565 988948424889904976387087)
              ·
                refine ⟨1483422637334857464580631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988948424889904976387087 1483422637334857464580631)
                ·
                  refine ⟨2225133956002286196870947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483422637334857464580631 2225133956002286196870947)
                  ·
                    refine ⟨3337700934003429295306421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2225133956002286196870947 3337700934003429295306421)
                    ·
                      refine ⟨312909462562821496434977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3337700934003429295306421 312909462562821496434977)
                      ·
                        rfl

theorem cell23_609389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_609389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609389 prefixEnd_609389 := by exact prefixLift 609389
  have htrace : WordTrace (prefixWord ++ tailWord_609389) baseStart_609389 baseEnd_609389 := by
    simpa [prefixWord, tailWord_609389, baseEnd_609389] using wordTrace_append hprefix tailTrace_609389
  have hstable : (prefixWord ++ tailWord_609389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609389).length < 2 ^ (prefixWord ++ tailWord_609389).sum := by decide
  have hdescent : baseEnd_609389 < baseStart_609389 := by decide
  rcases family_descends (prefixWord ++ tailWord_609389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609395 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 8]
def baseStart_609395 : Nat := 118140960795 + 609395 * 2 ^ 59
def prefixEnd_609395 : Nat := 4983230072969 + 3 ^ 40 * 609395 * 2
def baseEnd_609395 : Nat := 312912543446748472959949

theorem tailTrace_609395 : CollatzResearch.WordTrace tailWord_609395 prefixEnd_609395 312912543446748472959949 := by
  unfold tailWord_609395
  simp only [CollatzResearch.WordTrace]
  refine ⟨22226461627273466225165639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14817641084848977483443759 22226461627273466225165639)
  ·
    refine ⟨33339692440910199337748459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22226461627273466225165639 33339692440910199337748459)
    ·
      refine ⟨50009538661365299006622689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33339692440910199337748459 50009538661365299006622689)
      ·
        refine ⟨37507153996023974254967017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50009538661365299006622689 37507153996023974254967017)
        ·
          refine ⟨28130365497017980691225263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37507153996023974254967017 28130365497017980691225263)
          ·
            refine ⟨42195548245526971036837895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28130365497017980691225263 42195548245526971036837895)
            ·
              refine ⟨63293322368290456555256843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42195548245526971036837895 63293322368290456555256843)
              ·
                refine ⟨94939983552435684832885265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63293322368290456555256843 94939983552435684832885265)
                ·
                  refine ⟨71204987664326763624663949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94939983552435684832885265 71204987664326763624663949)
                  ·
                    refine ⟨26701870374122536359248981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71204987664326763624663949 26701870374122536359248981)
                    ·
                      refine ⟨312912543446748472959949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 26701870374122536359248981 312912543446748472959949)
                      ·
                        rfl

theorem cell23_609395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_609395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609395 prefixEnd_609395 := by exact prefixLift 609395
  have htrace : WordTrace (prefixWord ++ tailWord_609395) baseStart_609395 baseEnd_609395 := by
    simpa [prefixWord, tailWord_609395, baseEnd_609395] using wordTrace_append hprefix tailTrace_609395
  have hstable : (prefixWord ++ tailWord_609395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609395).length < 2 ^ (prefixWord ++ tailWord_609395).sum := by decide
  have hdescent : baseEnd_609395 < baseStart_609395 := by decide
  rcases family_descends (prefixWord ++ tailWord_609395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609409 : List Nat := [1, 2, 4, 2, 2, 3, 1, 8]
def baseStart_609409 : Nat := 118140960795 + 609409 * 2 ^ 59
def prefixEnd_609409 : Nat := 4983230072969 + 3 ^ 40 * 609409 * 2
def baseEnd_609409 : Nat := 11589619710218941414255

theorem tailTrace_609409 : CollatzResearch.WordTrace tailWord_609409 prefixEnd_609409 11589619710218941414255 := by
  unfold tailWord_609409
  simp only [CollatzResearch.WordTrace]
  refine ⟨22226972249222746616175281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14817981499481831077450187 22226972249222746616175281)
  ·
    refine ⟨16670229186917059962131461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22226972249222746616175281 16670229186917059962131461)
    ·
      refine ⟨3125667972546948742899649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16670229186917059962131461 3125667972546948742899649)
      ·
        refine ⟨2344250979410211557174737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3125667972546948742899649 2344250979410211557174737)
        ·
          refine ⟨1758188234557658667881053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2344250979410211557174737 1758188234557658667881053)
          ·
            refine ⟨659320587959122000455395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1758188234557658667881053 659320587959122000455395)
            ·
              refine ⟨988980881938683000683093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659320587959122000455395 988980881938683000683093)
              ·
                refine ⟨11589619710218941414255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 988980881938683000683093 11589619710218941414255)
                ·
                  rfl

theorem cell23_609409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 8].length) (baseStart_609409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609409 prefixEnd_609409 := by exact prefixLift 609409
  have htrace : WordTrace (prefixWord ++ tailWord_609409) baseStart_609409 baseEnd_609409 := by
    simpa [prefixWord, tailWord_609409, baseEnd_609409] using wordTrace_append hprefix tailTrace_609409
  have hstable : (prefixWord ++ tailWord_609409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609409).length < 2 ^ (prefixWord ++ tailWord_609409).sum := by decide
  have hdescent : baseEnd_609409 < baseStart_609409 := by decide
  rcases family_descends (prefixWord ++ tailWord_609409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609416 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 1, 2, 4]
def baseStart_609416 : Nat := 118140960795 + 609416 * 2 ^ 59
def prefixEnd_609416 : Nat := 4983230072969 + 3 ^ 40 * 609416 * 2
def baseEnd_609416 : Nat := 312923326540492890797353

theorem tailTrace_609416 : CollatzResearch.WordTrace tailWord_609416 prefixEnd_609416 312923326540492890797353 := by
  unfold tailWord_609416
  simp only [CollatzResearch.WordTrace]
  refine ⟨11113613780098693405840051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14818151706798257874453401 11113613780098693405840051)
  ·
    refine ⟨16670420670148040108760077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11113613780098693405840051 16670420670148040108760077)
    ·
      refine ⟨6251407751305515040785029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16670420670148040108760077 6251407751305515040785029)
      ·
        refine ⟨1172138953369784070147193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6251407751305515040785029 1172138953369784070147193)
        ·
          refine ⟨879104215027338052610395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1172138953369784070147193 879104215027338052610395)
          ·
            refine ⟨1318656322541007078915593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879104215027338052610395 1318656322541007078915593)
            ·
              refine ⟨988992241905755309186695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1318656322541007078915593 988992241905755309186695)
              ·
                refine ⟨1483488362858632963780043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988992241905755309186695 1483488362858632963780043)
                ·
                  refine ⟨2225232544287949445670065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483488362858632963780043 2225232544287949445670065)
                  ·
                    refine ⟨1668924408215962084252549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2225232544287949445670065 1668924408215962084252549)
                    ·
                      refine ⟨312923326540492890797353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1668924408215962084252549 312923326540492890797353)
                      ·
                        rfl

theorem cell23_609416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_609416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609416 prefixEnd_609416 := by exact prefixLift 609416
  have htrace : WordTrace (prefixWord ++ tailWord_609416) baseStart_609416 baseEnd_609416 := by
    simpa [prefixWord, tailWord_609416, baseEnd_609416] using wordTrace_append hprefix tailTrace_609416
  have hstable : (prefixWord ++ tailWord_609416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609416).length < 2 ^ (prefixWord ++ tailWord_609416).sum := by decide
  have hdescent : baseEnd_609416 < baseStart_609416 := by decide
  rcases family_descends (prefixWord ++ tailWord_609416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609453 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_609453 : Nat := 118140960795 + 609453 * 2 ^ 59
def prefixEnd_609453 : Nat := 4983230072969 + 3 ^ 40 * 609453 * 2
def baseEnd_609453 : Nat := 312942325324709246034683

theorem tailTrace_609453 : CollatzResearch.WordTrace tailWord_609453 prefixEnd_609453 312942325324709246034683 := by
  unfold tailWord_609453
  simp only [CollatzResearch.WordTrace]
  refine ⟨22228577061063342130777013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14819051374042228087184675 22228577061063342130777013)
  ·
    refine ⟨2083929099474688324760345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22228577061063342130777013 2083929099474688324760345)
    ·
      refine ⟨1562946824606016243570259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2083929099474688324760345 1562946824606016243570259)
      ·
        refine ⟨2344420236909024365355389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1562946824606016243570259 2344420236909024365355389)
        ·
          refine ⟨879157588840884137008271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2344420236909024365355389 879157588840884137008271)
          ·
            refine ⟨1318736383261326205512407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879157588840884137008271 1318736383261326205512407)
            ·
              refine ⟨1978104574891989308268611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318736383261326205512407 1978104574891989308268611)
              ·
                refine ⟨2967156862337983962402917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978104574891989308268611 2967156862337983962402917)
                ·
                  refine ⟨556341911688371992950547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2967156862337983962402917 556341911688371992950547)
                  ·
                    refine ⟨834512867532557989425821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 556341911688371992950547 834512867532557989425821)
                    ·
                      refine ⟨312942325324709246034683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 834512867532557989425821 312942325324709246034683)
                      ·
                        rfl

theorem cell23_609453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_609453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609453 prefixEnd_609453 := by exact prefixLift 609453
  have htrace : WordTrace (prefixWord ++ tailWord_609453) baseStart_609453 baseEnd_609453 := by
    simpa [prefixWord, tailWord_609453, baseEnd_609453] using wordTrace_append hprefix tailTrace_609453
  have hstable : (prefixWord ++ tailWord_609453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609453).length < 2 ^ (prefixWord ++ tailWord_609453).sum := by decide
  have hdescent : baseEnd_609453 < baseStart_609453 := by decide
  rcases family_descends (prefixWord ++ tailWord_609453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609459 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 3, 4, 2]
def baseStart_609459 : Nat := 118140960795 + 609459 * 2 ^ 59
def prefixEnd_609459 : Nat := 4983230072969 + 3 ^ 40 * 609459 * 2
def baseEnd_609459 : Nat := 312945406208636222559655

theorem tailTrace_609459 : CollatzResearch.WordTrace tailWord_609459 prefixEnd_609459 312945406208636222559655 := by
  unfold tailWord_609459
  simp only [CollatzResearch.WordTrace]
  refine ⟨22228795899041605155495431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14819197266027736770330287 22228795899041605155495431)
  ·
    refine ⟨33343193848562407733243147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22228795899041605155495431 33343193848562407733243147)
    ·
      refine ⟨50014790772843611599864721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33343193848562407733243147 50014790772843611599864721)
      ·
        refine ⟨37511093079632708699898541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50014790772843611599864721 37511093079632708699898541)
        ·
          refine ⟨14066659904862265762461953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37511093079632708699898541 14066659904862265762461953)
          ·
            refine ⟨10549994928646699321846465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14066659904862265762461953 10549994928646699321846465)
            ·
              refine ⟨7912496196485024491384849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10549994928646699321846465 7912496196485024491384849)
              ·
                refine ⟨5934372147363768368538637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7912496196485024491384849 5934372147363768368538637)
                ·
                  refine ⟨2225389555261413138201989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5934372147363768368538637 2225389555261413138201989)
                  ·
                    refine ⟨417260541611514963412873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2225389555261413138201989 417260541611514963412873)
                    ·
                      refine ⟨312945406208636222559655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 417260541611514963412873 312945406208636222559655)
                      ·
                        rfl

theorem cell23_609459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 4, 2].length) (baseStart_609459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609459 prefixEnd_609459 := by exact prefixLift 609459
  have htrace : WordTrace (prefixWord ++ tailWord_609459) baseStart_609459 baseEnd_609459 := by
    simpa [prefixWord, tailWord_609459, baseEnd_609459] using wordTrace_append hprefix tailTrace_609459
  have hstable : (prefixWord ++ tailWord_609459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609459).length < 2 ^ (prefixWord ++ tailWord_609459).sum := by decide
  have hdescent : baseEnd_609459 < baseStart_609459 := by decide
  rcases family_descends (prefixWord ++ tailWord_609459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609470 : List Nat := [4, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3]
def baseStart_609470 : Nat := 118140960795 + 609470 * 2 ^ 59
def prefixEnd_609470 : Nat := 4983230072969 + 3 ^ 40 * 609470 * 2
def baseEnd_609470 : Nat := 312951054495835679522105

theorem tailTrace_609470 : CollatzResearch.WordTrace tailWord_609470 prefixEnd_609470 312951054495835679522105 := by
  unfold tailWord_609470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2778649637750219254268233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14819464734667836022763909 2778649637750219254268233)
  ·
    refine ⟨2083987228312664440701175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2778649637750219254268233 2083987228312664440701175)
    ·
      refine ⟨3125980842468996661051763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2083987228312664440701175 3125980842468996661051763)
      ·
        refine ⟨4688971263703494991577645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3125980842468996661051763 4688971263703494991577645)
        ·
          refine ⟨1758364223888810621841617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4688971263703494991577645 1758364223888810621841617)
          ·
            refine ⟨1318773167916607966381213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1758364223888810621841617 1318773167916607966381213)
            ·
              refine ⟨494539937968727987392955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1318773167916607966381213 494539937968727987392955)
              ·
                refine ⟨741809906953091981089433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494539937968727987392955 741809906953091981089433)
                ·
                  refine ⟨556357430214818985817075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 741809906953091981089433 556357430214818985817075)
                  ·
                    refine ⟨834536145322228478725613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 556357430214818985817075 834536145322228478725613)
                    ·
                      refine ⟨312951054495835679522105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 834536145322228478725613 312951054495835679522105)
                      ·
                        rfl

theorem cell23_609470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_609470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609470 prefixEnd_609470 := by exact prefixLift 609470
  have htrace : WordTrace (prefixWord ++ tailWord_609470) baseStart_609470 baseEnd_609470 := by
    simpa [prefixWord, tailWord_609470, baseEnd_609470] using wordTrace_append hprefix tailTrace_609470
  have hstable : (prefixWord ++ tailWord_609470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609470).length < 2 ^ (prefixWord ++ tailWord_609470).sum := by decide
  have hdescent : baseEnd_609470 < baseStart_609470 := by decide
  rcases family_descends (prefixWord ++ tailWord_609470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609493 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 4, 2, 2]
def baseStart_609493 : Nat := 118140960795 + 609493 * 2 ^ 59
def prefixEnd_609493 : Nat := 4983230072969 + 3 ^ 40 * 609493 * 2
def baseEnd_609493 : Nat := 312962864550889089534499

theorem tailTrace_609493 : CollatzResearch.WordTrace tailWord_609493 prefixEnd_609493 312962864550889089534499 := by
  unfold tailWord_609493
  simp only [CollatzResearch.WordTrace]
  refine ⟨22230035980918428962233133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14820023987278952641488755 22230035980918428962233133)
  ·
    refine ⟨8336263492844410860837425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22230035980918428962233133 8336263492844410860837425)
    ·
      refine ⟨6252197619633308145628069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8336263492844410860837425 6252197619633308145628069)
      ·
        refine ⟨1172287053681245277305263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6252197619633308145628069 1172287053681245277305263)
        ·
          refine ⟨1758430580521867915957895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1172287053681245277305263 1758430580521867915957895)
          ·
            refine ⟨2637645870782801873936843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1758430580521867915957895 2637645870782801873936843)
            ·
              refine ⟨3956468806174202810905265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2637645870782801873936843 3956468806174202810905265)
              ·
                refine ⟨2967351604630652108178949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3956468806174202810905265 2967351604630652108178949)
                ·
                  refine ⟨556378425868247270283553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2967351604630652108178949 556378425868247270283553)
                  ·
                    refine ⟨417283819401185452712665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 556378425868247270283553 417283819401185452712665)
                    ·
                      refine ⟨312962864550889089534499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 417283819401185452712665 312962864550889089534499)
                      ·
                        rfl

theorem cell23_609493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_609493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609493 prefixEnd_609493 := by exact prefixLift 609493
  have htrace : WordTrace (prefixWord ++ tailWord_609493) baseStart_609493 baseEnd_609493 := by
    simpa [prefixWord, tailWord_609493, baseEnd_609493] using wordTrace_append hprefix tailTrace_609493
  have hstable : (prefixWord ++ tailWord_609493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609493).length < 2 ^ (prefixWord ++ tailWord_609493).sum := by decide
  have hdescent : baseEnd_609493 < baseStart_609493 := by decide
  rcases family_descends (prefixWord ++ tailWord_609493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609569 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 3, 4, 3]
def baseStart_609569 : Nat := 118140960795 + 609569 * 2 ^ 59
def prefixEnd_609569 : Nat := 4983230072969 + 3 ^ 40 * 609569 * 2
def baseEnd_609569 : Nat := 313001889080630792184149

theorem tailTrace_609569 : CollatzResearch.WordTrace tailWord_609569 prefixEnd_609569 313001889080630792184149 := by
  unfold tailWord_609569
  simp only [CollatzResearch.WordTrace]
  refine ⟨22232807928643093941999761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14821871952428729294666507 22232807928643093941999761)
  ·
    refine ⟨16674605946482320456499821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22232807928643093941999761 16674605946482320456499821)
    ·
      refine ⟨6252977229930870171187433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16674605946482320456499821 6252977229930870171187433)
      ·
        refine ⟨4689732922448152628390575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6252977229930870171187433 4689732922448152628390575)
        ·
          refine ⟨7034599383672228942585863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4689732922448152628390575 7034599383672228942585863)
          ·
            refine ⟨10551899075508343413878795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7034599383672228942585863 10551899075508343413878795)
            ·
              refine ⟨15827848613262515120818193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10551899075508343413878795 15827848613262515120818193)
              ·
                refine ⟨11870886459946886340613645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15827848613262515120818193 11870886459946886340613645)
                ·
                  refine ⟨4451582422480082377730117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11870886459946886340613645 4451582422480082377730117)
                  ·
                    refine ⟨834671704215015445824397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4451582422480082377730117 834671704215015445824397)
                    ·
                      refine ⟨313001889080630792184149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 834671704215015445824397 313001889080630792184149)
                      ·
                        rfl

theorem cell23_609569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_609569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609569 prefixEnd_609569 := by exact prefixLift 609569
  have htrace : WordTrace (prefixWord ++ tailWord_609569) baseStart_609569 baseEnd_609569 := by
    simpa [prefixWord, tailWord_609569, baseEnd_609569] using wordTrace_append hprefix tailTrace_609569
  have hstable : (prefixWord ++ tailWord_609569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609569).length < 2 ^ (prefixWord ++ tailWord_609569).sum := by decide
  have hdescent : baseEnd_609569 < baseStart_609569 := by decide
  rcases family_descends (prefixWord ++ tailWord_609569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609593 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 3, 4]
def baseStart_609593 : Nat := 118140960795 + 609593 * 2 ^ 59
def prefixEnd_609593 : Nat := 4983230072969 + 3 ^ 40 * 609593 * 2
def baseEnd_609593 : Nat := 104338070872112899428013

theorem tailTrace_609593 : CollatzResearch.WordTrace tailWord_609593 prefixEnd_609593 104338070872112899428013 := by
  unfold tailWord_609593
  simp only [CollatzResearch.WordTrace]
  refine ⟨22233683280556146040873433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14822455520370764027248955 22233683280556146040873433)
  ·
    refine ⟨16675262460417109530655075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22233683280556146040873433 16675262460417109530655075)
    ·
      refine ⟨25012893690625664295982613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16675262460417109530655075 25012893690625664295982613)
      ·
        refine ⟨1172479391748078013874185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25012893690625664295982613 1172479391748078013874185)
        ·
          refine ⟨879359543811058510405639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1172479391748078013874185 879359543811058510405639)
          ·
            refine ⟨1319039315716587765608459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879359543811058510405639 1319039315716587765608459)
            ·
              refine ⟨1978558973574881648412689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319039315716587765608459 1978558973574881648412689)
              ·
                refine ⟨1483919230181161236309517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1978558973574881648412689 1483919230181161236309517)
                ·
                  refine ⟨556469711317935463616069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1483919230181161236309517 556469711317935463616069)
                  ·
                    refine ⟨104338070872112899428013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 556469711317935463616069 104338070872112899428013)
                    ·
                      rfl

theorem cell23_609593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 4].length) (baseStart_609593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609593 prefixEnd_609593 := by exact prefixLift 609593
  have htrace : WordTrace (prefixWord ++ tailWord_609593) baseStart_609593 baseEnd_609593 := by
    simpa [prefixWord, tailWord_609593, baseEnd_609593] using wordTrace_append hprefix tailTrace_609593
  have hstable : (prefixWord ++ tailWord_609593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609593).length < 2 ^ (prefixWord ++ tailWord_609593).sum := by decide
  have hdescent : baseEnd_609593 < baseStart_609593 := by decide
  rcases family_descends (prefixWord ++ tailWord_609593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609616 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 5, 1, 3]
def baseStart_609616 : Nat := 118140960795 + 609616 * 2 ^ 59
def prefixEnd_609616 : Nat := 4983230072969 + 3 ^ 40 * 609616 * 2
def baseEnd_609616 : Nat := 313026022671392108296433

theorem tailTrace_609616 : CollatzResearch.WordTrace tailWord_609616 prefixEnd_609616 313026022671392108296433 := by
  unfold tailWord_609616
  simp only [CollatzResearch.WordTrace]
  refine ⟨11117261079736410484480351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14823014772981880645973801 11117261079736410484480351)
  ·
    refine ⟨16675891619604615726720527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11117261079736410484480351 16675891619604615726720527)
    ·
      refine ⟨25013837429406923590080791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16675891619604615726720527 25013837429406923590080791)
      ·
        refine ⟨37520756144110385385121187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25013837429406923590080791 37520756144110385385121187)
        ·
          refine ⟨56281134216165578077681781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37520756144110385385121187 56281134216165578077681781)
          ·
            refine ⟨5276356332765522944782667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56281134216165578077681781 5276356332765522944782667)
            ·
              refine ⟨7914534499148284417174001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5276356332765522944782667 7914534499148284417174001)
              ·
                refine ⟨5935900874361213312880501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7914534499148284417174001 5935900874361213312880501)
                ·
                  refine ⟨556490706971363748082547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5935900874361213312880501 556490706971363748082547)
                  ·
                    refine ⟨834736060457045622123821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 556490706971363748082547 834736060457045622123821)
                    ·
                      refine ⟨313026022671392108296433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 834736060457045622123821 313026022671392108296433)
                      ·
                        rfl

theorem cell23_609616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 5, 1, 3].length) (baseStart_609616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609616 prefixEnd_609616 := by exact prefixLift 609616
  have htrace : WordTrace (prefixWord ++ tailWord_609616) baseStart_609616 baseEnd_609616 := by
    simpa [prefixWord, tailWord_609616, baseEnd_609616] using wordTrace_append hprefix tailTrace_609616
  have hstable : (prefixWord ++ tailWord_609616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609616).length < 2 ^ (prefixWord ++ tailWord_609616).sum := by decide
  have hdescent : baseEnd_609616 < baseStart_609616 := by decide
  rcases family_descends (prefixWord ++ tailWord_609616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609659 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 5]
def baseStart_609659 : Nat := 118140960795 + 609659 * 2 ^ 59
def prefixEnd_609659 : Nat := 4983230072969 + 3 ^ 40 * 609659 * 2
def baseEnd_609659 : Nat := 313048102339535440058735

theorem tailTrace_609659 : CollatzResearch.WordTrace tailWord_609659 prefixEnd_609659 313048102339535440058735 := by
  unfold tailWord_609659
  simp only [CollatzResearch.WordTrace]
  refine ⟨22236090498317039312776031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14824060332211359541850687 22236090498317039312776031)
  ·
    refine ⟨33354135747475558969164047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22236090498317039312776031 33354135747475558969164047)
    ·
      refine ⟨50031203621213338453746071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33354135747475558969164047 50031203621213338453746071)
      ·
        refine ⟨75046805431820007680619107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50031203621213338453746071 75046805431820007680619107)
        ·
          refine ⟨112570208147730011520928661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75046805431820007680619107 112570208147730011520928661)
          ·
            refine ⟨5276728506924844290043531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 112570208147730011520928661 5276728506924844290043531)
            ·
              refine ⟨7915092760387266435065297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5276728506924844290043531 7915092760387266435065297)
              ·
                refine ⟨5936319570290449826298973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7915092760387266435065297 5936319570290449826298973)
                ·
                  refine ⟨2226119838858918684862115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5936319570290449826298973 2226119838858918684862115)
                  ·
                    refine ⟨3339179758288378027293173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2226119838858918684862115 3339179758288378027293173)
                    ·
                      refine ⟨313048102339535440058735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3339179758288378027293173 313048102339535440058735)
                      ·
                        rfl

theorem cell23_609659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 5].length) (baseStart_609659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_609659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_609659 prefixEnd_609659 := by exact prefixLift 609659
  have htrace : WordTrace (prefixWord ++ tailWord_609659) baseStart_609659 baseEnd_609659 := by
    simpa [prefixWord, tailWord_609659, baseEnd_609659] using wordTrace_append hprefix tailTrace_609659
  have hstable : (prefixWord ++ tailWord_609659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609659).length < 2 ^ (prefixWord ++ tailWord_609659).sum := by decide
  have hdescent : baseEnd_609659 < baseStart_609659 := by decide
  rcases family_descends (prefixWord ++ tailWord_609659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
