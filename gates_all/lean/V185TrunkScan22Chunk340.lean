import V185TrunkScan22Chunk339

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3032505 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 2, 4]
def baseStart_3032505 : Nat := 118140960795 + 3032505 * 2 ^ 59
def prefixEnd_3032505 : Nat := 4983230072969 + 3 ^ 40 * 3032505 * 2
def baseEnd_3032505 : Nat := 1038088434775175362627513

theorem tailTrace_3032505 : CollatzResearch.WordTrace tailWord_3032505 prefixEnd_3032505 1038088434775175362627513 := by
  unfold tailWord_3032505
  simp only [CollatzResearch.WordTrace]
  refine ⟨110604543878759770466138969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73736362585839846977425979 110604543878759770466138969)
  ·
    refine ⟨82953407909069827849604227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110604543878759770466138969 82953407909069827849604227)
    ·
      refine ⟨124430111863604741774406341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82953407909069827849604227 124430111863604741774406341)
      ·
        refine ⟨23330645974425889082701189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124430111863604741774406341 23330645974425889082701189)
        ·
          refine ⟨4374496120204854203006473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23330645974425889082701189 4374496120204854203006473)
          ·
            refine ⟨3280872090153640652254855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4374496120204854203006473 3280872090153640652254855)
            ·
              refine ⟨4921308135230460978382283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3280872090153640652254855 4921308135230460978382283)
              ·
                refine ⟨7381962202845691467573425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4921308135230460978382283 7381962202845691467573425)
                ·
                  refine ⟨5536471652134268600680069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7381962202845691467573425 5536471652134268600680069)
                  ·
                    refine ⟨1038088434775175362627513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5536471652134268600680069 1038088434775175362627513)
                    ·
                      rfl

theorem cell22_3032505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 4].length) (baseStart_3032505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032505 prefixEnd_3032505 := by exact prefixLift 3032505
  have htrace : WordTrace (prefixWord ++ tailWord_3032505) baseStart_3032505 baseEnd_3032505 := by
    simpa [prefixWord, tailWord_3032505, baseEnd_3032505] using wordTrace_append hprefix tailTrace_3032505
  have hstable : (prefixWord ++ tailWord_3032505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032505).length < 2 ^ (prefixWord ++ tailWord_3032505).sum := by decide
  have hdescent : baseEnd_3032505 < baseStart_3032505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032713 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 5, 4]
def baseStart_3032713 : Nat := 118140960795 + 3032713 * 2 ^ 59
def prefixEnd_3032713 : Nat := 4983230072969 + 3 ^ 40 * 3032713 * 2
def baseEnd_3032713 : Nat := 1038159637425932153426875

theorem tailTrace_3032713 : CollatzResearch.WordTrace tailWord_3032713 prefixEnd_3032713 1038159637425932153426875 := by
  unfold tailWord_3032713
  simp only [CollatzResearch.WordTrace]
  refine ⟨110612130262006221989710793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73741420174670814659807195 110612130262006221989710793)
  ·
    refine ⟨82959097696504666492283095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110612130262006221989710793 82959097696504666492283095)
    ·
      refine ⟨124438646544756999738424643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82959097696504666492283095 124438646544756999738424643)
      ·
        refine ⟨186657969817135499607636965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124438646544756999738424643 186657969817135499607636965)
        ·
          refine ⟨34998369340712906176431931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186657969817135499607636965 34998369340712906176431931)
          ·
            refine ⟨52497554011069359264647897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34998369340712906176431931 52497554011069359264647897)
            ·
              refine ⟨39373165508302019448485923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52497554011069359264647897 39373165508302019448485923)
              ·
                refine ⟨59059748262453029172728885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39373165508302019448485923 59059748262453029172728885)
                ·
                  refine ⟨5536851399604971484943333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59059748262453029172728885 5536851399604971484943333)
                  ·
                    refine ⟨1038159637425932153426875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5536851399604971484943333 1038159637425932153426875)
                    ·
                      rfl

theorem cell22_3032713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_3032713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032713 prefixEnd_3032713 := by exact prefixLift 3032713
  have htrace : WordTrace (prefixWord ++ tailWord_3032713) baseStart_3032713 baseEnd_3032713 := by
    simpa [prefixWord, tailWord_3032713, baseEnd_3032713] using wordTrace_append hprefix tailTrace_3032713
  have hstable : (prefixWord ++ tailWord_3032713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032713).length < 2 ^ (prefixWord ++ tailWord_3032713).sum := by decide
  have hdescent : baseEnd_3032713 < baseStart_3032713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032738 : List Nat := [3, 3, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_3032738 : Nat := 118140960795 + 3032738 * 2 ^ 59
def prefixEnd_3032738 : Nat := 4983230072969 + 3 ^ 40 * 3032738 * 2
def baseEnd_3032738 : Nat := 1038168195436840421551799

theorem tailTrace_3032738 : CollatzResearch.WordTrace tailWord_3032738 prefixEnd_3032738 1038168195436840421551799 := by
  unfold tailWord_3032738
  simp only [CollatzResearch.WordTrace]
  refine ⟨27653260521728912814842717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73742028057943767506247245 27653260521728912814842717)
  ·
    refine ⟨10369972695648342305566019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27653260521728912814842717 10369972695648342305566019)
    ·
      refine ⟨15554959043472513458349029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10369972695648342305566019 15554959043472513458349029)
      ·
        refine ⟨2916554820651096273440443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15554959043472513458349029 2916554820651096273440443)
        ·
          refine ⟨4374832230976644410160665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2916554820651096273440443 4374832230976644410160665)
          ·
            refine ⟨3281124173232483307620499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4374832230976644410160665 3281124173232483307620499)
            ·
              refine ⟨4921686259848724961430749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3281124173232483307620499 4921686259848724961430749)
              ·
                refine ⟨1845632347443271860536531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4921686259848724961430749 1845632347443271860536531)
                ·
                  refine ⟨2768448521164907790804797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845632347443271860536531 2768448521164907790804797)
                  ·
                    refine ⟨1038168195436840421551799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2768448521164907790804797 1038168195436840421551799)
                    ·
                      rfl

theorem cell22_3032738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_3032738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032738 prefixEnd_3032738 := by exact prefixLift 3032738
  have htrace : WordTrace (prefixWord ++ tailWord_3032738) baseStart_3032738 baseEnd_3032738 := by
    simpa [prefixWord, tailWord_3032738, baseEnd_3032738] using wordTrace_append hprefix tailTrace_3032738
  have hstable : (prefixWord ++ tailWord_3032738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032738).length < 2 ^ (prefixWord ++ tailWord_3032738).sum := by decide
  have hdescent : baseEnd_3032738 < baseStart_3032738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032781 : List Nat := [1, 6, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3032781 : Nat := 118140960795 + 3032781 * 2 ^ 59
def prefixEnd_3032781 : Nat := 4983230072969 + 3 ^ 40 * 3032781 * 2
def baseEnd_3032781 : Nat := 1038182915215602642726667

theorem tailTrace_3032781 : CollatzResearch.WordTrace tailWord_3032781 prefixEnd_3032781 1038182915215602642726667 := by
  unfold tailWord_3032781
  simp only [CollatzResearch.WordTrace]
  refine ⟨110614610425759869603186197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73743073617173246402124131 110614610425759869603186197)
  ·
    refine ⟨5185059863707493887649353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110614610425759869603186197 5185059863707493887649353)
    ·
      refine ⟨3888794897780620415737015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5185059863707493887649353 3888794897780620415737015)
      ·
        refine ⟨5833192346670930623605523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3888794897780620415737015 5833192346670930623605523)
        ·
          refine ⟨8749788520006395935408285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5833192346670930623605523 8749788520006395935408285)
          ·
            refine ⟨3281170695002398475778107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8749788520006395935408285 3281170695002398475778107)
            ·
              refine ⟨4921756042503597713667161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3281170695002398475778107 4921756042503597713667161)
              ·
                refine ⟨3691317031877698285250371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4921756042503597713667161 3691317031877698285250371)
                ·
                  refine ⟨5536975547816547427875557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3691317031877698285250371 5536975547816547427875557)
                  ·
                    refine ⟨1038182915215602642726667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5536975547816547427875557 1038182915215602642726667)
                    ·
                      rfl

theorem cell22_3032781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3032781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032781 prefixEnd_3032781 := by exact prefixLift 3032781
  have htrace : WordTrace (prefixWord ++ tailWord_3032781) baseStart_3032781 baseEnd_3032781 := by
    simpa [prefixWord, tailWord_3032781, baseEnd_3032781] using wordTrace_append hprefix tailTrace_3032781
  have hstable : (prefixWord ++ tailWord_3032781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032781).length < 2 ^ (prefixWord ++ tailWord_3032781).sum := by decide
  have hdescent : baseEnd_3032781 < baseStart_3032781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032807 : List Nat := [1, 1, 5, 4, 2, 9]
def baseStart_3032807 : Nat := 118140960795 + 3032807 * 2 ^ 59
def prefixEnd_3032807 : Nat := 4983230072969 + 3 ^ 40 * 3032807 * 2
def baseEnd_3032807 : Nat := 12817182907987002982427

theorem tailTrace_3032807 : CollatzResearch.WordTrace tailWord_3032807 prefixEnd_3032807 12817182907987002982427 := by
  unfold tailWord_3032807
  simp only [CollatzResearch.WordTrace]
  refine ⟨110615558723665676043632675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73743705815777117362421783 110615558723665676043632675)
  ·
    refine ⟨165923338085498514065449013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110615558723665676043632675 165923338085498514065449013)
    ·
      refine ⟨15555312945515485693635845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165923338085498514065449013 15555312945515485693635845)
      ·
        refine ⟨2916621177284153567556721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15555312945515485693635845 2916621177284153567556721)
        ·
          refine ⟨2187465882963115175667541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2916621177284153567556721 2187465882963115175667541)
          ·
            refine ⟨12817182907987002982427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2187465882963115175667541 12817182907987002982427)
            ·
              rfl

theorem cell22_3032807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 9].length) (baseStart_3032807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032807 prefixEnd_3032807 := by exact prefixLift 3032807
  have htrace : WordTrace (prefixWord ++ tailWord_3032807) baseStart_3032807 baseEnd_3032807 := by
    simpa [prefixWord, tailWord_3032807, baseEnd_3032807] using wordTrace_append hprefix tailTrace_3032807
  have hstable : (prefixWord ++ tailWord_3032807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032807).length < 2 ^ (prefixWord ++ tailWord_3032807).sum := by decide
  have hdescent : baseEnd_3032807 < baseStart_3032807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032835 : List Nat := [1, 1, 1, 3, 2, 2, 4, 3, 5]
def baseStart_3032835 : Nat := 118140960795 + 3032835 * 2 ^ 59
def prefixEnd_3032835 : Nat := 4983230072969 + 3 ^ 40 * 3032835 * 2
def baseEnd_3032835 : Nat := 346067133506388167292167

theorem tailTrace_3032835 : CollatzResearch.WordTrace tailWord_3032835 prefixEnd_3032835 346067133506388167292167 := by
  unfold tailWord_3032835
  simp only [CollatzResearch.WordTrace]
  refine ⟨110616579967564236825651959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73744386645042824550434639 110616579967564236825651959)
  ·
    refine ⟨165924869951346355238477939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110616579967564236825651959 165924869951346355238477939)
    ·
      refine ⟨248887304927019532857716909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165924869951346355238477939 248887304927019532857716909)
      ·
        refine ⟨93332739347632324821643841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248887304927019532857716909 93332739347632324821643841)
        ·
          refine ⟨69999554510724243616232881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93332739347632324821643841 69999554510724243616232881)
          ·
            refine ⟨52499665883043182712174661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69999554510724243616232881 52499665883043182712174661)
            ·
              refine ⟨9843687353070596758532749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52499665883043182712174661 9843687353070596758532749)
              ·
                refine ⟨3691382757401473784449781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9843687353070596758532749 3691382757401473784449781)
                ·
                  refine ⟨346067133506388167292167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3691382757401473784449781 346067133506388167292167)
                  ·
                    rfl

theorem cell22_3032835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 5].length) (baseStart_3032835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032835 prefixEnd_3032835 := by exact prefixLift 3032835
  have htrace : WordTrace (prefixWord ++ tailWord_3032835) baseStart_3032835 baseEnd_3032835 := by
    simpa [prefixWord, tailWord_3032835, baseEnd_3032835] using wordTrace_append hprefix tailTrace_3032835
  have hstable : (prefixWord ++ tailWord_3032835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032835).length < 2 ^ (prefixWord ++ tailWord_3032835).sum := by decide
  have hdescent : baseEnd_3032835 < baseStart_3032835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032839 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 3, 3]
def baseStart_3032839 : Nat := 118140960795 + 3032839 * 2 ^ 59
def prefixEnd_3032839 : Nat := 4983230072969 + 3 ^ 40 * 3032839 * 2
def baseEnd_3032839 : Nat := 1038202769800909824776489

theorem tailTrace_3032839 : CollatzResearch.WordTrace tailWord_3032839 prefixEnd_3032839 1038202769800909824776489 := by
  unfold tailWord_3032839
  simp only [CollatzResearch.WordTrace]
  refine ⟨110616725859549745508797571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73744483906366497005865047 110616725859549745508797571)
  ·
    refine ⟨165925088789324618263196357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110616725859549745508797571 165925088789324618263196357)
    ·
      refine ⟨31110954147998365924349317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165925088789324618263196357 31110954147998365924349317)
      ·
        refine ⟨5833303902749693610815497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31110954147998365924349317 5833303902749693610815497)
        ·
          refine ⟨4374977927062270208111623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5833303902749693610815497 4374977927062270208111623)
          ·
            refine ⟨6562466890593405312167435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4374977927062270208111623 6562466890593405312167435)
            ·
              refine ⟨9843700335890107968251153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6562466890593405312167435 9843700335890107968251153)
              ·
                refine ⟨7382775251917580976188365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9843700335890107968251153 7382775251917580976188365)
                ·
                  refine ⟨2768540719469092866070637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7382775251917580976188365 2768540719469092866070637)
                  ·
                    refine ⟨1038202769800909824776489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2768540719469092866070637 1038202769800909824776489)
                    ·
                      rfl

theorem cell22_3032839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_3032839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032839 prefixEnd_3032839 := by exact prefixLift 3032839
  have htrace : WordTrace (prefixWord ++ tailWord_3032839) baseStart_3032839 baseEnd_3032839 := by
    simpa [prefixWord, tailWord_3032839, baseEnd_3032839] using wordTrace_append hprefix tailTrace_3032839
  have hstable : (prefixWord ++ tailWord_3032839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032839).length < 2 ^ (prefixWord ++ tailWord_3032839).sum := by decide
  have hdescent : baseEnd_3032839 < baseStart_3032839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032886 : List Nat := [5, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_3032886 : Nat := 118140960795 + 3032886 * 2 ^ 59
def prefixEnd_3032886 : Nat := 4983230072969 + 3 ^ 40 * 3032886 * 2
def baseEnd_3032886 : Nat := 346072952953805789617115

theorem tailTrace_3032886 : CollatzResearch.WordTrace tailWord_3032886 prefixEnd_3032886 346072952953805789617115 := by
  unfold tailWord_3032886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6913652505648717033484907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73745626726919648357172341 6913652505648717033484907)
  ·
    refine ⟨10370478758473075550227361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6913652505648717033484907 10370478758473075550227361)
    ·
      refine ⟨7777859068854806662670521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10370478758473075550227361 7777859068854806662670521)
      ·
        refine ⟨5833394301641104997002891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7777859068854806662670521 5833394301641104997002891)
        ·
          refine ⟨8750091452461657495504337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5833394301641104997002891 8750091452461657495504337)
          ·
            refine ⟨6562568589346243121628253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8750091452461657495504337 6562568589346243121628253)
            ·
              refine ⟨2460963221004841170610595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6562568589346243121628253 2460963221004841170610595)
              ·
                refine ⟨3691444831507261755915893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2460963221004841170610595 3691444831507261755915893)
                ·
                  refine ⟨346072952953805789617115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3691444831507261755915893 346072952953805789617115)
                  ·
                    rfl

theorem cell22_3032886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_3032886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032886 prefixEnd_3032886 := by exact prefixLift 3032886
  have htrace : WordTrace (prefixWord ++ tailWord_3032886) baseStart_3032886 baseEnd_3032886 := by
    simpa [prefixWord, tailWord_3032886, baseEnd_3032886] using wordTrace_append hprefix tailTrace_3032886
  have hstable : (prefixWord ++ tailWord_3032886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032886).length < 2 ^ (prefixWord ++ tailWord_3032886).sum := by decide
  have hdescent : baseEnd_3032886 < baseStart_3032886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032914 : List Nat := [3, 2, 2, 1, 1, 3, 3, 3, 4]
def baseStart_3032914 : Nat := 118140960795 + 3032914 * 2 ^ 59
def prefixEnd_3032914 : Nat := 4983230072969 + 3 ^ 40 * 3032914 * 2
def baseEnd_3032914 : Nat := 346076147944544876383753

theorem tailTrace_3032914 : CollatzResearch.WordTrace tailWord_3032914 prefixEnd_3032914 346076147944544876383753 := by
  unfold tailWord_3032914
  simp only [CollatzResearch.WordTrace]
  refine ⟨27654865333569508329444449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73746307556185355545185197 27654865333569508329444449)
  ·
    refine ⟨20741149000177131247083337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27654865333569508329444449 20741149000177131247083337)
    ·
      refine ⟨15555861750132848435312503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20741149000177131247083337 15555861750132848435312503)
      ·
        refine ⟨23333792625199272652968755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15555861750132848435312503 23333792625199272652968755)
        ·
          refine ⟨35000688937798908979453133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23333792625199272652968755 35000688937798908979453133)
          ·
            refine ⟨13125258351674590867294925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35000688937798908979453133 13125258351674590867294925)
            ·
              refine ⟨4921971881877971575235597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13125258351674590867294925 4921971881877971575235597)
              ·
                refine ⟨1845739455704239340713349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4921971881877971575235597 1845739455704239340713349)
                ·
                  refine ⟨346076147944544876383753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1845739455704239340713349 346076147944544876383753)
                  ·
                    rfl

theorem cell22_3032914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_3032914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032914 prefixEnd_3032914 := by exact prefixLift 3032914
  have htrace : WordTrace (prefixWord ++ tailWord_3032914) baseStart_3032914 baseEnd_3032914 := by
    simpa [prefixWord, tailWord_3032914, baseEnd_3032914] using wordTrace_append hprefix tailTrace_3032914
  have hstable : (prefixWord ++ tailWord_3032914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032914).length < 2 ^ (prefixWord ++ tailWord_3032914).sum := by decide
  have hdescent : baseEnd_3032914 < baseStart_3032914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032927 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 2, 4]
def baseStart_3032927 : Nat := 118140960795 + 3032927 * 2 ^ 59
def prefixEnd_3032927 : Nat := 4983230072969 + 3 ^ 40 * 3032927 * 2
def baseEnd_3032927 : Nat := 1038232893999306928576219

theorem tailTrace_3032927 : CollatzResearch.WordTrace tailWord_3032927 prefixEnd_3032927 1038232893999306928576219 := by
  unfold tailWord_3032927
  simp only [CollatzResearch.WordTrace]
  refine ⟨110619935483230936538001035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73746623655487291025334023 110619935483230936538001035)
  ·
    refine ⟨165929903224846404807001553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110619935483230936538001035 165929903224846404807001553)
    ·
      refine ⟨124447427418634803605251165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165929903224846404807001553 124447427418634803605251165)
      ·
        refine ⟨46667785281988051351969187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124447427418634803605251165 46667785281988051351969187)
        ·
          refine ⟨70001677922982077027953781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46667785281988051351969187 70001677922982077027953781)
          ·
            refine ⟨6562657305279569721370667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70001677922982077027953781 6562657305279569721370667)
            ·
              refine ⟨9843985957919354582056001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6562657305279569721370667 9843985957919354582056001)
              ·
                refine ⟨7382989468439515936542001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9843985957919354582056001 7382989468439515936542001)
                ·
                  refine ⟨5537242101329636952406501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7382989468439515936542001 5537242101329636952406501)
                  ·
                    refine ⟨1038232893999306928576219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5537242101329636952406501 1038232893999306928576219)
                    ·
                      rfl

theorem cell22_3032927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_3032927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032927 prefixEnd_3032927 := by exact prefixLift 3032927
  have htrace : WordTrace (prefixWord ++ tailWord_3032927) baseStart_3032927 baseEnd_3032927 := by
    simpa [prefixWord, tailWord_3032927, baseEnd_3032927] using wordTrace_append hprefix tailTrace_3032927
  have hstable : (prefixWord ++ tailWord_3032927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032927).length < 2 ^ (prefixWord ++ tailWord_3032927).sum := by decide
  have hdescent : baseEnd_3032927 < baseStart_3032927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032931 : List Nat := [1, 1, 1, 5, 4, 1, 3, 2, 4]
def baseStart_3032931 : Nat := 118140960795 + 3032931 * 2 ^ 59
def prefixEnd_3032931 : Nat := 4983230072969 + 3 ^ 40 * 3032931 * 2
def baseEnd_3032931 : Nat := 346078087760350750492069

theorem tailTrace_3032931 : CollatzResearch.WordTrace tailWord_3032931 prefixEnd_3032931 346078087760350750492069 := by
  unfold tailWord_3032931
  simp only [CollatzResearch.WordTrace]
  refine ⟨110620081375216445221146647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73746720916810963480764431 110620081375216445221146647)
  ·
    refine ⟨165930122062824667831719971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110620081375216445221146647 165930122062824667831719971)
    ·
      refine ⟨248895183094237001747579957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165930122062824667831719971 248895183094237001747579957)
      ·
        refine ⟨23333923415084718913835621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 248895183094237001747579957 23333923415084718913835621)
        ·
          refine ⟨4375110640328384796344179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23333923415084718913835621 4375110640328384796344179)
          ·
            refine ⟨6562665960492577194516269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4375110640328384796344179 6562665960492577194516269)
            ·
              refine ⟨2460999735184716447943601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6562665960492577194516269 2460999735184716447943601)
              ·
                refine ⟨1845749801388537335957701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2460999735184716447943601 1845749801388537335957701)
                ·
                  refine ⟨346078087760350750492069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1845749801388537335957701 346078087760350750492069)
                  ·
                    rfl

theorem cell22_3032931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 4].length) (baseStart_3032931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032931 prefixEnd_3032931 := by exact prefixLift 3032931
  have htrace : WordTrace (prefixWord ++ tailWord_3032931) baseStart_3032931 baseEnd_3032931 := by
    simpa [prefixWord, tailWord_3032931, baseEnd_3032931] using wordTrace_append hprefix tailTrace_3032931
  have hstable : (prefixWord ++ tailWord_3032931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032931).length < 2 ^ (prefixWord ++ tailWord_3032931).sum := by decide
  have hdescent : baseEnd_3032931 < baseStart_3032931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032942 : List Nat := [4, 1, 2, 3, 1, 1, 1, 9]
def baseStart_3032942 : Nat := 118140960795 + 3032942 * 2 ^ 59
def prefixEnd_3032942 : Nat := 4983230072969 + 3 ^ 40 * 3032942 * 2
def baseEnd_3032942 : Nat := 115359780978427987716797

theorem tailTrace_3032942 : CollatzResearch.WordTrace tailWord_3032942 prefixEnd_3032942 115359780978427987716797 := by
  unfold tailWord_3032942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13827560322272074262474635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73746988385451062733198053 13827560322272074262474635)
  ·
    refine ⟨20741340483408111393711953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13827560322272074262474635 20741340483408111393711953)
    ·
      refine ⟨15556005362556083545283965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20741340483408111393711953 15556005362556083545283965)
      ·
        refine ⟨5833502010958531329481487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15556005362556083545283965 5833502010958531329481487)
        ·
          refine ⟨8750253016437796994222231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5833502010958531329481487 8750253016437796994222231)
          ·
            refine ⟨13125379524656695491333347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8750253016437796994222231 13125379524656695491333347)
            ·
              refine ⟨19688069286985043237000021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13125379524656695491333347 19688069286985043237000021)
              ·
                refine ⟨115359780978427987716797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19688069286985043237000021 115359780978427987716797)
                ·
                  rfl

theorem cell22_3032942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_3032942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032942 prefixEnd_3032942 := by exact prefixLift 3032942
  have htrace : WordTrace (prefixWord ++ tailWord_3032942) baseStart_3032942 baseEnd_3032942 := by
    simpa [prefixWord, tailWord_3032942, baseEnd_3032942] using wordTrace_append hprefix tailTrace_3032942
  have hstable : (prefixWord ++ tailWord_3032942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032942).length < 2 ^ (prefixWord ++ tailWord_3032942).sum := by decide
  have hdescent : baseEnd_3032942 < baseStart_3032942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032957 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 5, 3]
def baseStart_3032957 : Nat := 118140960795 + 3032957 * 2 ^ 59
def prefixEnd_3032957 : Nat := 4983230072969 + 3 ^ 40 * 3032957 * 2
def baseEnd_3032957 : Nat := 1038243163612396850326127

theorem tailTrace_3032957 : CollatzResearch.WordTrace tailWord_3032957 prefixEnd_3032957 1038243163612396850326127 := by
  unfold tailWord_3032957
  simp only [CollatzResearch.WordTrace]
  refine ⟨110621029673122251661593125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73747353115414834441062083 110621029673122251661593125)
  ·
    refine ⟨20741443063710422186548711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110621029673122251661593125 20741443063710422186548711)
    ·
      refine ⟨31112164595565633279823067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20741443063710422186548711 31112164595565633279823067)
      ·
        refine ⟨46668246893348449919734601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31112164595565633279823067 46668246893348449919734601)
        ·
          refine ⟨35001185170011337439800951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46668246893348449919734601 35001185170011337439800951)
          ·
            refine ⟨52501777755017006159701427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35001185170011337439800951 52501777755017006159701427)
            ·
              refine ⟨78752666632525509239552141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52501777755017006159701427 78752666632525509239552141)
              ·
                refine ⟨29532249987197065964832053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78752666632525509239552141 29532249987197065964832053)
                ·
                  refine ⟨2768648436299724934203005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29532249987197065964832053 2768648436299724934203005)
                  ·
                    refine ⟨1038243163612396850326127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2768648436299724934203005 1038243163612396850326127)
                    ·
                      rfl

theorem cell22_3032957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_3032957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032957 prefixEnd_3032957 := by exact prefixLift 3032957
  have htrace : WordTrace (prefixWord ++ tailWord_3032957) baseStart_3032957 baseEnd_3032957 := by
    simpa [prefixWord, tailWord_3032957, baseEnd_3032957] using wordTrace_append hprefix tailTrace_3032957
  have hstable : (prefixWord ++ tailWord_3032957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032957).length < 2 ^ (prefixWord ++ tailWord_3032957).sum := by decide
  have hdescent : baseEnd_3032957 < baseStart_3032957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032961 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 2, 4]
def baseStart_3032961 : Nat := 118140960795 + 3032961 * 2 ^ 59
def prefixEnd_3032961 : Nat := 4983230072969 + 3 ^ 40 * 3032961 * 2
def baseEnd_3032961 : Nat := 1038244532894142173226115

theorem tailTrace_3032961 : CollatzResearch.WordTrace tailWord_3032961 prefixEnd_3032961 1038244532894142173226115 := by
  unfold tailWord_3032961
  simp only [CollatzResearch.WordTrace]
  refine ⟨110621175565107760344738737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73747450376738506896492491 110621175565107760344738737)
  ·
    refine ⟨82965881673830820258554053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110621175565107760344738737 82965881673830820258554053)
    ·
      refine ⟨15556102813843278798478885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82965881673830820258554053 15556102813843278798478885)
      ·
        refine ⟨2916769277595614774714791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15556102813843278798478885 2916769277595614774714791)
        ·
          refine ⟨4375153916393422162072187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2916769277595614774714791 4375153916393422162072187)
          ·
            refine ⟨6562730874590133243108281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4375153916393422162072187 6562730874590133243108281)
            ·
              refine ⟨4922048155942599932331211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6562730874590133243108281 4922048155942599932331211)
              ·
                refine ⟨7383072233913899898496817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4922048155942599932331211 7383072233913899898496817)
                ·
                  refine ⟨5537304175435424923872613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7383072233913899898496817 5537304175435424923872613)
                  ·
                    refine ⟨1038244532894142173226115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5537304175435424923872613 1038244532894142173226115)
                    ·
                      rfl

theorem cell22_3032961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_3032961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032961 prefixEnd_3032961 := by exact prefixLift 3032961
  have htrace : WordTrace (prefixWord ++ tailWord_3032961) baseStart_3032961 baseEnd_3032961 := by
    simpa [prefixWord, tailWord_3032961, baseEnd_3032961] using wordTrace_append hprefix tailTrace_3032961
  have hstable : (prefixWord ++ tailWord_3032961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032961).length < 2 ^ (prefixWord ++ tailWord_3032961).sum := by decide
  have hdescent : baseEnd_3032961 < baseStart_3032961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032982 : List Nat := [5, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_3032982 : Nat := 118140960795 + 3032982 * 2 ^ 59
def prefixEnd_3032982 : Nat := 4983230072969 + 3 ^ 40 * 3032982 * 2
def baseEnd_3032982 : Nat := 346083907207768372817017

theorem tailTrace_3032982 : CollatzResearch.WordTrace tailWord_3032982 prefixEnd_3032982 346083907207768372817017 := by
  unfold tailWord_3032982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6913871343626980058203325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73747960998687787287502133 6913871343626980058203325)
  ·
    refine ⟨2592701753860117521826247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6913871343626980058203325 2592701753860117521826247)
    ·
      refine ⟨3889052630790176282739371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2592701753860117521826247 3889052630790176282739371)
      ·
        refine ⟨5833578946185264424109057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3889052630790176282739371 5833578946185264424109057)
        ·
          refine ⟨4375184209638948318081793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5833578946185264424109057 4375184209638948318081793)
          ·
            refine ⟨3281388157229211238561345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4375184209638948318081793 3281388157229211238561345)
            ·
              refine ⟨2461041117921908428921009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3281388157229211238561345 2461041117921908428921009)
              ·
                refine ⟨1845780838441431321690757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2461041117921908428921009 1845780838441431321690757)
                ·
                  refine ⟨346083907207768372817017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1845780838441431321690757 346083907207768372817017)
                  ·
                    rfl

theorem cell22_3032982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_3032982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3032982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3032982 prefixEnd_3032982 := by exact prefixLift 3032982
  have htrace : WordTrace (prefixWord ++ tailWord_3032982) baseStart_3032982 baseEnd_3032982 := by
    simpa [prefixWord, tailWord_3032982, baseEnd_3032982] using wordTrace_append hprefix tailTrace_3032982
  have hstable : (prefixWord ++ tailWord_3032982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032982).length < 2 ^ (prefixWord ++ tailWord_3032982).sum := by decide
  have hdescent : baseEnd_3032982 < baseStart_3032982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033017 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 3, 4]
def baseStart_3033017 : Nat := 118140960795 + 3033017 * 2 ^ 59
def prefixEnd_3033017 : Nat := 4983230072969 + 3 ^ 40 * 3033017 * 2
def baseEnd_3033017 : Nat := 1038263702838576693825943

theorem tailTrace_3033017 : CollatzResearch.WordTrace tailWord_3033017 prefixEnd_3033017 1038263702838576693825943 := by
  unfold tailWord_3033017
  simp only [CollatzResearch.WordTrace]
  refine ⟨110623218052904881908777305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73748812035269921272518203 110623218052904881908777305)
  ·
    refine ⟨82967413539678661431582979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110623218052904881908777305 82967413539678661431582979)
    ·
      refine ⟨124451120309517992147374469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82967413539678661431582979 124451120309517992147374469)
      ·
        refine ⟨23334585058034623527632713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124451120309517992147374469 23334585058034623527632713)
        ·
          refine ⟨17500938793525967645724535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23334585058034623527632713 17500938793525967645724535)
          ·
            refine ⟨26251408190288951468586803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17500938793525967645724535 26251408190288951468586803)
            ·
              refine ⟨39377112285433427202880205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26251408190288951468586803 39377112285433427202880205)
              ·
                refine ⟨14766417107037535201080077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39377112285433427202880205 14766417107037535201080077)
                ·
                  refine ⟨5537406415139075700405029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14766417107037535201080077 5537406415139075700405029)
                  ·
                    refine ⟨1038263702838576693825943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5537406415139075700405029 1038263702838576693825943)
                    ·
                      rfl

theorem cell22_3033017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_3033017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033017 prefixEnd_3033017 := by exact prefixLift 3033017
  have htrace : WordTrace (prefixWord ++ tailWord_3033017) baseStart_3033017 baseEnd_3033017 := by
    simpa [prefixWord, tailWord_3033017, baseEnd_3033017] using wordTrace_append hprefix tailTrace_3033017
  have hstable : (prefixWord ++ tailWord_3033017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033017).length < 2 ^ (prefixWord ++ tailWord_3033017).sum := by decide
  have hdescent : baseEnd_3033017 < baseStart_3033017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033049 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 6]
def baseStart_3033049 : Nat := 118140960795 + 3033049 * 2 ^ 59
def prefixEnd_3033049 : Nat := 4983230072969 + 3 ^ 40 * 3033049 * 2
def baseEnd_3033049 : Nat := 346091552364179759008615

theorem tailTrace_3033049 : CollatzResearch.WordTrace tailWord_3033049 prefixEnd_3033049 346091552364179759008615 := by
  unfold tailWord_3033049
  simp only [CollatzResearch.WordTrace]
  refine ⟨110624385188788951373942201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73749590125859300915961467 110624385188788951373942201)
  ·
    refine ⟨82968288891591713530456651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110624385188788951373942201 82968288891591713530456651)
    ·
      refine ⟨124452433337387570295684977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82968288891591713530456651 124452433337387570295684977)
      ·
        refine ⟨93339325003040677721763733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124452433337387570295684977 93339325003040677721763733)
        ·
          refine ⟨4375280859517531768207675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 93339325003040677721763733 4375280859517531768207675)
          ·
            refine ⟨6562921289276297652311513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4375280859517531768207675 6562921289276297652311513)
            ·
              refine ⟨4922190966957223239233635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6562921289276297652311513 4922190966957223239233635)
              ·
                refine ⟨7383286450435834858850453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4922190966957223239233635 7383286450435834858850453)
                ·
                  refine ⟨346091552364179759008615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7383286450435834858850453 346091552364179759008615)
                  ·
                    rfl

theorem cell22_3033049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 6].length) (baseStart_3033049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033049 prefixEnd_3033049 := by exact prefixLift 3033049
  have htrace : WordTrace (prefixWord ++ tailWord_3033049) baseStart_3033049 baseEnd_3033049 := by
    simpa [prefixWord, tailWord_3033049, baseEnd_3033049] using wordTrace_append hprefix tailTrace_3033049
  have hstable : (prefixWord ++ tailWord_3033049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033049).length < 2 ^ (prefixWord ++ tailWord_3033049).sum := by decide
  have hdescent : baseEnd_3033049 < baseStart_3033049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033184 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 6]
def baseStart_3033184 : Nat := 118140960795 + 3033184 * 2 ^ 59
def prefixEnd_3033184 : Nat := 4983230072969 + 3 ^ 40 * 3033184 * 2
def baseEnd_3033184 : Nat := 346106956783814641633477

theorem tailTrace_3033184 : CollatzResearch.WordTrace tailWord_3033184 prefixEnd_3033184 346106956783814641633477 := by
  unfold tailWord_3033184
  simp only [CollatzResearch.WordTrace]
  refine ⟨55314654521649934715053303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73752872695533246286737737 55314654521649934715053303)
  ·
    refine ⟨82971981782474902072579955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55314654521649934715053303 82971981782474902072579955)
    ·
      refine ⟨124457972673712353108869933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82971981782474902072579955 124457972673712353108869933)
      ·
        refine ⟨46671739752642132415826225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124457972673712353108869933 46671739752642132415826225)
        ·
          refine ⟨35003804814481599311869669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46671739752642132415826225 35003804814481599311869669)
          ·
            refine ⟨6563213402715299870975563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35003804814481599311869669 6563213402715299870975563)
            ·
              refine ⟨9844820104072949806463345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6563213402715299870975563 9844820104072949806463345)
              ·
                refine ⟨7383615078054712354847509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9844820104072949806463345 7383615078054712354847509)
                ·
                  refine ⟨346106956783814641633477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7383615078054712354847509 346106956783814641633477)
                  ·
                    rfl

theorem cell22_3033184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 6].length) (baseStart_3033184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033184 prefixEnd_3033184 := by exact prefixLift 3033184
  have htrace : WordTrace (prefixWord ++ tailWord_3033184) baseStart_3033184 baseEnd_3033184 := by
    simpa [prefixWord, tailWord_3033184, baseEnd_3033184] using wordTrace_append hprefix tailTrace_3033184
  have hstable : (prefixWord ++ tailWord_3033184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033184).length < 2 ^ (prefixWord ++ tailWord_3033184).sum := by decide
  have hdescent : baseEnd_3033184 < baseStart_3033184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033199 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 1, 5]
def baseStart_3033199 : Nat := 118140960795 + 3033199 * 2 ^ 59
def prefixEnd_3033199 : Nat := 4983230072969 + 3 ^ 40 * 3033199 * 2
def baseEnd_3033199 : Nat := 1038326005157988885775385

theorem tailTrace_3033199 : CollatzResearch.WordTrace tailWord_3033199 prefixEnd_3033199 1038326005157988885775385 := by
  unfold tailWord_3033199
  simp only [CollatzResearch.WordTrace]
  refine ⟨110629856138245526991902651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73753237425497017994601767 110629856138245526991902651)
  ·
    refine ⟨165944784207368290487853977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110629856138245526991902651 165944784207368290487853977)
    ·
      refine ⟨124458588155526217865890483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165944784207368290487853977 124458588155526217865890483)
      ·
        refine ⟨186687882233289326798835725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124458588155526217865890483 186687882233289326798835725)
        ·
          refine ⟨70007955837483497549563397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186687882233289326798835725 70007955837483497549563397)
          ·
            refine ⟨13126491719528155790543137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70007955837483497549563397 13126491719528155790543137)
            ·
              refine ⟨9844868789646116842907353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13126491719528155790543137 9844868789646116842907353)
              ·
                refine ⟨7383651592234587632180515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9844868789646116842907353 7383651592234587632180515)
                ·
                  refine ⟨11075477388351881448270773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7383651592234587632180515 11075477388351881448270773)
                  ·
                    refine ⟨1038326005157988885775385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11075477388351881448270773 1038326005157988885775385)
                    ·
                      rfl

theorem cell22_3033199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_3033199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033199 prefixEnd_3033199 := by exact prefixLift 3033199
  have htrace : WordTrace (prefixWord ++ tailWord_3033199) baseStart_3033199 baseEnd_3033199 := by
    simpa [prefixWord, tailWord_3033199, baseEnd_3033199] using wordTrace_append hprefix tailTrace_3033199
  have hstable : (prefixWord ++ tailWord_3033199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033199).length < 2 ^ (prefixWord ++ tailWord_3033199).sum := by decide
  have hdescent : baseEnd_3033199 < baseStart_3033199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033201 : List Nat := [1, 2, 2, 2, 1, 1, 6, 3, 4]
def baseStart_3033201 : Nat := 118140960795 + 3033201 * 2 ^ 59
def prefixEnd_3033201 : Nat := 4983230072969 + 3 ^ 40 * 3033201 * 2
def baseEnd_3033201 : Nat := 346108896599620515741793

theorem tailTrace_3033201 : CollatzResearch.WordTrace tailWord_3033201 prefixEnd_3033201 346108896599620515741793 := by
  unfold tailWord_3033201
  simp only [CollatzResearch.WordTrace]
  refine ⟨110629929084238281333475457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73753286056158854222316971 110629929084238281333475457)
  ·
    refine ⟨82972446813178711000106593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110629929084238281333475457 82972446813178711000106593)
    ·
      refine ⟨62229335109884033250079945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82972446813178711000106593 62229335109884033250079945)
      ·
        refine ⟨46672001332413024937559959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62229335109884033250079945 46672001332413024937559959)
        ·
          refine ⟨70008001998619537406339939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46672001332413024937559959 70008001998619537406339939)
          ·
            refine ⟨105012002997929306109509909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70008001998619537406339939 105012002997929306109509909)
            ·
              refine ⟨4922437640527936223883277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105012002997929306109509909 4922437640527936223883277)
              ·
                refine ⟨1845914115197976083956229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4922437640527936223883277 1845914115197976083956229)
                ·
                  refine ⟨346108896599620515741793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1845914115197976083956229 346108896599620515741793)
                  ·
                    rfl

theorem cell22_3033201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 4].length) (baseStart_3033201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033201 prefixEnd_3033201 := by exact prefixLift 3033201
  have htrace : WordTrace (prefixWord ++ tailWord_3033201) baseStart_3033201 baseEnd_3033201 := by
    simpa [prefixWord, tailWord_3033201, baseEnd_3033201] using wordTrace_append hprefix tailTrace_3033201
  have hstable : (prefixWord ++ tailWord_3033201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033201).length < 2 ^ (prefixWord ++ tailWord_3033201).sum := by decide
  have hdescent : baseEnd_3033201 < baseStart_3033201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033244 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 2, 7]
def baseStart_3033244 : Nat := 118140960795 + 3033244 * 2 ^ 59
def prefixEnd_3033244 : Nat := 4983230072969 + 3 ^ 40 * 3033244 * 2
def baseEnd_3033244 : Nat := 1038341409577623768400247

theorem tailTrace_3033244 : CollatzResearch.WordTrace tailWord_3033244 prefixEnd_3033244 1038341409577623768400247 := by
  unfold tailWord_3033244
  simp only [CollatzResearch.WordTrace]
  refine ⟨55315748711541249838645393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73754331615388333118193857 55315748711541249838645393)
  ·
    refine ⟨41486811533655937378984045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55315748711541249838645393 41486811533655937378984045)
    ·
      refine ⟨15557554325120976517119017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41486811533655937378984045 15557554325120976517119017)
      ·
        refine ⟨11668165743840732387839263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15557554325120976517119017 11668165743840732387839263)
        ·
          refine ⟨17502248615761098581758895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11668165743840732387839263 17502248615761098581758895)
          ·
            refine ⟨26253372923641647872638343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17502248615761098581758895 26253372923641647872638343)
            ·
              refine ⟨39380059385462471808957515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26253372923641647872638343 39380059385462471808957515)
              ·
                refine ⟨59070089078193707713436273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39380059385462471808957515 59070089078193707713436273)
                ·
                  refine ⟨44302566808645280785077205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59070089078193707713436273 44302566808645280785077205)
                  ·
                    refine ⟨1038341409577623768400247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44302566808645280785077205 1038341409577623768400247)
                    ·
                      rfl

theorem cell22_3033244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_3033244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033244 prefixEnd_3033244 := by exact prefixLift 3033244
  have htrace : WordTrace (prefixWord ++ tailWord_3033244) baseStart_3033244 baseEnd_3033244 := by
    simpa [prefixWord, tailWord_3033244, baseEnd_3033244] using wordTrace_append hprefix tailTrace_3033244
  have hstable : (prefixWord ++ tailWord_3033244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033244).length < 2 ^ (prefixWord ++ tailWord_3033244).sum := by decide
  have hdescent : baseEnd_3033244 < baseStart_3033244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033274 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 7]
def baseStart_3033274 : Nat := 118140960795 + 3033274 * 2 ^ 59
def prefixEnd_3033274 : Nat := 4983230072969 + 3 ^ 40 * 3033274 * 2
def baseEnd_3033274 : Nat := 346117226396904563383385

theorem tailTrace_3033274 : CollatzResearch.WordTrace tailWord_3033274 prefixEnd_3033274 346117226396904563383385 := by
  unfold tailWord_3033274
  simp only [CollatzResearch.WordTrace]
  refine ⟨27658147903243453700220719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73755061075315876533921917 27658147903243453700220719)
  ·
    refine ⟨41487221854865180550331079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27658147903243453700220719 41487221854865180550331079)
    ·
      refine ⟨62230832782297770825496619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41487221854865180550331079 62230832782297770825496619)
      ·
        refine ⟨93346249173446656238244929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62230832782297770825496619 93346249173446656238244929)
        ·
          refine ⟨70009686880084992178683697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93346249173446656238244929 70009686880084992178683697)
          ·
            refine ⟨52507265160063744134012773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70009686880084992178683697 52507265160063744134012773)
            ·
              refine ⟨9845112217511952025127395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52507265160063744134012773 9845112217511952025127395)
              ·
                refine ⟨14767668326267928037691093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9845112217511952025127395 14767668326267928037691093)
                ·
                  refine ⟨346117226396904563383385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14767668326267928037691093 346117226396904563383385)
                  ·
                    rfl

theorem cell22_3033274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_3033274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033274 prefixEnd_3033274 := by exact prefixLift 3033274
  have htrace : WordTrace (prefixWord ++ tailWord_3033274) baseStart_3033274 baseEnd_3033274 := by
    simpa [prefixWord, tailWord_3033274, baseEnd_3033274] using wordTrace_append hprefix tailTrace_3033274
  have hstable : (prefixWord ++ tailWord_3033274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033274).length < 2 ^ (prefixWord ++ tailWord_3033274).sum := by decide
  have hdescent : baseEnd_3033274 < baseStart_3033274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033370 : List Nat := [3, 1, 1, 3, 4, 1, 2, 3, 4]
def baseStart_3033370 : Nat := 118140960795 + 3033370 * 2 ^ 59
def prefixEnd_3033370 : Nat := 4983230072969 + 3 ^ 40 * 3033370 * 2
def baseEnd_3033370 : Nat := 346128180650867146583287

theorem tailTrace_3033370 : CollatzResearch.WordTrace tailWord_3033370 prefixEnd_3033370 346128180650867146583287 := by
  unfold tailWord_3033370
  simp only [CollatzResearch.WordTrace]
  refine ⟨27659023255156505799094391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73757395347084015464251709 27659023255156505799094391)
  ·
    refine ⟨41488534882734758698641587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27659023255156505799094391 41488534882734758698641587)
    ·
      refine ⟨62232802324102138047962381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41488534882734758698641587 62232802324102138047962381)
      ·
        refine ⟨23337300871538301767985893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62232802324102138047962381 23337300871538301767985893)
        ·
          refine ⟨4375743913413431581497355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23337300871538301767985893 4375743913413431581497355)
          ·
            refine ⟨6563615870120147372246033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4375743913413431581497355 6563615870120147372246033)
            ·
              refine ⟨4922711902590110529184525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6563615870120147372246033 4922711902590110529184525)
              ·
                refine ⟨1846016963471291448444197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4922711902590110529184525 1846016963471291448444197)
                ·
                  refine ⟨346128180650867146583287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1846016963471291448444197 346128180650867146583287)
                  ·
                    rfl

theorem cell22_3033370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_3033370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033370 prefixEnd_3033370 := by exact prefixLift 3033370
  have htrace : WordTrace (prefixWord ++ tailWord_3033370) baseStart_3033370 baseEnd_3033370 := by
    simpa [prefixWord, tailWord_3033370, baseEnd_3033370] using wordTrace_append hprefix tailTrace_3033370
  have hstable : (prefixWord ++ tailWord_3033370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033370).length < 2 ^ (prefixWord ++ tailWord_3033370).sum := by decide
  have hdescent : baseEnd_3033370 < baseStart_3033370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033381 : List Nat := [1, 3, 1, 2, 5, 1, 9]
def baseStart_3033381 : Nat := 118140960795 + 3033381 * 2 ^ 59
def prefixEnd_3033381 : Nat := 4983230072969 + 3 ^ 40 * 3033381 * 2
def baseEnd_3033381 : Nat := 38458826202866706582401

theorem tailTrace_3033381 : CollatzResearch.WordTrace tailWord_3033381 prefixEnd_3033381 38458826202866706582401 := by
  unfold tailWord_3033381
  simp only [CollatzResearch.WordTrace]
  refine ⟨110636494223586172075027997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73757662815724114716685331 110636494223586172075027997)
  ·
    refine ⟨41488685333844814528135499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110636494223586172075027997 41488685333844814528135499)
    ·
      refine ⟨62233028000767221792203249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41488685333844814528135499 62233028000767221792203249)
      ·
        refine ⟨46674771000575416344152437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62233028000767221792203249 46674771000575416344152437)
        ·
          refine ⟨4375759781303945282264291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46674771000575416344152437 4375759781303945282264291)
          ·
            refine ⟨6563639671955917923396437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4375759781303945282264291 6563639671955917923396437)
            ·
              refine ⟨38458826202866706582401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6563639671955917923396437 38458826202866706582401)
              ·
                rfl

theorem cell22_3033381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 9].length) (baseStart_3033381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033381 prefixEnd_3033381 := by exact prefixLift 3033381
  have htrace : WordTrace (prefixWord ++ tailWord_3033381) baseStart_3033381 baseEnd_3033381 := by
    simpa [prefixWord, tailWord_3033381, baseEnd_3033381] using wordTrace_append hprefix tailTrace_3033381
  have hstable : (prefixWord ++ tailWord_3033381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033381).length < 2 ^ (prefixWord ++ tailWord_3033381).sum := by decide
  have hdescent : baseEnd_3033381 < baseStart_3033381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033426 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 7]
def baseStart_3033426 : Nat := 118140960795 + 3033426 * 2 ^ 59
def prefixEnd_3033426 : Nat := 4983230072969 + 3 ^ 40 * 3033426 * 2
def baseEnd_3033426 : Nat := 346134570632345320116563

theorem tailTrace_3033426 : CollatzResearch.WordTrace tailWord_3033426 prefixEnd_3033426 346134570632345320116563 := by
  unfold tailWord_3033426
  simp only [CollatzResearch.WordTrace]
  refine ⟨27659533877105786190104033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73758757005615429840277421 27659533877105786190104033)
  ·
    refine ⟨20744650407829339642578025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27659533877105786190104033 20744650407829339642578025)
    ·
      refine ⟨15558487805872004731933519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20744650407829339642578025 15558487805872004731933519)
      ·
        refine ⟨23337731708808007097900279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15558487805872004731933519 23337731708808007097900279)
        ·
          refine ⟨35006597563212010646850419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23337731708808007097900279 35006597563212010646850419)
          ·
            refine ⟨52509896344818015970275629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35006597563212010646850419 52509896344818015970275629)
            ·
              refine ⟨19691211129306755988853361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52509896344818015970275629 19691211129306755988853361)
              ·
                refine ⟨14768408346980066991640021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19691211129306755988853361 14768408346980066991640021)
                ·
                  refine ⟨346134570632345320116563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14768408346980066991640021 346134570632345320116563)
                  ·
                    rfl

theorem cell22_3033426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_3033426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033426 prefixEnd_3033426 := by exact prefixLift 3033426
  have htrace : WordTrace (prefixWord ++ tailWord_3033426) baseStart_3033426 baseEnd_3033426 := by
    simpa [prefixWord, tailWord_3033426, baseEnd_3033426] using wordTrace_append hprefix tailTrace_3033426
  have hstable : (prefixWord ++ tailWord_3033426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033426).length < 2 ^ (prefixWord ++ tailWord_3033426).sum := by decide
  have hdescent : baseEnd_3033426 < baseStart_3033426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033438 : List Nat := [4, 4, 2, 1, 1, 1, 3, 2, 4]
def baseStart_3033438 : Nat := 118140960795 + 3033438 * 2 ^ 59
def prefixEnd_3033438 : Nat := 4983230072969 + 3 ^ 40 * 3033438 * 2
def baseEnd_3033438 : Nat := 346135939914090643016551

theorem tailTrace_3033438 : CollatzResearch.WordTrace tailWord_3033438 prefixEnd_3033438 346135939914090643016551 := by
  unfold tailWord_3033438
  simp only [CollatzResearch.WordTrace]
  refine ⟨13829821648047458851231621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73759048789586447206568645 13829821648047458851231621)
  ·
    refine ⟨2593091559008898534605929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13829821648047458851231621 2593091559008898534605929)
    ·
      refine ⟨1944818669256673900954447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2593091559008898534605929 1944818669256673900954447)
      ·
        refine ⟨2917228003885010851431671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1944818669256673900954447 2917228003885010851431671)
        ·
          refine ⟨4375842005827516277147507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2917228003885010851431671 4375842005827516277147507)
          ·
            refine ⟨6563763008741274415721261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4375842005827516277147507 6563763008741274415721261)
            ·
              refine ⟨2461411128277977905895473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6563763008741274415721261 2461411128277977905895473)
              ·
                refine ⟨1846058346208483429421605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2461411128277977905895473 1846058346208483429421605)
                ·
                  refine ⟨346135939914090643016551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1846058346208483429421605 346135939914090643016551)
                  ·
                    rfl

theorem cell22_3033438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_3033438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033438 prefixEnd_3033438 := by exact prefixLift 3033438
  have htrace : WordTrace (prefixWord ++ tailWord_3033438) baseStart_3033438 baseEnd_3033438 := by
    simpa [prefixWord, tailWord_3033438, baseEnd_3033438] using wordTrace_append hprefix tailTrace_3033438
  have hstable : (prefixWord ++ tailWord_3033438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033438).length < 2 ^ (prefixWord ++ tailWord_3033438).sum := by decide
  have hdescent : baseEnd_3033438 < baseStart_3033438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033608 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 5, 4]
def baseStart_3033608 : Nat := 118140960795 + 3033608 * 2 ^ 59
def prefixEnd_3033608 : Nat := 4983230072969 + 3 ^ 40 * 3033608 * 2
def baseEnd_3033608 : Nat := 1038466014216448152299131

theorem tailTrace_3033608 : CollatzResearch.WordTrace tailWord_3033608 prefixEnd_3033608 1038466014216448152299131 := by
  unfold tailWord_3033608
  simp only [CollatzResearch.WordTrace]
  refine ⟨55322386796881894921770739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73763182395842526562360985 55322386796881894921770739)
  ·
    refine ⟨82983580195322842382656109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55322386796881894921770739 82983580195322842382656109)
    ·
      refine ⟨31118842573246065893496041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82983580195322842382656109 31118842573246065893496041)
      ·
        refine ⟨23339131929934549420122031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31118842573246065893496041 23339131929934549420122031)
        ·
          refine ⟨35008697894901824130183047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23339131929934549420122031 35008697894901824130183047)
          ·
            refine ⟨52513046842352736195274571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35008697894901824130183047 52513046842352736195274571)
            ·
              refine ⟨78769570263529104292911857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52513046842352736195274571 78769570263529104292911857)
              ·
                refine ⟨59077177697646828219683893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78769570263529104292911857 59077177697646828219683893)
                ·
                  refine ⟨5538485409154390145595365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59077177697646828219683893 5538485409154390145595365)
                  ·
                    refine ⟨1038466014216448152299131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5538485409154390145595365 1038466014216448152299131)
                    ·
                      rfl

theorem cell22_3033608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_3033608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033608 prefixEnd_3033608 := by exact prefixLift 3033608
  have htrace : WordTrace (prefixWord ++ tailWord_3033608) baseStart_3033608 baseEnd_3033608 := by
    simpa [prefixWord, tailWord_3033608, baseEnd_3033608] using wordTrace_append hprefix tailTrace_3033608
  have hstable : (prefixWord ++ tailWord_3033608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033608).length < 2 ^ (prefixWord ++ tailWord_3033608).sum := by decide
  have hdescent : baseEnd_3033608 < baseStart_3033608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033642 : List Nat := [3, 1, 4, 1, 1, 2, 3, 2, 1, 4]
def baseStart_3033642 : Nat := 118140960795 + 3033642 * 2 ^ 59
def prefixEnd_3033642 : Nat := 4983230072969 + 3 ^ 40 * 3033642 * 2
def baseEnd_3033642 : Nat := 1038477653111283396949027

theorem tailTrace_3033642 : CollatzResearch.WordTrace tailWord_3033642 prefixEnd_3033642 1038477653111283396949027 := by
  unfold tailWord_3033642
  simp only [CollatzResearch.WordTrace]
  refine ⟨27661503418910153412569795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73764009117093742433519453 27661503418910153412569795)
  ·
    refine ⟨41492255128365230118854693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27661503418910153412569795 41492255128365230118854693)
    ·
      refine ⟨7779797836568480647285255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41492255128365230118854693 7779797836568480647285255)
      ·
        refine ⟨11669696754852720970927883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7779797836568480647285255 11669696754852720970927883)
        ·
          refine ⟨17504545132279081456391825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11669696754852720970927883 17504545132279081456391825)
          ·
            refine ⟨13128408849209311092293869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17504545132279081456391825 13128408849209311092293869)
            ·
              refine ⟨4923153318453491659610201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13128408849209311092293869 4923153318453491659610201)
              ·
                refine ⟨3692364988840118744707651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4923153318453491659610201 3692364988840118744707651)
                ·
                  refine ⟨5538547483260178117061477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3692364988840118744707651 5538547483260178117061477)
                  ·
                    refine ⟨1038477653111283396949027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5538547483260178117061477 1038477653111283396949027)
                    ·
                      rfl

theorem cell22_3033642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_3033642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033642 prefixEnd_3033642 := by exact prefixLift 3033642
  have htrace : WordTrace (prefixWord ++ tailWord_3033642) baseStart_3033642 baseEnd_3033642 := by
    simpa [prefixWord, tailWord_3033642, baseEnd_3033642] using wordTrace_append hprefix tailTrace_3033642
  have hstable : (prefixWord ++ tailWord_3033642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033642).length < 2 ^ (prefixWord ++ tailWord_3033642).sum := by decide
  have hdescent : baseEnd_3033642 < baseStart_3033642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033674 : List Nat := [3, 1, 2, 1, 1, 6, 2, 2, 4]
def baseStart_3033674 : Nat := 118140960795 + 3033674 * 2 ^ 59
def prefixEnd_3033674 : Nat := 4983230072969 + 3 ^ 40 * 3033674 * 2
def baseEnd_3033674 : Nat := 346162869121748660049643

theorem tailTrace_3033674 : CollatzResearch.WordTrace tailWord_3033674 prefixEnd_3033674 346162869121748660049643 := by
  unfold tailWord_3033674
  simp only [CollatzResearch.WordTrace]
  refine ⟨27661795202881170778861019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73764787207683122076962717 27661795202881170778861019)
  ·
    refine ⟨41492692804321756168291529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27661795202881170778861019 41492692804321756168291529)
    ·
      refine ⟨31119519603241317126218647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41492692804321756168291529 31119519603241317126218647)
      ·
        refine ⟨46679279404861975689327971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31119519603241317126218647 46679279404861975689327971)
        ·
          refine ⟨70018919107292963533991957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46679279404861975689327971 70018919107292963533991957)
          ·
            refine ⟨3282136833154357665655873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70018919107292963533991957 3282136833154357665655873)
            ·
              refine ⟨2461602624865768249241905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3282136833154357665655873 2461602624865768249241905)
              ·
                refine ⟨1846201968649326186931429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2461602624865768249241905 1846201968649326186931429)
                ·
                  refine ⟨346162869121748660049643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1846201968649326186931429 346162869121748660049643)
                  ·
                    rfl

theorem cell22_3033674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_3033674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033674 prefixEnd_3033674 := by exact prefixLift 3033674
  have htrace : WordTrace (prefixWord ++ tailWord_3033674) baseStart_3033674 baseEnd_3033674 := by
    simpa [prefixWord, tailWord_3033674, baseEnd_3033674] using wordTrace_append hprefix tailTrace_3033674
  have hstable : (prefixWord ++ tailWord_3033674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033674).length < 2 ^ (prefixWord ++ tailWord_3033674).sum := by decide
  have hdescent : baseEnd_3033674 < baseStart_3033674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033704 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 2, 4]
def baseStart_3033704 : Nat := 118140960795 + 3033704 * 2 ^ 59
def prefixEnd_3033704 : Nat := 4983230072969 + 3 ^ 40 * 3033704 * 2
def baseEnd_3033704 : Nat := 1038498876978335901898837

theorem tailTrace_3033704 : CollatzResearch.WordTrace tailWord_3033704 prefixEnd_3033704 1038498876978335901898837 := by
  unfold tailWord_3033704
  simp only [CollatzResearch.WordTrace]
  refine ⟨55324137500707999119518083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73765516667610665492690777 55324137500707999119518083)
  ·
    refine ⟨82986206251061998679277125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55324137500707999119518083 82986206251061998679277125)
    ·
      refine ⟨15559913672074124752364461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82986206251061998679277125 15559913672074124752364461)
      ·
        refine ⟨5834967627027796782136673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15559913672074124752364461 5834967627027796782136673)
        ·
          refine ⟨4376225720270847586602505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5834967627027796782136673 4376225720270847586602505)
          ·
            refine ⟨3282169290203135689951879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4376225720270847586602505 3282169290203135689951879)
            ·
              refine ⟨4923253935304703534927819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282169290203135689951879 4923253935304703534927819)
              ·
                refine ⟨7384880902957055302391729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4923253935304703534927819 7384880902957055302391729)
                ·
                  refine ⟨5538660677217791476793797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7384880902957055302391729 5538660677217791476793797)
                  ·
                    refine ⟨1038498876978335901898837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5538660677217791476793797 1038498876978335901898837)
                    ·
                      rfl

theorem cell22_3033704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_3033704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033704 prefixEnd_3033704 := by exact prefixLift 3033704
  have htrace : WordTrace (prefixWord ++ tailWord_3033704) baseStart_3033704 baseEnd_3033704 := by
    simpa [prefixWord, tailWord_3033704, baseEnd_3033704] using wordTrace_append hprefix tailTrace_3033704
  have hstable : (prefixWord ++ tailWord_3033704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033704).length < 2 ^ (prefixWord ++ tailWord_3033704).sum := by decide
  have hdescent : baseEnd_3033704 < baseStart_3033704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033792 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 6]
def baseStart_3033792 : Nat := 118140960795 + 3033792 * 2 ^ 59
def prefixEnd_3033792 : Nat := 4983230072969 + 3 ^ 40 * 3033792 * 2
def baseEnd_3033792 : Nat := 346176333725577668566189

theorem tailTrace_3033792 : CollatzResearch.WordTrace tailWord_3033792 prefixEnd_3033792 346176333725577668566189 := by
  unfold tailWord_3033792
  simp only [CollatzResearch.WordTrace]
  refine ⟨55325742312548594634119815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73767656416731459512159753 55325742312548594634119815)
  ·
    refine ⟨82988613468822891951179723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55325742312548594634119815 82988613468822891951179723)
    ·
      refine ⟨124482920203234337926769585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82988613468822891951179723 124482920203234337926769585)
      ·
        refine ⟨93362190152425753445077189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124482920203234337926769585 93362190152425753445077189)
        ·
          refine ⟨17505410653579828770951973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93362190152425753445077189 17505410653579828770951973)
          ·
            refine ⟨3282264497546217894553495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17505410653579828770951973 3282264497546217894553495)
            ·
              refine ⟨4923396746319326841830243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282264497546217894553495 4923396746319326841830243)
              ·
                refine ⟨7385095119478990262745365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4923396746319326841830243 7385095119478990262745365)
                ·
                  refine ⟨346176333725577668566189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7385095119478990262745365 346176333725577668566189)
                  ·
                    rfl

theorem cell22_3033792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 6].length) (baseStart_3033792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033792 prefixEnd_3033792 := by exact prefixLift 3033792
  have htrace : WordTrace (prefixWord ++ tailWord_3033792) baseStart_3033792 baseEnd_3033792 := by
    simpa [prefixWord, tailWord_3033792, baseEnd_3033792] using wordTrace_append hprefix tailTrace_3033792
  have hstable : (prefixWord ++ tailWord_3033792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033792).length < 2 ^ (prefixWord ++ tailWord_3033792).sum := by decide
  have hdescent : baseEnd_3033792 < baseStart_3033792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033850 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 2, 6]
def baseStart_3033850 : Nat := 118140960795 + 3033850 * 2 ^ 59
def prefixEnd_3033850 : Nat := 4983230072969 + 3 ^ 40 * 3033850 * 2
def baseEnd_3033850 : Nat := 1038548855762040187748389

theorem tailTrace_3033850 : CollatzResearch.WordTrace tailWord_3033850 prefixEnd_3033850 1038548855762040187748389 := by
  unfold tailWord_3033850
  simp only [CollatzResearch.WordTrace]
  refine ⟨27663400014721766293462751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73769066705924710115900669 27663400014721766293462751)
  ·
    refine ⟨41495100022082649440194127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27663400014721766293462751 41495100022082649440194127)
    ·
      refine ⟨62242650033123974160291191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41495100022082649440194127 62242650033123974160291191)
      ·
        refine ⟨93363975049685961240436787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62242650033123974160291191 93363975049685961240436787)
        ·
          refine ⟨140045962574528941860655181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93363975049685961240436787 140045962574528941860655181)
          ·
            refine ⟨52517235965448353197745693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140045962574528941860655181 52517235965448353197745693)
            ·
              refine ⟨19693963487043132449154635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52517235965448353197745693 19693963487043132449154635)
              ·
                refine ⟨29540945230564698673731953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19693963487043132449154635 29540945230564698673731953)
                ·
                  refine ⟨22155708922923524005298965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29540945230564698673731953 22155708922923524005298965)
                  ·
                    refine ⟨1038548855762040187748389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22155708922923524005298965 1038548855762040187748389)
                    ·
                      rfl

theorem cell22_3033850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_3033850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033850 prefixEnd_3033850 := by exact prefixLift 3033850
  have htrace : WordTrace (prefixWord ++ tailWord_3033850) baseStart_3033850 baseEnd_3033850 := by
    simpa [prefixWord, tailWord_3033850, baseEnd_3033850] using wordTrace_append hprefix tailTrace_3033850
  have hstable : (prefixWord ++ tailWord_3033850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033850).length < 2 ^ (prefixWord ++ tailWord_3033850).sum := by decide
  have hdescent : baseEnd_3033850 < baseStart_3033850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033854 : List Nat := [4, 2, 2, 1, 2, 3, 1, 7]
def baseStart_3033854 : Nat := 118140960795 + 3033854 * 2 ^ 59
def prefixEnd_3033854 : Nat := 4983230072969 + 3 ^ 40 * 3033854 * 2
def baseEnd_3033854 : Nat := 115394469449309501183153

theorem tailTrace_3033854 : CollatzResearch.WordTrace tailWord_3033854 prefixEnd_3033854 115394469449309501183153 := by
  unfold tailWord_3033854
  simp only [CollatzResearch.WordTrace]
  refine ⟨13831718243859071732124577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73769163967248382571331077 13831718243859071732124577)
  ·
    refine ⟨10373788682894303799093433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13831718243859071732124577 10373788682894303799093433)
    ·
      refine ⟨7780341512170727849320075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10373788682894303799093433 7780341512170727849320075)
      ·
        refine ⟨11670512268256091773980113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7780341512170727849320075 11670512268256091773980113)
        ·
          refine ⟨8752884201192068830485085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11670512268256091773980113 8752884201192068830485085)
          ·
            refine ⟨3282331575447025811431907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8752884201192068830485085 3282331575447025811431907)
            ·
              refine ⟨4923497363170538717147861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282331575447025811431907 4923497363170538717147861)
              ·
                refine ⟨115394469449309501183153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4923497363170538717147861 115394469449309501183153)
                ·
                  rfl

theorem cell22_3033854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_3033854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033854 prefixEnd_3033854 := by exact prefixLift 3033854
  have htrace : WordTrace (prefixWord ++ tailWord_3033854) baseStart_3033854 baseEnd_3033854 := by
    simpa [prefixWord, tailWord_3033854, baseEnd_3033854] using wordTrace_append hprefix tailTrace_3033854
  have hstable : (prefixWord ++ tailWord_3033854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033854).length < 2 ^ (prefixWord ++ tailWord_3033854).sum := by decide
  have hdescent : baseEnd_3033854 < baseStart_3033854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033880 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 3, 7]
def baseStart_3033880 : Nat := 118140960795 + 3033880 * 2 ^ 59
def prefixEnd_3033880 : Nat := 4983230072969 + 3 ^ 40 * 3033880 * 2
def baseEnd_3033880 : Nat := 1038559125375130109498297

theorem tailTrace_3033880 : CollatzResearch.WordTrace tailWord_3033880 prefixEnd_3033880 1038559125375130109498297 := by
  unfold tailWord_3033880
  simp only [CollatzResearch.WordTrace]
  refine ⟨55327347124389190148721547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73769796165852253531628729 55327347124389190148721547)
  ·
    refine ⟨82991020686583785223082321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55327347124389190148721547 82991020686583785223082321)
    ·
      refine ⟨62243265514937838917311741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82991020686583785223082321 62243265514937838917311741)
      ·
        refine ⟨23341224568101689593991903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62243265514937838917311741 23341224568101689593991903)
        ·
          refine ⟨35011836852152534390987855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23341224568101689593991903 35011836852152534390987855)
          ·
            refine ⟨52517755278228801586481783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35011836852152534390987855 52517755278228801586481783)
            ·
              refine ⟨78776632917343202379722675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52517755278228801586481783 78776632917343202379722675)
              ·
                refine ⟨118164949376014803569584013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78776632917343202379722675 118164949376014803569584013)
                ·
                  refine ⟨44311856016005551338594005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118164949376014803569584013 44311856016005551338594005)
                  ·
                    refine ⟨1038559125375130109498297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44311856016005551338594005 1038559125375130109498297)
                    ·
                      rfl

theorem cell22_3033880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_3033880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033880 prefixEnd_3033880 := by exact prefixLift 3033880
  have htrace : WordTrace (prefixWord ++ tailWord_3033880) baseStart_3033880 baseEnd_3033880 := by
    simpa [prefixWord, tailWord_3033880, baseEnd_3033880] using wordTrace_append hprefix tailTrace_3033880
  have hstable : (prefixWord ++ tailWord_3033880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033880).length < 2 ^ (prefixWord ++ tailWord_3033880).sum := by decide
  have hdescent : baseEnd_3033880 < baseStart_3033880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033929 : List Nat := [1, 2, 1, 1, 2, 6, 2, 2, 1, 4]
def baseStart_3033929 : Nat := 118140960795 + 3033929 * 2 ^ 59
def prefixEnd_3033929 : Nat := 4983230072969 + 3 ^ 40 * 3033929 * 2
def baseEnd_3033929 : Nat := 1038575899076510315023147

theorem tailTrace_3033929 : CollatzResearch.WordTrace tailWord_3033929 prefixEnd_3033929 1038575899076510315023147 := by
  unfold tailWord_3033929
  simp only [CollatzResearch.WordTrace]
  refine ⟨110656481425600861665976841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73770987617067241110651227 110656481425600861665976841)
  ·
    refine ⟨82992361069200646249482631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110656481425600861665976841 82992361069200646249482631)
    ·
      refine ⟨124488541603800969374223947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82992361069200646249482631 124488541603800969374223947)
      ·
        refine ⟨186732812405701454061335921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124488541603800969374223947 186732812405701454061335921)
        ·
          refine ⟨140049609304276090546001941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186732812405701454061335921 140049609304276090546001941)
          ·
            refine ⟨6564825436137941744343841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140049609304276090546001941 6564825436137941744343841)
            ·
              refine ⟨4923619077103456308257881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6564825436137941744343841 4923619077103456308257881)
              ·
                refine ⟨3692714307827592231193411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4923619077103456308257881 3692714307827592231193411)
                ·
                  refine ⟨5539071461741388346790117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3692714307827592231193411 5539071461741388346790117)
                  ·
                    refine ⟨1038575899076510315023147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5539071461741388346790117 1038575899076510315023147)
                    ·
                      rfl

theorem cell22_3033929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 4].length) (baseStart_3033929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033929 prefixEnd_3033929 := by exact prefixLift 3033929
  have htrace : WordTrace (prefixWord ++ tailWord_3033929) baseStart_3033929 baseEnd_3033929 := by
    simpa [prefixWord, tailWord_3033929, baseEnd_3033929] using wordTrace_append hprefix tailTrace_3033929
  have hstable : (prefixWord ++ tailWord_3033929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033929).length < 2 ^ (prefixWord ++ tailWord_3033929).sum := by decide
  have hdescent : baseEnd_3033929 < baseStart_3033929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033957 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 4, 4]
def baseStart_3033957 : Nat := 118140960795 + 3033957 * 2 ^ 59
def prefixEnd_3033957 : Nat := 4983230072969 + 3 ^ 40 * 3033957 * 2
def baseEnd_3033957 : Nat := 1038585484048727575323061

theorem tailTrace_3033957 : CollatzResearch.WordTrace tailWord_3033957 prefixEnd_3033957 1038585484048727575323061 := by
  unfold tailWord_3033957
  simp only [CollatzResearch.WordTrace]
  refine ⟨110657502669499422447996125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73771668446332948298664083 110657502669499422447996125)
  ·
    refine ⟨41496563501062283417998547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110657502669499422447996125 41496563501062283417998547)
    ·
      refine ⟨62244845251593425126997821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41496563501062283417998547 62244845251593425126997821)
      ·
        refine ⟨23341816969347534422624183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62244845251593425126997821 23341816969347534422624183)
        ·
          refine ⟨35012725454021301633936275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23341816969347534422624183 35012725454021301633936275)
          ·
            refine ⟨52519088181031952450904413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35012725454021301633936275 52519088181031952450904413)
            ·
              refine ⟨19694658067886982169089155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52519088181031952450904413 19694658067886982169089155)
              ·
                refine ⟨29541987101830473253633733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19694658067886982169089155 29541987101830473253633733)
                ·
                  refine ⟨5539122581593213735056325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29541987101830473253633733 5539122581593213735056325)
                  ·
                    refine ⟨1038585484048727575323061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5539122581593213735056325 1038585484048727575323061)
                    ·
                      rfl

theorem cell22_3033957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_3033957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033957 prefixEnd_3033957 := by exact prefixLift 3033957
  have htrace : WordTrace (prefixWord ++ tailWord_3033957) baseStart_3033957 baseEnd_3033957 := by
    simpa [prefixWord, tailWord_3033957, baseEnd_3033957] using wordTrace_append hprefix tailTrace_3033957
  have hstable : (prefixWord ++ tailWord_3033957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033957).length < 2 ^ (prefixWord ++ tailWord_3033957).sum := by decide
  have hdescent : baseEnd_3033957 < baseStart_3033957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033959 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 4, 3]
def baseStart_3033959 : Nat := 118140960795 + 3033959 * 2 ^ 59
def prefixEnd_3033959 : Nat := 4983230072969 + 3 ^ 40 * 3033959 * 2
def baseEnd_3033959 : Nat := 1038586168689600236773055

theorem tailTrace_3033959 : CollatzResearch.WordTrace tailWord_3033959 prefixEnd_3033959 1038586168689600236773055 := by
  unfold tailWord_3033959
  simp only [CollatzResearch.WordTrace]
  refine ⟨110657575615492176789568931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73771717076994784526379287 110657575615492176789568931)
  ·
    refine ⟨165986363423238265184353397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110657575615492176789568931 165986363423238265184353397)
    ·
      refine ⟨15561221570928587361033131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165986363423238265184353397 15561221570928587361033131)
      ·
        refine ⟨23341832356392881041549697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15561221570928587361033131 23341832356392881041549697)
        ·
          refine ⟨17506374267294660781162273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23341832356392881041549697 17506374267294660781162273)
          ·
            refine ⟨13129780700470995585871705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17506374267294660781162273 13129780700470995585871705)
            ·
              refine ⟨9847335525353246689403779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13129780700470995585871705 9847335525353246689403779)
              ·
                refine ⟨14771003288029870034105669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9847335525353246689403779 14771003288029870034105669)
                ·
                  refine ⟨2769563116505600631394813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14771003288029870034105669 2769563116505600631394813)
                  ·
                    refine ⟨1038586168689600236773055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2769563116505600631394813 1038586168689600236773055)
                    ·
                      rfl

theorem cell22_3033959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_3033959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3033959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3033959 prefixEnd_3033959 := by exact prefixLift 3033959
  have htrace : WordTrace (prefixWord ++ tailWord_3033959) baseStart_3033959 baseEnd_3033959 := by
    simpa [prefixWord, tailWord_3033959, baseEnd_3033959] using wordTrace_append hprefix tailTrace_3033959
  have hstable : (prefixWord ++ tailWord_3033959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033959).length < 2 ^ (prefixWord ++ tailWord_3033959).sum := by decide
  have hdescent : baseEnd_3033959 < baseStart_3033959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034006 : List Nat := [5, 3, 1, 1, 1, 11]
def baseStart_3034006 : Nat := 118140960795 + 3034006 * 2 ^ 59
def prefixEnd_3034006 : Nat := 4983230072969 + 3 ^ 40 * 3034006 * 2
def baseEnd_3034006 : Nat := 12822250095680342973431

theorem tailTrace_3034006 : CollatzResearch.WordTrace tailWord_3034006 prefixEnd_3034006 12822250095680342973431 := by
  unfold tailWord_3034006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6916205615395118988533117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73772859897547935877686581 6916205615395118988533117)
  ·
    refine ⟨2593577105773169620699919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6916205615395118988533117 2593577105773169620699919)
    ·
      refine ⟨3890365658659754431049879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2593577105773169620699919 3890365658659754431049879)
      ·
        refine ⟨5835548487989631646574819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3890365658659754431049879 5835548487989631646574819)
        ·
          refine ⟨8753322731984447469862229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5835548487989631646574819 8753322731984447469862229)
          ·
            refine ⟨12822250095680342973431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8753322731984447469862229 12822250095680342973431)
            ·
              rfl

theorem cell22_3034006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 11].length) (baseStart_3034006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034006 prefixEnd_3034006 := by exact prefixLift 3034006
  have htrace : WordTrace (prefixWord ++ tailWord_3034006) baseStart_3034006 baseEnd_3034006 := by
    simpa [prefixWord, tailWord_3034006, baseEnd_3034006] using wordTrace_append hprefix tailTrace_3034006
  have hstable : (prefixWord ++ tailWord_3034006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034006).length < 2 ^ (prefixWord ++ tailWord_3034006).sum := by decide
  have hdescent : baseEnd_3034006 < baseStart_3034006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034109 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_3034109 : Nat := 118140960795 + 3034109 * 2 ^ 59
def prefixEnd_3034109 : Nat := 4983230072969 + 3 ^ 40 * 3034109 * 2
def baseEnd_3034109 : Nat := 1038637516755049845522595

theorem tailTrace_3034109 : CollatzResearch.WordTrace tailWord_3034109 prefixEnd_3034109 1038637516755049845522595 := by
  unfold tailWord_3034109
  simp only [CollatzResearch.WordTrace]
  refine ⟨110663046564948752407529381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73775364376632501605019587 110663046564948752407529381)
  ·
    refine ⟨20749321230927891076411759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110663046564948752407529381 20749321230927891076411759)
    ·
      refine ⟨31123981846391836614617639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20749321230927891076411759 31123981846391836614617639)
      ·
        refine ⟨46685972769587754921926459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31123981846391836614617639 46685972769587754921926459)
        ·
          refine ⟨70028959154381632382889689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46685972769587754921926459 70028959154381632382889689)
          ·
            refine ⟨52521719365786224287167267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70028959154381632382889689 52521719365786224287167267)
            ·
              refine ⟨78782579048679336430750901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52521719365786224287167267 78782579048679336430750901)
              ·
                refine ⟨7385866785813687790382897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78782579048679336430750901 7385866785813687790382897)
                ·
                  refine ⟨5539400089360265842787173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7385866785813687790382897 5539400089360265842787173)
                  ·
                    refine ⟨1038637516755049845522595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5539400089360265842787173 1038637516755049845522595)
                    ·
                      rfl

theorem cell22_3034109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_3034109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034109 prefixEnd_3034109 := by exact prefixLift 3034109
  have htrace : WordTrace (prefixWord ++ tailWord_3034109) baseStart_3034109 baseEnd_3034109 := by
    simpa [prefixWord, tailWord_3034109, baseEnd_3034109] using wordTrace_append hprefix tailTrace_3034109
  have hstable : (prefixWord ++ tailWord_3034109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034109).length < 2 ^ (prefixWord ++ tailWord_3034109).sum := by decide
  have hdescent : baseEnd_3034109 < baseStart_3034109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034113 : List Nat := [1, 2, 4, 1, 2, 4, 1, 3, 4]
def baseStart_3034113 : Nat := 118140960795 + 3034113 * 2 ^ 59
def prefixEnd_3034113 : Nat := 4983230072969 + 3 ^ 40 * 3034113 * 2
def baseEnd_3034113 : Nat := 346212962012265056140861

theorem tailTrace_3034113 : CollatzResearch.WordTrace tailWord_3034113 prefixEnd_3034113 346212962012265056140861 := by
  unfold tailWord_3034113
  simp only [CollatzResearch.WordTrace]
  refine ⟨110663192456934261090674993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73775461637956174060449995 110663192456934261090674993)
  ·
    refine ⟨82997394342700695818006245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110663192456934261090674993 82997394342700695818006245)
    ·
      refine ⟨15562011439256380465876171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82997394342700695818006245 15562011439256380465876171)
      ·
        refine ⟨23343017158884570698814257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15562011439256380465876171 23343017158884570698814257)
        ·
          refine ⟨17507262869163428024110693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23343017158884570698814257 17507262869163428024110693)
          ·
            refine ⟨3282611787968142754520755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17507262869163428024110693 3282611787968142754520755)
            ·
              refine ⟨4923917681952214131781133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282611787968142754520755 4923917681952214131781133)
              ·
                refine ⟨1846469130732080299417925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4923917681952214131781133 1846469130732080299417925)
                ·
                  refine ⟨346212962012265056140861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1846469130732080299417925 346212962012265056140861)
                  ·
                    rfl

theorem cell22_3034113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 4].length) (baseStart_3034113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034113 prefixEnd_3034113 := by exact prefixLift 3034113
  have htrace : WordTrace (prefixWord ++ tailWord_3034113) baseStart_3034113 baseEnd_3034113 := by
    simpa [prefixWord, tailWord_3034113, baseEnd_3034113] using wordTrace_append hprefix tailTrace_3034113
  have hstable : (prefixWord ++ tailWord_3034113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034113).length < 2 ^ (prefixWord ++ tailWord_3034113).sum := by decide
  have hdescent : baseEnd_3034113 < baseStart_3034113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034124 : List Nat := [2, 2, 1, 2, 3, 4, 8]
def baseStart_3034124 : Nat := 118140960795 + 3034124 * 2 ^ 59
def prefixEnd_3034124 : Nat := 4983230072969 + 3 ^ 40 * 3034124 * 2
def baseEnd_3034124 : Nat := 38468246354133140977687

theorem tailTrace_3034124 : CollatzResearch.WordTrace tailWord_3034124 prefixEnd_3034124 38468246354133140977687 := by
  unfold tailWord_3034124
  simp only [CollatzResearch.WordTrace]
  refine ⟨55331796829947204984662713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73775729106596273312883617 55331796829947204984662713)
  ·
    refine ⟨41498847622460403738497035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55331796829947204984662713 41498847622460403738497035)
    ·
      refine ⟨62248271433690605607745553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41498847622460403738497035 62248271433690605607745553)
      ·
        refine ⟨46686203575267954205809165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62248271433690605607745553 46686203575267954205809165)
        ·
          refine ⟨17507326340725482827178437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46686203575267954205809165 17507326340725482827178437)
          ·
            refine ⟨3282623688886028030095957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17507326340725482827178437 3282623688886028030095957)
            ·
              refine ⟨38468246354133140977687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3282623688886028030095957 38468246354133140977687)
              ·
                rfl

theorem cell22_3034124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 8].length) (baseStart_3034124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034124 prefixEnd_3034124 := by exact prefixLift 3034124
  have htrace : WordTrace (prefixWord ++ tailWord_3034124) baseStart_3034124 baseEnd_3034124 := by
    simpa [prefixWord, tailWord_3034124, baseEnd_3034124] using wordTrace_append hprefix tailTrace_3034124
  have hstable : (prefixWord ++ tailWord_3034124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034124).length < 2 ^ (prefixWord ++ tailWord_3034124).sum := by decide
  have hdescent : baseEnd_3034124 < baseStart_3034124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034126 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_3034126 : Nat := 118140960795 + 3034126 * 2 ^ 59
def prefixEnd_3034126 : Nat := 4983230072969 + 3 ^ 40 * 3034126 * 2
def baseEnd_3034126 : Nat := 1038643336202467467847543

theorem tailTrace_3034126 : CollatzResearch.WordTrace tailWord_3034126 prefixEnd_3034126 1038643336202467467847543 := by
  unfold tailWord_3034126
  simp only [CollatzResearch.WordTrace]
  refine ⟨13832958325735895538862279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73775777737258109540598821 13832958325735895538862279)
  ·
    refine ⟨20749437488603843308293419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13832958325735895538862279 20749437488603843308293419)
    ·
      refine ⟨31124156232905764962440129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20749437488603843308293419 31124156232905764962440129)
      ·
        refine ⟨23343117174679323721830097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31124156232905764962440129 23343117174679323721830097)
        ·
          refine ⟨17507337881009492791372573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23343117174679323721830097 17507337881009492791372573)
          ·
            refine ⟨6565251705378559796764715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17507337881009492791372573 6565251705378559796764715)
            ·
              refine ⟨9847877558067839695147073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6565251705378559796764715 9847877558067839695147073)
              ·
                refine ⟨7385908168550879771360305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9847877558067839695147073 7385908168550879771360305)
                ·
                  refine ⟨5539431126413159828520229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7385908168550879771360305 5539431126413159828520229)
                  ·
                    refine ⟨1038643336202467467847543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5539431126413159828520229 1038643336202467467847543)
                    ·
                      rfl

theorem cell22_3034126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_3034126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034126 prefixEnd_3034126 := by exact prefixLift 3034126
  have htrace : WordTrace (prefixWord ++ tailWord_3034126) baseStart_3034126 baseEnd_3034126 := by
    simpa [prefixWord, tailWord_3034126, baseEnd_3034126] using wordTrace_append hprefix tailTrace_3034126
  have hstable : (prefixWord ++ tailWord_3034126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034126).length < 2 ^ (prefixWord ++ tailWord_3034126).sum := by decide
  have hdescent : baseEnd_3034126 < baseStart_3034126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034141 : List Nat := [1, 4, 2, 2, 3, 1, 2, 7]
def baseStart_3034141 : Nat := 118140960795 + 3034141 * 2 ^ 59
def prefixEnd_3034141 : Nat := 4983230072969 + 3 ^ 40 * 3034141 * 2
def baseEnd_3034141 : Nat := 115405385667668047635833

theorem tailTrace_3034141 : CollatzResearch.WordTrace tailWord_3034141 prefixEnd_3034141 115405385667668047635833 := by
  unfold tailWord_3034141
  simp only [CollatzResearch.WordTrace]
  refine ⟨110664213700832821872694277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73776142467221881248462851 110664213700832821872694277)
  ·
    refine ⟨20749540068906154101130177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110664213700832821872694277 20749540068906154101130177)
    ·
      refine ⟨15562155051679615575847633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20749540068906154101130177 15562155051679615575847633)
      ·
        refine ⟨11671616288759711681885725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15562155051679615575847633 11671616288759711681885725)
        ·
          refine ⟨4376856108284891880707147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11671616288759711681885725 4376856108284891880707147)
          ·
            refine ⟨6565284162427337821060721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4376856108284891880707147 6565284162427337821060721)
            ·
              refine ⟨4923963121820503365795541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6565284162427337821060721 4923963121820503365795541)
              ·
                refine ⟨115405385667668047635833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4923963121820503365795541 115405385667668047635833)
                ·
                  rfl

theorem cell22_3034141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 7].length) (baseStart_3034141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034141 prefixEnd_3034141 := by exact prefixLift 3034141
  have htrace : WordTrace (prefixWord ++ tailWord_3034141) baseStart_3034141 baseEnd_3034141 := by
    simpa [prefixWord, tailWord_3034141, baseEnd_3034141] using wordTrace_append hprefix tailTrace_3034141
  have hstable : (prefixWord ++ tailWord_3034141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034141).length < 2 ^ (prefixWord ++ tailWord_3034141).sum := by decide
  have hdescent : baseEnd_3034141 < baseStart_3034141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034145 : List Nat := [1, 2, 3, 2, 3, 3, 2, 1, 2, 3]
def baseStart_3034145 : Nat := 118140960795 + 3034145 * 2 ^ 59
def prefixEnd_3034145 : Nat := 4983230072969 + 3 ^ 40 * 3034145 * 2
def baseEnd_3034145 : Nat := 1038649840290757751622485

theorem tailTrace_3034145 : CollatzResearch.WordTrace tailWord_3034145 prefixEnd_3034145 1038649840290757751622485 := by
  unfold tailWord_3034145
  simp only [CollatzResearch.WordTrace]
  refine ⟨110664359592818330555839889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73776239728545553703893259 110664359592818330555839889)
  ·
    refine ⟨82998269694613747916879917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110664359592818330555839889 82998269694613747916879917)
    ·
      refine ⟨31124351135480155468829969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82998269694613747916879917 31124351135480155468829969)
      ·
        refine ⟨23343263351610116601622477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31124351135480155468829969 23343263351610116601622477)
        ·
          refine ⟨8753723756853793725608429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23343263351610116601622477 8753723756853793725608429)
          ·
            refine ⟨3282646408820172647103161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8753723756853793725608429 3282646408820172647103161)
            ·
              refine ⟨2461984806615129485327371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3282646408820172647103161 2461984806615129485327371)
              ·
                refine ⟨3692977209922694227991057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2461984806615129485327371 3692977209922694227991057)
                ·
                  refine ⟨2769732907442020670993293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3692977209922694227991057 2769732907442020670993293)
                  ·
                    refine ⟨1038649840290757751622485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2769732907442020670993293 1038649840290757751622485)
                    ·
                      rfl

theorem cell22_3034145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_3034145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034145 prefixEnd_3034145 := by exact prefixLift 3034145
  have htrace : WordTrace (prefixWord ++ tailWord_3034145) baseStart_3034145 baseEnd_3034145 := by
    simpa [prefixWord, tailWord_3034145, baseEnd_3034145] using wordTrace_append hprefix tailTrace_3034145
  have hstable : (prefixWord ++ tailWord_3034145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034145).length < 2 ^ (prefixWord ++ tailWord_3034145).sum := by decide
  have hdescent : baseEnd_3034145 < baseStart_3034145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034184 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 2, 5]
def baseStart_3034184 : Nat := 118140960795 + 3034184 * 2 ^ 59
def prefixEnd_3034184 : Nat := 4983230072969 + 3 ^ 40 * 3034184 * 2
def baseEnd_3034184 : Nat := 1038663190787774649897365

theorem tailTrace_3034184 : CollatzResearch.WordTrace tailWord_3034184 prefixEnd_3034184 1038663190787774649897365 := by
  unfold tailWord_3034184
  simp only [CollatzResearch.WordTrace]
  refine ⟨55332891019838520108254803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73777188026451360144339737 55332891019838520108254803)
  ·
    refine ⟨82999336529757780162382205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55332891019838520108254803 82999336529757780162382205)
    ·
      refine ⟨31124751198659167560893327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82999336529757780162382205 31124751198659167560893327)
      ·
        refine ⟨46687126797988751341339991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31124751198659167560893327 46687126797988751341339991)
        ·
          refine ⟨70030690196983127012009987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46687126797988751341339991 70030690196983127012009987)
          ·
            refine ⟨105046035295474690518014981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70030690196983127012009987 105046035295474690518014981)
            ·
              refine ⟨19696131617901504472127809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105046035295474690518014981 19696131617901504472127809)
              ·
                refine ⟨14772098713426128354095857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19696131617901504472127809 14772098713426128354095857)
                ·
                  refine ⟨11079074035069596265571893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14772098713426128354095857 11079074035069596265571893)
                  ·
                    refine ⟨1038663190787774649897365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11079074035069596265571893 1038663190787774649897365)
                    ·
                      rfl

theorem cell22_3034184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_3034184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034184 prefixEnd_3034184 := by exact prefixLift 3034184
  have htrace : WordTrace (prefixWord ++ tailWord_3034184) baseStart_3034184 baseEnd_3034184 := by
    simpa [prefixWord, tailWord_3034184, baseEnd_3034184] using wordTrace_append hprefix tailTrace_3034184
  have hstable : (prefixWord ++ tailWord_3034184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034184).length < 2 ^ (prefixWord ++ tailWord_3034184).sum := by decide
  have hdescent : baseEnd_3034184 < baseStart_3034184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034233 : List Nat := [1, 2, 1, 3, 5, 1, 1, 3, 1, 4]
def baseStart_3034233 : Nat := 118140960795 + 3034233 * 2 ^ 59
def prefixEnd_3034233 : Nat := 4983230072969 + 3 ^ 40 * 3034233 * 2
def baseEnd_3034233 : Nat := 1038679964489154855422215

theorem tailTrace_3034233 : CollatzResearch.WordTrace tailWord_3034233 prefixEnd_3034233 1038679964489154855422215 := by
  unfold tailWord_3034233
  simp only [CollatzResearch.WordTrace]
  refine ⟨110667569216499521585043353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73778379477666347723362235 110667569216499521585043353)
  ·
    refine ⟨83000676912374641188782515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110667569216499521585043353 83000676912374641188782515)
    ·
      refine ⟨124501015368561961783173773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83000676912374641188782515 124501015368561961783173773)
      ·
        refine ⟨46687880763210735668690165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124501015368561961783173773 46687880763210735668690165)
        ·
          refine ⟨4376988821551006468939703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46687880763210735668690165 4376988821551006468939703)
          ·
            refine ⟨6565483232326509703409555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4376988821551006468939703 6565483232326509703409555)
            ·
              refine ⟨9848224848489764555114333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6565483232326509703409555 9848224848489764555114333)
              ·
                refine ⟨3693084318183661708167875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9848224848489764555114333 3693084318183661708167875)
                ·
                  refine ⟨5539626477275492562251813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3693084318183661708167875 5539626477275492562251813)
                  ·
                    refine ⟨1038679964489154855422215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5539626477275492562251813 1038679964489154855422215)
                    ·
                      rfl

theorem cell22_3034233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 4].length) (baseStart_3034233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034233 prefixEnd_3034233 := by exact prefixLift 3034233
  have htrace : WordTrace (prefixWord ++ tailWord_3034233) baseStart_3034233 baseEnd_3034233 := by
    simpa [prefixWord, tailWord_3034233, baseEnd_3034233] using wordTrace_append hprefix tailTrace_3034233
  have hstable : (prefixWord ++ tailWord_3034233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034233).length < 2 ^ (prefixWord ++ tailWord_3034233).sum := by decide
  have hdescent : baseEnd_3034233 < baseStart_3034233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034248 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 6]
def baseStart_3034248 : Nat := 118140960795 + 3034248 * 2 ^ 59
def prefixEnd_3034248 : Nat := 4983230072969 + 3 ^ 40 * 3034248 * 2
def baseEnd_3034248 : Nat := 346228366431899938765723

theorem tailTrace_3034248 : CollatzResearch.WordTrace tailWord_3034248 prefixEnd_3034248 346228366431899938765723 := by
  unfold tailWord_3034248
  simp only [CollatzResearch.WordTrace]
  refine ⟨55334058155722589573419699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73778744207630119431226265 55334058155722589573419699)
  ·
    refine ⟨83001087233583884360129549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55334058155722589573419699 83001087233583884360129549)
    ·
      refine ⟨31125407712593956635048581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83001087233583884360129549 31125407712593956635048581)
      ·
        refine ⟨5836013946111366869071609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31125407712593956635048581 5836013946111366869071609)
        ·
          refine ⟨4377010459583525151803707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5836013946111366869071609 4377010459583525151803707)
          ·
            refine ⟨6565515689375287727705561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377010459583525151803707 6565515689375287727705561)
            ·
              refine ⟨4924136767031465795779171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6565515689375287727705561 4924136767031465795779171)
              ·
                refine ⟨7386205150547198693668757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4924136767031465795779171 7386205150547198693668757)
                ·
                  refine ⟨346228366431899938765723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7386205150547198693668757 346228366431899938765723)
                  ·
                    rfl

theorem cell22_3034248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 6].length) (baseStart_3034248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034248 prefixEnd_3034248 := by exact prefixLift 3034248
  have htrace : WordTrace (prefixWord ++ tailWord_3034248) baseStart_3034248 baseEnd_3034248 := by
    simpa [prefixWord, tailWord_3034248, baseEnd_3034248] using wordTrace_append hprefix tailTrace_3034248
  have hstable : (prefixWord ++ tailWord_3034248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034248).length < 2 ^ (prefixWord ++ tailWord_3034248).sum := by decide
  have hdescent : baseEnd_3034248 < baseStart_3034248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034263 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 1, 5]
def baseStart_3034263 : Nat := 118140960795 + 3034263 * 2 ^ 59
def prefixEnd_3034263 : Nat := 4983230072969 + 3 ^ 40 * 3034263 * 2
def baseEnd_3034263 : Nat := 1038690234102244777172123

theorem tailTrace_3034263 : CollatzResearch.WordTrace tailWord_3034263 prefixEnd_3034263 1038690234102244777172123 := by
  unfold tailWord_3034263
  simp only [CollatzResearch.WordTrace]
  refine ⟨110668663406390836708635443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73779108937593891139090295 110668663406390836708635443)
  ·
    refine ⟨166002995109586255062953165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110668663406390836708635443 166002995109586255062953165)
    ·
      refine ⟨62251123166094845648607437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166002995109586255062953165 62251123166094845648607437)
      ·
        refine ⟨23344171187285567118227789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62251123166094845648607437 23344171187285567118227789)
        ·
          refine ⟨8754064195232087669335421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23344171187285567118227789 8754064195232087669335421)
          ·
            refine ⟨3282774073212032876000783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8754064195232087669335421 3282774073212032876000783)
            ·
              refine ⟨4924161109818049314001175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282774073212032876000783 4924161109818049314001175)
              ·
                refine ⟨7386241664727073971001763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4924161109818049314001175 7386241664727073971001763)
                ·
                  refine ⟨11079362497090610956502645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7386241664727073971001763 11079362497090610956502645)
                  ·
                    refine ⟨1038690234102244777172123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11079362497090610956502645 1038690234102244777172123)
                    ·
                      rfl

theorem cell22_3034263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_3034263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034263 prefixEnd_3034263 := by exact prefixLift 3034263
  have htrace : WordTrace (prefixWord ++ tailWord_3034263) baseStart_3034263 baseEnd_3034263 := by
    simpa [prefixWord, tailWord_3034263, baseEnd_3034263] using wordTrace_append hprefix tailTrace_3034263
  have hstable : (prefixWord ++ tailWord_3034263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034263).length < 2 ^ (prefixWord ++ tailWord_3034263).sum := by decide
  have hdescent : baseEnd_3034263 < baseStart_3034263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034276 : List Nat := [2, 3, 1, 2, 3, 2, 1, 8]
def baseStart_3034276 : Nat := 118140960795 + 3034276 * 2 ^ 59
def prefixEnd_3034276 : Nat := 4983230072969 + 3 ^ 40 * 3034276 * 2
def baseEnd_3034276 : Nat := 115410520474213008510787

theorem tailTrace_3034276 : CollatzResearch.WordTrace tailWord_3034276 prefixEnd_3034276 115410520474213008510787 := by
  unfold tailWord_3034276
  simp only [CollatzResearch.WordTrace]
  refine ⟨55334568777671869964429341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73779425036895826619239121 55334568777671869964429341)
  ·
    refine ⟨20750463291626951236661003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55334568777671869964429341 20750463291626951236661003)
    ·
      refine ⟨31125694937440426854991505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20750463291626951236661003 31125694937440426854991505)
      ·
        refine ⟨23344271203080320141243629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31125694937440426854991505 23344271203080320141243629)
        ·
          refine ⟨8754101701155120052966361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23344271203080320141243629 8754101701155120052966361)
          ·
            refine ⟨6565576275866340039724771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8754101701155120052966361 6565576275866340039724771)
            ·
              refine ⟨9848364413799510059587157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6565576275866340039724771 9848364413799510059587157)
              ·
                refine ⟨115410520474213008510787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9848364413799510059587157 115410520474213008510787)
                ·
                  rfl

theorem cell22_3034276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 8].length) (baseStart_3034276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034276 prefixEnd_3034276 := by exact prefixLift 3034276
  have htrace : WordTrace (prefixWord ++ tailWord_3034276) baseStart_3034276 baseEnd_3034276 := by
    simpa [prefixWord, tailWord_3034276, baseEnd_3034276] using wordTrace_append hprefix tailTrace_3034276
  have hstable : (prefixWord ++ tailWord_3034276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034276).length < 2 ^ (prefixWord ++ tailWord_3034276).sum := by decide
  have hdescent : baseEnd_3034276 < baseStart_3034276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034282 : List Nat := [3, 1, 5, 1, 1, 3, 1, 3, 4]
def baseStart_3034282 : Nat := 118140960795 + 3034282 * 2 ^ 59
def prefixEnd_3034282 : Nat := 4983230072969 + 3 ^ 40 * 3034282 * 2
def baseEnd_3034282 : Nat := 346232246063511686982355

theorem tailTrace_3034282 : CollatzResearch.WordTrace tailWord_3034282 prefixEnd_3034282 346232246063511686982355 := by
  unfold tailWord_3034282
  simp only [CollatzResearch.WordTrace]
  refine ⟨27667339098330500738394275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73779570928881335302384733 27667339098330500738394275)
  ·
    refine ⟨41501008647495751107591413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27667339098330500738394275 41501008647495751107591413)
    ·
      refine ⟨3890719560702726666336695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41501008647495751107591413 3890719560702726666336695)
      ·
        refine ⟨5836079341054089999505043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3890719560702726666336695 5836079341054089999505043)
        ·
          refine ⟨8754119011581134999257565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5836079341054089999505043 8754119011581134999257565)
          ·
            refine ⟨3282794629342925624721587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8754119011581134999257565 3282794629342925624721587)
            ·
              refine ⟨4924191944014388437082381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282794629342925624721587 4924191944014388437082381)
              ·
                refine ⟨1846571979005395663905893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4924191944014388437082381 1846571979005395663905893)
                ·
                  refine ⟨346232246063511686982355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1846571979005395663905893 346232246063511686982355)
                  ·
                    rfl

theorem cell22_3034282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_3034282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034282 prefixEnd_3034282 := by exact prefixLift 3034282
  have htrace : WordTrace (prefixWord ++ tailWord_3034282) baseStart_3034282 baseEnd_3034282 := by
    simpa [prefixWord, tailWord_3034282, baseEnd_3034282] using wordTrace_append hprefix tailTrace_3034282
  have hstable : (prefixWord ++ tailWord_3034282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034282).length < 2 ^ (prefixWord ++ tailWord_3034282).sum := by decide
  have hdescent : baseEnd_3034282 < baseStart_3034282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034291 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 5, 3]
def baseStart_3034291 : Nat := 118140960795 + 3034291 * 2 ^ 59
def prefixEnd_3034291 : Nat := 4983230072969 + 3 ^ 40 * 3034291 * 2
def baseEnd_3034291 : Nat := 1038699819074462037472037

theorem tailTrace_3034291 : CollatzResearch.WordTrace tailWord_3034291 prefixEnd_3034291 1038699819074462037472037 := by
  unfold tailWord_3034291
  simp only [CollatzResearch.WordTrace]
  refine ⟨110669684650289397490654727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73779789766859598327103151 110669684650289397490654727)
  ·
    refine ⟨166004526975434096235982091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110669684650289397490654727 166004526975434096235982091)
    ·
      refine ⟨249006790463151144353973137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166004526975434096235982091 249006790463151144353973137)
      ·
        refine ⟨186755092847363358265479853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249006790463151144353973137 186755092847363358265479853)
        ·
          refine ⟨70033159817761259349554945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186755092847363358265479853 70033159817761259349554945)
          ·
            refine ⟨52524869863320944512166209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70033159817761259349554945 52524869863320944512166209)
            ·
              refine ⟨39393652397490708384124657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52524869863320944512166209 39393652397490708384124657)
              ·
                refine ⟨29545239298118031288093493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39393652397490708384124657 29545239298118031288093493)
                ·
                  refine ⟨2769866184198565433258765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29545239298118031288093493 2769866184198565433258765)
                  ·
                    refine ⟨1038699819074462037472037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2769866184198565433258765 1038699819074462037472037)
                    ·
                      rfl

theorem cell22_3034291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 3].length) (baseStart_3034291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034291 prefixEnd_3034291 := by exact prefixLift 3034291
  have htrace : WordTrace (prefixWord ++ tailWord_3034291) baseStart_3034291 baseEnd_3034291 := by
    simpa [prefixWord, tailWord_3034291, baseEnd_3034291] using wordTrace_append hprefix tailTrace_3034291
  have hstable : (prefixWord ++ tailWord_3034291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034291).length < 2 ^ (prefixWord ++ tailWord_3034291).sum := by decide
  have hdescent : baseEnd_3034291 < baseStart_3034291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034370 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3034370 : Nat := 118140960795 + 3034370 * 2 ^ 59
def prefixEnd_3034370 : Nat := 4983230072969 + 3 ^ 40 * 3034370 * 2
def baseEnd_3034370 : Nat := 1038726862388932164746795

theorem tailTrace_3034370 : CollatzResearch.WordTrace tailWord_3034370 prefixEnd_3034370 1038726862388932164746795 := by
  unfold tailWord_3034370
  simp only [CollatzResearch.WordTrace]
  refine ⟨27668141504250798495695141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73781710678002129321853709 27668141504250798495695141)
  ·
    refine ⟨5187776532047024717942839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27668141504250798495695141 5187776532047024717942839)
    ·
      refine ⟨7781664798070537076914259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5187776532047024717942839 7781664798070537076914259)
      ·
        refine ⟨11672497197105805615371389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7781664798070537076914259 11672497197105805615371389)
        ·
          refine ⟨4377186448914677105764271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11672497197105805615371389 4377186448914677105764271)
          ·
            refine ⟨6565779673372015658646407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377186448914677105764271 6565779673372015658646407)
            ·
              refine ⟨9848669510058023487969611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6565779673372015658646407 9848669510058023487969611)
              ·
                refine ⟨14773004265087035231954417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9848669510058023487969611 14773004265087035231954417)
                ·
                  refine ⟨11079753198815276423965813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14773004265087035231954417 11079753198815276423965813)
                  ·
                    refine ⟨1038726862388932164746795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11079753198815276423965813 1038726862388932164746795)
                    ·
                      rfl

theorem cell22_3034370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3034370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034370 prefixEnd_3034370 := by exact prefixLift 3034370
  have htrace : WordTrace (prefixWord ++ tailWord_3034370) baseStart_3034370 baseEnd_3034370 := by
    simpa [prefixWord, tailWord_3034370, baseEnd_3034370] using wordTrace_append hprefix tailTrace_3034370
  have hstable : (prefixWord ++ tailWord_3034370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034370).length < 2 ^ (prefixWord ++ tailWord_3034370).sum := by decide
  have hdescent : baseEnd_3034370 < baseStart_3034370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034441 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 2, 6]
def baseStart_3034441 : Nat := 118140960795 + 3034441 * 2 ^ 59
def prefixEnd_3034441 : Nat := 4983230072969 + 3 ^ 40 * 3034441 * 2
def baseEnd_3034441 : Nat := 1038751167139911646221577

theorem tailTrace_3034441 : CollatzResearch.WordTrace tailWord_3034441 prefixEnd_3034441 1038751167139911646221577 := by
  unfold tailWord_3034441
  simp only [CollatzResearch.WordTrace]
  refine ⟨110675155599745973108615177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73783437066497315405743451 110675155599745973108615177)
  ·
    refine ⟨83006366699809479831461383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110675155599745973108615177 83006366699809479831461383)
    ·
      refine ⟨124509550049714219747192075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83006366699809479831461383 124509550049714219747192075)
      ·
        refine ⟨186764325074571329620788113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124509550049714219747192075 186764325074571329620788113)
        ·
          refine ⟨140073243805928497215591085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186764325074571329620788113 140073243805928497215591085)
          ·
            refine ⟨52527466427223186455846657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140073243805928497215591085 52527466427223186455846657)
            ·
              refine ⟨39395599820417389841884993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52527466427223186455846657 39395599820417389841884993)
              ·
                refine ⟨29546699865313042381413745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39395599820417389841884993 29546699865313042381413745)
                ·
                  refine ⟨22160024898984781786060309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29546699865313042381413745 22160024898984781786060309)
                  ·
                    refine ⟨1038751167139911646221577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22160024898984781786060309 1038751167139911646221577)
                    ·
                      rfl

theorem cell22_3034441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_3034441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034441 prefixEnd_3034441 := by exact prefixLift 3034441
  have htrace : WordTrace (prefixWord ++ tailWord_3034441) baseStart_3034441 baseEnd_3034441 := by
    simpa [prefixWord, tailWord_3034441, baseEnd_3034441] using wordTrace_append hprefix tailTrace_3034441
  have hstable : (prefixWord ++ tailWord_3034441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034441).length < 2 ^ (prefixWord ++ tailWord_3034441).sum := by decide
  have hdescent : baseEnd_3034441 < baseStart_3034441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034456 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 9]
def baseStart_3034456 : Nat := 118140960795 + 3034456 * 2 ^ 59
def prefixEnd_3034456 : Nat := 4983230072969 + 3 ^ 40 * 3034456 * 2
def baseEnd_3034456 : Nat := 346252100648818869032177

theorem tailTrace_3034456 : CollatzResearch.WordTrace tailWord_3034456 prefixEnd_3034456 346252100648818869032177 := by
  unfold tailWord_3034456
  simp only [CollatzResearch.WordTrace]
  refine ⟨55337851347345815335205611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73783801796461087113607481 55337851347345815335205611)
  ·
    refine ⟨83006777021018723002808417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55337851347345815335205611 83006777021018723002808417)
    ·
      refine ⟨62255082765764042252106313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83006777021018723002808417 62255082765764042252106313)
      ·
        refine ⟨46691312074323031689079735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62255082765764042252106313 46691312074323031689079735)
        ·
          refine ⟨70036968111484547533619603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46691312074323031689079735 70036968111484547533619603)
          ·
            refine ⟨105055452167226821300429405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70036968111484547533619603 105055452167226821300429405)
            ·
              refine ⟨39395794562710057987661027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105055452167226821300429405 39395794562710057987661027)
              ·
                refine ⟨59093691844065086981491541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39395794562710057987661027 59093691844065086981491541)
                ·
                  refine ⟨346252100648818869032177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59093691844065086981491541 346252100648818869032177)
                  ·
                    rfl

theorem cell22_3034456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 9].length) (baseStart_3034456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034456 prefixEnd_3034456 := by exact prefixLift 3034456
  have htrace : WordTrace (prefixWord ++ tailWord_3034456) baseStart_3034456 baseEnd_3034456 := by
    simpa [prefixWord, tailWord_3034456, baseEnd_3034456] using wordTrace_append hprefix tailTrace_3034456
  have hstable : (prefixWord ++ tailWord_3034456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034456).length < 2 ^ (prefixWord ++ tailWord_3034456).sum := by decide
  have hdescent : baseEnd_3034456 < baseStart_3034456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034477 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_3034477 : Nat := 118140960795 + 3034477 * 2 ^ 59
def prefixEnd_3034477 : Nat := 4983230072969 + 3 ^ 40 * 3034477 * 2
def baseEnd_3034477 : Nat := 1038763490675619552321467

theorem tailTrace_3034477 : CollatzResearch.WordTrace tailWord_3034477 prefixEnd_3034477 1038763490675619552321467 := by
  unfold tailWord_3034477
  simp only [CollatzResearch.WordTrace]
  refine ⟨110676468627615551256925685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73784312418410367504617123 110676468627615551256925685)
  ·
    refine ⟨10375918933838957930336783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110676468627615551256925685 10375918933838957930336783)
    ·
      refine ⟨15563878400758436895505175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10375918933838957930336783 15563878400758436895505175)
      ·
        refine ⟨23345817601137655343257763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15563878400758436895505175 23345817601137655343257763)
        ·
          refine ⟨35018726401706483014886645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23345817601137655343257763 35018726401706483014886645)
          ·
            refine ⟨3283005600159982782645623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35018726401706483014886645 3283005600159982782645623)
            ·
              refine ⟨4924508400239974173968435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3283005600159982782645623 4924508400239974173968435)
              ·
                refine ⟨7386762600359961260952653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4924508400239974173968435 7386762600359961260952653)
                ·
                  refine ⟨2770035975134985472857245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7386762600359961260952653 2770035975134985472857245)
                  ·
                    refine ⟨1038763490675619552321467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2770035975134985472857245 1038763490675619552321467)
                    ·
                      rfl

theorem cell22_3034477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_3034477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034477 prefixEnd_3034477 := by exact prefixLift 3034477
  have htrace : WordTrace (prefixWord ++ tailWord_3034477) baseStart_3034477 baseEnd_3034477 := by
    simpa [prefixWord, tailWord_3034477, baseEnd_3034477] using wordTrace_append hprefix tailTrace_3034477
  have hstable : (prefixWord ++ tailWord_3034477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034477).length < 2 ^ (prefixWord ++ tailWord_3034477).sum := by decide
  have hdescent : baseEnd_3034477 < baseStart_3034477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034580 : List Nat := [2, 4, 1, 2, 3, 1, 9]
def baseStart_3034580 : Nat := 118140960795 + 3034580 * 2 ^ 59
def prefixEnd_3034580 : Nat := 4983230072969 + 3 ^ 40 * 3034580 * 2
def baseEnd_3034580 : Nat := 38474027765946726555413

theorem tailTrace_3034580 : CollatzResearch.WordTrace tailWord_3034580 prefixEnd_3034580 38474027765946726555413 := by
  unfold tailWord_3034580
  simp only [CollatzResearch.WordTrace]
  refine ⟨55340112673121199923962597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73786816897494933231950129 55340112673121199923962597)
  ·
    refine ⟨10376271126210224985742987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55340112673121199923962597 10376271126210224985742987)
    ·
      refine ⟨15564406689315337478614481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10376271126210224985742987 15564406689315337478614481)
      ·
        refine ⟨11673305016986503108960861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15564406689315337478614481 11673305016986503108960861)
        ·
          refine ⟨4377489381369938665860323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11673305016986503108960861 4377489381369938665860323)
          ·
            refine ⟨6566234072054907998790485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377489381369938665860323 6566234072054907998790485)
            ·
              refine ⟨38474027765946726555413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6566234072054907998790485 38474027765946726555413)
              ·
                rfl

theorem cell22_3034580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 9].length) (baseStart_3034580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034580 prefixEnd_3034580 := by exact prefixLift 3034580
  have htrace : WordTrace (prefixWord ++ tailWord_3034580) baseStart_3034580 baseEnd_3034580 := by
    simpa [prefixWord, tailWord_3034580, baseEnd_3034580] using wordTrace_append hprefix tailTrace_3034580
  have hstable : (prefixWord ++ tailWord_3034580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034580).length < 2 ^ (prefixWord ++ tailWord_3034580).sum := by decide
  have hdescent : baseEnd_3034580 < baseStart_3034580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034623 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 4, 5]
def baseStart_3034623 : Nat := 118140960795 + 3034623 * 2 ^ 59
def prefixEnd_3034623 : Nat := 4983230072969 + 3 ^ 40 * 3034623 * 2
def baseEnd_3034623 : Nat := 1038813469459323838171019

theorem tailTrace_3034623 : CollatzResearch.WordTrace tailWord_3034623 prefixEnd_3034623 1038813469459323838171019 := by
  unfold tailWord_3034623
  simp only [CollatzResearch.WordTrace]
  refine ⟨110681793685086618191740523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73787862456724412127827015 110681793685086618191740523)
  ·
    refine ⟨166022690527629927287610785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110681793685086618191740523 166022690527629927287610785)
    ·
      refine ⟨124517017895722445465708089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166022690527629927287610785 124517017895722445465708089)
      ·
        refine ⟨93387763421791834099281067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124517017895722445465708089 93387763421791834099281067)
        ·
          refine ⟨140081645132687751148921601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93387763421791834099281067 140081645132687751148921601)
          ·
            refine ⟨105061233849515813361691201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140081645132687751148921601 105061233849515813361691201)
            ·
              refine ⟨78795925387136860021268401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105061233849515813361691201 78795925387136860021268401)
              ·
                refine ⟨59096944040352645015951301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78795925387136860021268401 59096944040352645015951301)
                ·
                  refine ⟨11080677007566120940490869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59096944040352645015951301 11080677007566120940490869)
                  ·
                    refine ⟨1038813469459323838171019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11080677007566120940490869 1038813469459323838171019)
                    ·
                      rfl

theorem cell22_3034623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_3034623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034623 prefixEnd_3034623 := by exact prefixLift 3034623
  have htrace : WordTrace (prefixWord ++ tailWord_3034623) baseStart_3034623 baseEnd_3034623 := by
    simpa [prefixWord, tailWord_3034623, baseEnd_3034623] using wordTrace_append hprefix tailTrace_3034623
  have hstable : (prefixWord ++ tailWord_3034623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034623).length < 2 ^ (prefixWord ++ tailWord_3034623).sum := by decide
  have hdescent : baseEnd_3034623 < baseStart_3034623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034659 : List Nat := [1, 1, 1, 4, 5, 2, 2, 1, 5]
def baseStart_3034659 : Nat := 118140960795 + 3034659 * 2 ^ 59
def prefixEnd_3034659 : Nat := 4983230072969 + 3 ^ 40 * 3034659 * 2
def baseEnd_3034659 : Nat := 346275264331677248090303

theorem tailTrace_3034659 : CollatzResearch.WordTrace tailWord_3034659 prefixEnd_3034659 346275264331677248090303 := by
  unfold tailWord_3034659
  simp only [CollatzResearch.WordTrace]
  refine ⟨110683106712956196340051031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73788737808637464226700687 110683106712956196340051031)
  ·
    refine ⟨166024660069434294510076547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110683106712956196340051031 166024660069434294510076547)
    ·
      refine ⟨249036990104151441765114821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166024660069434294510076547 249036990104151441765114821)
      ·
        refine ⟨46694435644528395330959029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249036990104151441765114821 46694435644528395330959029)
        ·
          refine ⟨4377603341674537062277409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46694435644528395330959029 4377603341674537062277409)
          ·
            refine ⟨3283202506255902796708057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4377603341674537062277409 3283202506255902796708057)
            ·
              refine ⟨2462401879691927097531043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3283202506255902796708057 2462401879691927097531043)
              ·
                refine ⟨3693602819537890646296565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462401879691927097531043 3693602819537890646296565)
                ·
                  refine ⟨346275264331677248090303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3693602819537890646296565 346275264331677248090303)
                  ·
                    rfl

theorem cell22_3034659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 5].length) (baseStart_3034659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034659 prefixEnd_3034659 := by exact prefixLift 3034659
  have htrace : WordTrace (prefixWord ++ tailWord_3034659) baseStart_3034659 baseEnd_3034659 := by
    simpa [prefixWord, tailWord_3034659, baseEnd_3034659] using wordTrace_append hprefix tailTrace_3034659
  have hstable : (prefixWord ++ tailWord_3034659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034659).length < 2 ^ (prefixWord ++ tailWord_3034659).sum := by decide
  have hdescent : baseEnd_3034659 < baseStart_3034659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034689 : List Nat := [1, 2, 5, 1, 1, 1, 5, 1, 1, 4]
def baseStart_3034689 : Nat := 118140960795 + 3034689 * 2 ^ 59
def prefixEnd_3034689 : Nat := 4983230072969 + 3 ^ 40 * 3034689 * 2
def baseEnd_3034689 : Nat := 1038836062608121666020817

theorem tailTrace_3034689 : CollatzResearch.WordTrace tailWord_3034689 prefixEnd_3034689 1038836062608121666020817 := by
  unfold tailWord_3034689
  simp only [CollatzResearch.WordTrace]
  refine ⟨110684200902847511463643121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73789467268565007642428747 110684200902847511463643121)
  ·
    refine ⟨83013150677135633597732341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110684200902847511463643121 83013150677135633597732341)
    ·
      refine ⟨7782482875981465649787407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83013150677135633597732341 7782482875981465649787407)
      ·
        refine ⟨11673724313972198474681111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7782482875981465649787407 11673724313972198474681111)
        ·
          refine ⟨17510586470958297712021667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11673724313972198474681111 17510586470958297712021667)
          ·
            refine ⟨26265879706437446568032501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17510586470958297712021667 26265879706437446568032501)
            ·
              refine ⟨2462426222478510615753047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26265879706437446568032501 2462426222478510615753047)
              ·
                refine ⟨3693639333717765923629571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462426222478510615753047 3693639333717765923629571)
                ·
                  refine ⟨5540459000576648885444357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3693639333717765923629571 5540459000576648885444357)
                  ·
                    refine ⟨1038836062608121666020817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5540459000576648885444357 1038836062608121666020817)
                    ·
                      rfl

theorem cell22_3034689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_3034689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034689 prefixEnd_3034689 := by exact prefixLift 3034689
  have htrace : WordTrace (prefixWord ++ tailWord_3034689) baseStart_3034689 baseEnd_3034689 := by
    simpa [prefixWord, tailWord_3034689, baseEnd_3034689] using wordTrace_append hprefix tailTrace_3034689
  have hstable : (prefixWord ++ tailWord_3034689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034689).length < 2 ^ (prefixWord ++ tailWord_3034689).sum := by decide
  have hdescent : baseEnd_3034689 < baseStart_3034689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034764 : List Nat := [2, 2, 1, 2, 1, 1, 3, 6, 1, 3]
def baseStart_3034764 : Nat := 118140960795 + 3034764 * 2 ^ 59
def prefixEnd_3034764 : Nat := 4983230072969 + 3 ^ 40 * 3034764 * 2
def baseEnd_3034764 : Nat := 1038861736640846470395587

theorem tailTrace_3034764 : CollatzResearch.WordTrace tailWord_3034764 prefixEnd_3034764 1038861736640846470395587 := by
  unfold tailWord_3034764
  simp only [CollatzResearch.WordTrace]
  refine ⟨55343468188787899636311673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73791290918383866181748897 55343468188787899636311673)
  ·
    refine ⟨41507601141590924727233755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55343468188787899636311673 41507601141590924727233755)
    ·
      refine ⟨62261401712386387090850633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41507601141590924727233755 62261401712386387090850633)
      ·
        refine ⟨46696051284289790318137975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62261401712386387090850633 46696051284289790318137975)
        ·
          refine ⟨70044076926434685477206963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46696051284289790318137975 70044076926434685477206963)
          ·
            refine ⟨105066115389652028215810445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70044076926434685477206963 105066115389652028215810445)
            ·
              refine ⟨39399793271119510580928917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105066115389652028215810445 39399793271119510580928917)
              ·
                refine ⟨1846865309583727058481043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39399793271119510580928917 1846865309583727058481043)
                ·
                  refine ⟨2770297964375590587721565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1846865309583727058481043 2770297964375590587721565)
                  ·
                    refine ⟨1038861736640846470395587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2770297964375590587721565 1038861736640846470395587)
                    ·
                      rfl

theorem cell22_3034764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_3034764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034764 prefixEnd_3034764 := by exact prefixLift 3034764
  have htrace : WordTrace (prefixWord ++ tailWord_3034764) baseStart_3034764 baseEnd_3034764 := by
    simpa [prefixWord, tailWord_3034764, baseEnd_3034764] using wordTrace_append hprefix tailTrace_3034764
  have hstable : (prefixWord ++ tailWord_3034764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034764).length < 2 ^ (prefixWord ++ tailWord_3034764).sum := by decide
  have hdescent : baseEnd_3034764 < baseStart_3034764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034828 : List Nat := [2, 2, 1, 5, 3, 1, 2, 1, 5]
def baseStart_3034828 : Nat := 118140960795 + 3034828 * 2 ^ 59
def prefixEnd_3034828 : Nat := 4983230072969 + 3 ^ 40 * 3034828 * 2
def baseEnd_3034828 : Nat := 346294548382923878931797

theorem tailTrace_3034828 : CollatzResearch.WordTrace tailWord_3034828 prefixEnd_3034828 346294548382923878931797 := by
  unfold tailWord_3034828
  simp only [CollatzResearch.WordTrace]
  refine ⟨55344635324671969101476569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73792847099562625468635425 55344635324671969101476569)
  ·
    refine ⟨41508476493503976826107427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55344635324671969101476569 41508476493503976826107427)
    ·
      refine ⟨62262714740255965239161141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41508476493503976826107427 62262714740255965239161141)
      ·
        refine ⟨5837129506898996741171357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62262714740255965239161141 5837129506898996741171357)
        ·
          refine ⟨2188923565087123777939259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5837129506898996741171357 2188923565087123777939259)
          ·
            refine ⟨3283385347630685666908889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2188923565087123777939259 3283385347630685666908889)
            ·
              refine ⟨2462539010723014250181667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3283385347630685666908889 2462539010723014250181667)
              ·
                refine ⟨3693808516084521375272501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462539010723014250181667 3693808516084521375272501)
                ·
                  refine ⟨346294548382923878931797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3693808516084521375272501 346294548382923878931797)
                  ·
                    rfl

theorem cell22_3034828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_3034828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034828 prefixEnd_3034828 := by exact prefixLift 3034828
  have htrace : WordTrace (prefixWord ++ tailWord_3034828) baseStart_3034828 baseEnd_3034828 := by
    simpa [prefixWord, tailWord_3034828, baseEnd_3034828] using wordTrace_append hprefix tailTrace_3034828
  have hstable : (prefixWord ++ tailWord_3034828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034828).length < 2 ^ (prefixWord ++ tailWord_3034828).sum := by decide
  have hdescent : baseEnd_3034828 < baseStart_3034828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034884 : List Nat := [2, 3, 2, 2, 1, 4, 1, 7]
def baseStart_3034884 : Nat := 118140960795 + 3034884 * 2 ^ 59
def prefixEnd_3034884 : Nat := 4983230072969 + 3 ^ 40 * 3034884 * 2
def baseEnd_3034884 : Nat := 115433646121467350821691

theorem tailTrace_3034884 : CollatzResearch.WordTrace tailWord_3034884 prefixEnd_3034884 115433646121467350821691 := by
  unfold tailWord_3034884
  simp only [CollatzResearch.WordTrace]
  refine ⟨55345656568570529883495853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73794208758094039844661137 55345656568570529883495853)
  ·
    refine ⟨20754621213213948706310945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55345656568570529883495853 20754621213213948706310945)
    ·
      refine ⟨15565965909910461529733209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20754621213213948706310945 15565965909910461529733209)
      ·
        refine ⟨11674474432432846147299907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15565965909910461529733209 11674474432432846147299907)
        ·
          refine ⟨17511711648649269220949861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11674474432432846147299907 17511711648649269220949861)
          ·
            refine ⟨3283445934121737978928099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17511711648649269220949861 3283445934121737978928099)
            ·
              refine ⟨4925168901182606968392149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3283445934121737978928099 4925168901182606968392149)
              ·
                refine ⟨115433646121467350821691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4925168901182606968392149 115433646121467350821691)
                ·
                  rfl

theorem cell22_3034884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 7].length) (baseStart_3034884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034884 prefixEnd_3034884 := by exact prefixLift 3034884
  have htrace : WordTrace (prefixWord ++ tailWord_3034884) baseStart_3034884 baseEnd_3034884 := by
    simpa [prefixWord, tailWord_3034884, baseEnd_3034884] using wordTrace_append hprefix tailTrace_3034884
  have hstable : (prefixWord ++ tailWord_3034884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034884).length < 2 ^ (prefixWord ++ tailWord_3034884).sum := by decide
  have hdescent : baseEnd_3034884 < baseStart_3034884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034912 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 7]
def baseStart_3034912 : Nat := 118140960795 + 3034912 * 2 ^ 59
def prefixEnd_3034912 : Nat := 4983230072969 + 3 ^ 40 * 3034912 * 2
def baseEnd_3034912 : Nat := 346304133355141139231711

theorem tailTrace_3034912 : CollatzResearch.WordTrace tailWord_3034912 prefixEnd_3034912 346304133355141139231711 := by
  unfold tailWord_3034912
  simp only [CollatzResearch.WordTrace]
  refine ⟨55346167190519810274505495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73794889587359747032673993 55346167190519810274505495)
  ·
    refine ⟨83019250785779715411758243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55346167190519810274505495 83019250785779715411758243)
    ·
      refine ⟨124528876178669573117637365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83019250785779715411758243 124528876178669573117637365)
      ·
        refine ⟨11674582141750272479778503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124528876178669573117637365 11674582141750272479778503)
        ·
          refine ⟨17511873212625408719667755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11674582141750272479778503 17511873212625408719667755)
          ·
            refine ⟨26267809818938113079501633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17511873212625408719667755 26267809818938113079501633)
            ·
              refine ⟨19700857364203584809626225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26267809818938113079501633 19700857364203584809626225)
              ·
                refine ⟨14775643023152688607219669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19700857364203584809626225 14775643023152688607219669)
                ·
                  refine ⟨346304133355141139231711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14775643023152688607219669 346304133355141139231711)
                  ·
                    rfl

theorem cell22_3034912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 7].length) (baseStart_3034912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034912 prefixEnd_3034912 := by exact prefixLift 3034912
  have htrace : WordTrace (prefixWord ++ tailWord_3034912) baseStart_3034912 baseEnd_3034912 := by
    simpa [prefixWord, tailWord_3034912, baseEnd_3034912] using wordTrace_append hprefix tailTrace_3034912
  have hstable : (prefixWord ++ tailWord_3034912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034912).length < 2 ^ (prefixWord ++ tailWord_3034912).sum := by decide
  have hdescent : baseEnd_3034912 < baseStart_3034912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034929 : List Nat := [1, 2, 2, 3, 2, 2, 3, 2, 5]
def baseStart_3034929 : Nat := 118140960795 + 3034929 * 2 ^ 59
def prefixEnd_3034929 : Nat := 4983230072969 + 3 ^ 40 * 3034929 * 2
def baseEnd_3034929 : Nat := 346306073170947013340027

theorem tailTrace_3034929 : CollatzResearch.WordTrace tailWord_3034929 prefixEnd_3034929 346306073170947013340027 := by
  unfold tailWord_3034929
  simp only [CollatzResearch.WordTrace]
  refine ⟨110692954421978032452379841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73795302947985354968253227 110692954421978032452379841)
  ·
    refine ⟨83019715816483524339284881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110692954421978032452379841 83019715816483524339284881)
    ·
      refine ⟨62264786862362643254463661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83019715816483524339284881 62264786862362643254463661)
      ·
        refine ⟨23349295073385991220423873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62264786862362643254463661 23349295073385991220423873)
        ·
          refine ⟨17511971305039493415317905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23349295073385991220423873 17511971305039493415317905)
          ·
            refine ⟨13133978478779620061488429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17511971305039493415317905 13133978478779620061488429)
            ·
              refine ⟨4925241929542357523058161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13133978478779620061488429 4925241929542357523058161)
              ·
                refine ⟨3693931447156768142293621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4925241929542357523058161 3693931447156768142293621)
                ·
                  refine ⟨346306073170947013340027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3693931447156768142293621 346306073170947013340027)
                  ·
                    rfl

theorem cell22_3034929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 5].length) (baseStart_3034929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3034929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3034929 prefixEnd_3034929 := by exact prefixLift 3034929
  have htrace : WordTrace (prefixWord ++ tailWord_3034929) baseStart_3034929 baseEnd_3034929 := by
    simpa [prefixWord, tailWord_3034929, baseEnd_3034929] using wordTrace_append hprefix tailTrace_3034929
  have hstable : (prefixWord ++ tailWord_3034929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034929).length < 2 ^ (prefixWord ++ tailWord_3034929).sum := by decide
  have hdescent : baseEnd_3034929 < baseStart_3034929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035002 : List Nat := [3, 1, 1, 1, 1, 1, 5, 9]
def baseStart_3035002 : Nat := 118140960795 + 3035002 * 2 ^ 59
def prefixEnd_3035002 : Nat := 4983230072969 + 3 ^ 40 * 3035002 * 2
def baseEnd_3035002 : Nat := 115438134322743686993873

theorem tailTrace_3035002 : CollatzResearch.WordTrace tailWord_3035002 prefixEnd_3035002 115438134322743686993873 := by
  unfold tailWord_3035002
  simp only [CollatzResearch.WordTrace]
  refine ⟨27673904237678391479946815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73797077967142377279858173 27673904237678391479946815)
  ·
    refine ⟨41510856356517587219920223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27673904237678391479946815 41510856356517587219920223)
    ·
      refine ⟨62266284534776380829880335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41510856356517587219920223 62266284534776380829880335)
      ·
        refine ⟨93399426802164571244820503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62266284534776380829880335 93399426802164571244820503)
        ·
          refine ⟨140099140203246856867230755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93399426802164571244820503 140099140203246856867230755)
          ·
            refine ⟨210148710304870285300846133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140099140203246856867230755 210148710304870285300846133)
            ·
              refine ⟨19701441591081589246954325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 210148710304870285300846133 19701441591081589246954325)
              ·
                refine ⟨115438134322743686993873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19701441591081589246954325 115438134322743686993873)
                ·
                  rfl

theorem cell22_3035002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 9].length) (baseStart_3035002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035002 prefixEnd_3035002 := by exact prefixLift 3035002
  have htrace : WordTrace (prefixWord ++ tailWord_3035002) baseStart_3035002 baseEnd_3035002 := by
    simpa [prefixWord, tailWord_3035002, baseEnd_3035002] using wordTrace_append hprefix tailTrace_3035002
  have hstable : (prefixWord ++ tailWord_3035002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035002).length < 2 ^ (prefixWord ++ tailWord_3035002).sum := by decide
  have hdescent : baseEnd_3035002 < baseStart_3035002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035042 : List Nat := [3, 3, 1, 2, 4, 1, 2, 2, 4]
def baseStart_3035042 : Nat := 118140960795 + 3035042 * 2 ^ 59
def prefixEnd_3035042 : Nat := 4983230072969 + 3 ^ 40 * 3035042 * 2
def baseEnd_3035042 : Nat := 346318967240715470648245

theorem tailTrace_3035042 : CollatzResearch.WordTrace tailWord_3035042 prefixEnd_3035042 346318967240715470648245 := by
  unfold tailWord_3035042
  simp only [CollatzResearch.WordTrace]
  refine ⟨27674268967642163187810845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73798050580379101834162253 27674268967642163187810845)
  ·
    refine ⟨10377850862865811195429067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27674268967642163187810845 10377850862865811195429067)
    ·
      refine ⟨15566776294298716793143601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10377850862865811195429067 15566776294298716793143601)
      ·
        refine ⟨11675082220724037594857701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15566776294298716793143601 11675082220724037594857701)
        ·
          refine ⟨2189077916385757049035819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11675082220724037594857701 2189077916385757049035819)
          ·
            refine ⟨3283616874578635573553729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189077916385757049035819 3283616874578635573553729)
            ·
              refine ⟨2462712655933976680165297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3283616874578635573553729 2462712655933976680165297)
              ·
                refine ⟨1847034491950482510123973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2462712655933976680165297 1847034491950482510123973)
                ·
                  refine ⟨346318967240715470648245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1847034491950482510123973 346318967240715470648245)
                  ·
                    rfl

theorem cell22_3035042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_3035042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035042 prefixEnd_3035042 := by exact prefixLift 3035042
  have htrace : WordTrace (prefixWord ++ tailWord_3035042) baseStart_3035042 baseEnd_3035042 := by
    simpa [prefixWord, tailWord_3035042, baseEnd_3035042] using wordTrace_append hprefix tailTrace_3035042
  have hstable : (prefixWord ++ tailWord_3035042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035042).length < 2 ^ (prefixWord ++ tailWord_3035042).sum := by decide
  have hdescent : baseEnd_3035042 < baseStart_3035042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035064 : List Nat := [2, 1, 2, 1, 2, 3, 1, 5, 5]
def baseStart_3035064 : Nat := 118140960795 + 3035064 * 2 ^ 59
def prefixEnd_3035064 : Nat := 4983230072969 + 3 ^ 40 * 3035064 * 2
def baseEnd_3035064 : Nat := 346321477590581895964889

theorem tailTrace_3035064 : CollatzResearch.WordTrace tailWord_3035064 prefixEnd_3035064 346321477590581895964889 := by
  unfold tailWord_3035064
  simp only [CollatzResearch.WordTrace]
  refine ⟨55348939138244475254272123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73798585517659300339029497 55348939138244475254272123)
  ·
    refine ⟨83023408707366712881408185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55348939138244475254272123 83023408707366712881408185)
    ·
      refine ⟨62267556530525034661056139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83023408707366712881408185 62267556530525034661056139)
      ·
        refine ⟨93401334795787551991584209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62267556530525034661056139 93401334795787551991584209)
        ·
          refine ⟨70051001096840663993688157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93401334795787551991584209 70051001096840663993688157)
          ·
            refine ⟨26269125411315248997633059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70051001096840663993688157 26269125411315248997633059)
            ·
              refine ⟨39403688116972873496449589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26269125411315248997633059 39403688116972873496449589)
              ·
                refine ⟨3694095760966206890292149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39403688116972873496449589 3694095760966206890292149)
                ·
                  refine ⟨346321477590581895964889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3694095760966206890292149 346321477590581895964889)
                  ·
                    rfl

theorem cell22_3035064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 5].length) (baseStart_3035064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035064 prefixEnd_3035064 := by exact prefixLift 3035064
  have htrace : WordTrace (prefixWord ++ tailWord_3035064) baseStart_3035064 baseEnd_3035064 := by
    simpa [prefixWord, tailWord_3035064, baseEnd_3035064] using wordTrace_append hprefix tailTrace_3035064
  have hstable : (prefixWord ++ tailWord_3035064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035064).length < 2 ^ (prefixWord ++ tailWord_3035064).sum := by decide
  have hdescent : baseEnd_3035064 < baseStart_3035064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035098 : List Nat := [3, 1, 1, 2, 5, 2, 1, 2, 5]
def baseStart_3035098 : Nat := 118140960795 + 3035098 * 2 ^ 59
def prefixEnd_3035098 : Nat := 4983230072969 + 3 ^ 40 * 3035098 * 2
def baseEnd_3035098 : Nat := 346325357222193644181521

theorem tailTrace_3035098 : CollatzResearch.WordTrace tailWord_3035098 prefixEnd_3035098 346325357222193644181521 := by
  unfold tailWord_3035098
  simp only [CollatzResearch.WordTrace]
  refine ⟨27674779589591443578820487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73799412238910516210187965 27674779589591443578820487)
  ·
    refine ⟨41512169384387165368230731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27674779589591443578820487 41512169384387165368230731)
    ·
      refine ⟨62268254076580748052346097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41512169384387165368230731 62268254076580748052346097)
      ·
        refine ⟨46701190557435561039259573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62268254076580748052346097 46701190557435561039259573)
        ·
          refine ⟨4378236614759583847430585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46701190557435561039259573 4378236614759583847430585)
          ·
            refine ⟨3283677461069687885572939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4378236614759583847430585 3283677461069687885572939)
            ·
              refine ⟨4925516191604531828359409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3283677461069687885572939 4925516191604531828359409)
              ·
                refine ⟨3694137143703398871269557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4925516191604531828359409 3694137143703398871269557)
                ·
                  refine ⟨346325357222193644181521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3694137143703398871269557 346325357222193644181521)
                  ·
                    rfl

theorem cell22_3035098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_3035098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035098 prefixEnd_3035098 := by exact prefixLift 3035098
  have htrace : WordTrace (prefixWord ++ tailWord_3035098) baseStart_3035098 baseEnd_3035098 := by
    simpa [prefixWord, tailWord_3035098, baseEnd_3035098] using wordTrace_append hprefix tailTrace_3035098
  have hstable : (prefixWord ++ tailWord_3035098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035098).length < 2 ^ (prefixWord ++ tailWord_3035098).sum := by decide
  have hdescent : baseEnd_3035098 < baseStart_3035098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035139 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 6, 4]
def baseStart_3035139 : Nat := 118140960795 + 3035139 * 2 ^ 59
def prefixEnd_3035139 : Nat := 4983230072969 + 3 ^ 40 * 3035139 * 2
def baseEnd_3035139 : Nat := 1038990106804470492269437

theorem tailTrace_3035139 : CollatzResearch.WordTrace tailWord_3035139 prefixEnd_3035139 1038990106804470492269437 := by
  unfold tailWord_3035139
  simp only [CollatzResearch.WordTrace]
  refine ⟨110700613751217238317524471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73800409167478158878349647 110700613751217238317524471)
  ·
    refine ⟨166050920626825857476286707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110700613751217238317524471 166050920626825857476286707)
    ·
      refine ⟨249076380940238786214430061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166050920626825857476286707 249076380940238786214430061)
      ·
        refine ⟨93403642852589544830411273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249076380940238786214430061 93403642852589544830411273)
        ·
          refine ⟨70052732139442158622808455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93403642852589544830411273 70052732139442158622808455)
          ·
            refine ⟨105079098209163237934212683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70052732139442158622808455 105079098209163237934212683)
            ·
              refine ⟨157618647313744856901319025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105079098209163237934212683 157618647313744856901319025)
              ·
                refine ⟨118213985485308642675989269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157618647313744856901319025 118213985485308642675989269)
                ·
                  refine ⟨5541280569623842625436997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118213985485308642675989269 5541280569623842625436997)
                  ·
                    refine ⟨1038990106804470492269437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5541280569623842625436997 1038990106804470492269437)
                    ·
                      rfl

theorem cell22_3035139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 4].length) (baseStart_3035139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035139 prefixEnd_3035139 := by exact prefixLift 3035139
  have htrace : WordTrace (prefixWord ++ tailWord_3035139) baseStart_3035139 baseEnd_3035139 := by
    simpa [prefixWord, tailWord_3035139, baseEnd_3035139] using wordTrace_append hprefix tailTrace_3035139
  have hstable : (prefixWord ++ tailWord_3035139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035139).length < 2 ^ (prefixWord ++ tailWord_3035139).sum := by decide
  have hdescent : baseEnd_3035139 < baseStart_3035139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035141 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 4, 3]
def baseStart_3035141 : Nat := 118140960795 + 3035141 * 2 ^ 59
def prefixEnd_3035141 : Nat := 4983230072969 + 3 ^ 40 * 3035141 * 2
def baseEnd_3035141 : Nat := 1038990791445343153719431

theorem tailTrace_3035141 : CollatzResearch.WordTrace tailWord_3035141 prefixEnd_3035141 1038990791445343153719431 := by
  unfold tailWord_3035141
  simp only [CollatzResearch.WordTrace]
  refine ⟨110700686697209992659097277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73800457798139995106064851 110700686697209992659097277)
  ·
    refine ⟨41512757511453747247161479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110700686697209992659097277 41512757511453747247161479)
    ·
      refine ⟨62269136267180620870742219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41512757511453747247161479 62269136267180620870742219)
      ·
        refine ⟨93403704400770931306113329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62269136267180620870742219 93403704400770931306113329)
        ·
          refine ⟨70052778300578198479584997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93403704400770931306113329 70052778300578198479584997)
          ·
            refine ⟨13134895931358412214922187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70052778300578198479584997 13134895931358412214922187)
            ·
              refine ⟨19702343897037618322383281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13134895931358412214922187 19702343897037618322383281)
              ·
                refine ⟨14776757922778213741787461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19702343897037618322383281 14776757922778213741787461)
                ·
                  refine ⟨2770642110520915076585149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14776757922778213741787461 2770642110520915076585149)
                  ·
                    refine ⟨1038990791445343153719431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2770642110520915076585149 1038990791445343153719431)
                    ·
                      rfl

theorem cell22_3035141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_3035141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035141 prefixEnd_3035141 := by exact prefixLift 3035141
  have htrace : WordTrace (prefixWord ++ tailWord_3035141) baseStart_3035141 baseEnd_3035141 := by
    simpa [prefixWord, tailWord_3035141, baseEnd_3035141] using wordTrace_append hprefix tailTrace_3035141
  have hstable : (prefixWord ++ tailWord_3035141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035141).length < 2 ^ (prefixWord ++ tailWord_3035141).sum := by decide
  have hdescent : baseEnd_3035141 < baseStart_3035141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035143 : List Nat := [1, 1, 4, 3, 1, 2, 3, 3, 4]
def baseStart_3035143 : Nat := 118140960795 + 3035143 * 2 ^ 59
def prefixEnd_3035143 : Nat := 4983230072969 + 3 ^ 40 * 3035143 * 2
def baseEnd_3035143 : Nat := 346330492028738605056475

theorem tailTrace_3035143 : CollatzResearch.WordTrace tailWord_3035143 prefixEnd_3035143 346330492028738605056475 := by
  unfold tailWord_3035143
  simp only [CollatzResearch.WordTrace]
  refine ⟨110700759643202747000670083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73800506428801831333780055 110700759643202747000670083)
  ·
    refine ⟨166051139464804120501005125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110700759643202747000670083 166051139464804120501005125)
    ·
      refine ⟨31134588649650772593938461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166051139464804120501005125 31134588649650772593938461)
      ·
        refine ⟨11675470743619039722726923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31134588649650772593938461 11675470743619039722726923)
        ·
          refine ⟨17513206115428559584090385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11675470743619039722726923 17513206115428559584090385)
          ·
            refine ⟨13134904586571419688067789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17513206115428559584090385 13134904586571419688067789)
            ·
              refine ⟨4925589219964282383025421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13134904586571419688067789 4925589219964282383025421)
              ·
                refine ⟨1847095957486605893634533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4925589219964282383025421 1847095957486605893634533)
                ·
                  refine ⟨346330492028738605056475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1847095957486605893634533 346330492028738605056475)
                  ·
                    rfl

theorem cell22_3035143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 4].length) (baseStart_3035143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035143 prefixEnd_3035143 := by exact prefixLift 3035143
  have htrace : WordTrace (prefixWord ++ tailWord_3035143) baseStart_3035143 baseEnd_3035143 := by
    simpa [prefixWord, tailWord_3035143, baseEnd_3035143] using wordTrace_append hprefix tailTrace_3035143
  have hstable : (prefixWord ++ tailWord_3035143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035143).length < 2 ^ (prefixWord ++ tailWord_3035143).sum := by decide
  have hdescent : baseEnd_3035143 < baseStart_3035143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035199 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 9]
def baseStart_3035199 : Nat := 118140960795 + 3035199 * 2 ^ 59
def prefixEnd_3035199 : Nat := 4983230072969 + 3 ^ 40 * 3035199 * 2
def baseEnd_3035199 : Nat := 346336882010216778589751

theorem tailTrace_3035199 : CollatzResearch.WordTrace tailWord_3035199 prefixEnd_3035199 346336882010216778589751 := by
  unfold tailWord_3035199
  simp only [CollatzResearch.WordTrace]
  refine ⟨110702802130999868564708651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73801868087333245709805767 110702802130999868564708651)
  ·
    refine ⟨166054203196499802847062977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110702802130999868564708651 166054203196499802847062977)
    ·
      refine ⟨124540652397374852135297233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166054203196499802847062977 124540652397374852135297233)
      ·
        refine ⟨93405489298031139101472925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124540652397374852135297233 93405489298031139101472925)
        ·
          refine ⟨35027058486761677163052347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93405489298031139101472925 35027058486761677163052347)
          ·
            refine ⟨52540587730142515744578521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35027058486761677163052347 52540587730142515744578521)
            ·
              refine ⟨39405440797606886808433891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52540587730142515744578521 39405440797606886808433891)
              ·
                refine ⟨59108161196410330212650837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39405440797606886808433891 59108161196410330212650837)
                ·
                  refine ⟨346336882010216778589751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59108161196410330212650837 346336882010216778589751)
                  ·
                    rfl

theorem cell22_3035199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 9].length) (baseStart_3035199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035199 prefixEnd_3035199 := by exact prefixLift 3035199
  have htrace : WordTrace (prefixWord ++ tailWord_3035199) baseStart_3035199 baseEnd_3035199 := by
    simpa [prefixWord, tailWord_3035199, baseEnd_3035199] using wordTrace_append hprefix tailTrace_3035199
  have hstable : (prefixWord ++ tailWord_3035199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035199).length < 2 ^ (prefixWord ++ tailWord_3035199).sum := by decide
  have hdescent : baseEnd_3035199 < baseStart_3035199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035293 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_3035293 : Nat := 118140960795 + 3035293 * 2 ^ 59
def prefixEnd_3035293 : Nat := 4983230072969 + 3 ^ 40 * 3035293 * 2
def baseEnd_3035293 : Nat := 1039042824151665423918965

theorem tailTrace_3035293 : CollatzResearch.WordTrace tailWord_3035293 prefixEnd_3035293 1039042824151665423918965 := by
  unfold tailWord_3035293
  simp only [CollatzResearch.WordTrace]
  refine ⟨110706230592659322618630533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73804153728439548412420355 110706230592659322618630533)
  ·
    refine ⟨20757418236123622990993225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110706230592659322618630533 20757418236123622990993225)
    ·
      refine ⟨15568063677092717243244919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20757418236123622990993225 15568063677092717243244919)
      ·
        refine ⟨23352095515639075864867379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15568063677092717243244919 23352095515639075864867379)
        ·
          refine ⟨35028143273458613797301069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23352095515639075864867379 35028143273458613797301069)
          ·
            refine ⟨13135553727546980173987901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35028143273458613797301069 13135553727546980173987901)
            ·
              refine ⟨4925832647830117565245463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13135553727546980173987901 4925832647830117565245463)
              ·
                refine ⟨7388748971745176347868195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4925832647830117565245463 7388748971745176347868195)
                ·
                  refine ⟨11083123457617764521802293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7388748971745176347868195 11083123457617764521802293)
                  ·
                    refine ⟨1039042824151665423918965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11083123457617764521802293 1039042824151665423918965)
                    ·
                      rfl

theorem cell22_3035293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_3035293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035293 prefixEnd_3035293 := by exact prefixLift 3035293
  have htrace : WordTrace (prefixWord ++ tailWord_3035293) baseStart_3035293 baseEnd_3035293 := by
    simpa [prefixWord, tailWord_3035293, baseEnd_3035293] using wordTrace_append hprefix tailTrace_3035293
  have hstable : (prefixWord ++ tailWord_3035293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035293).length < 2 ^ (prefixWord ++ tailWord_3035293).sum := by decide
  have hdescent : baseEnd_3035293 < baseStart_3035293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035329 : List Nat := [1, 2, 6, 1, 2, 1, 3, 2, 4]
def baseStart_3035329 : Nat := 118140960795 + 3035329 * 2 ^ 59
def prefixEnd_3035329 : Nat := 4983230072969 + 3 ^ 40 * 3035329 * 2
def baseEnd_3035329 : Nat := 346351715895791110006285

theorem tailTrace_3035329 : CollatzResearch.WordTrace tailWord_3035329 prefixEnd_3035329 346351715895791110006285 := by
  unfold tailWord_3035329
  simp only [CollatzResearch.WordTrace]
  refine ⟨110707543620528900766941041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73805029080352600511294027 110707543620528900766941041)
  ·
    refine ⟨83030657715396675575205781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110707543620528900766941041 83030657715396675575205781)
    ·
      refine ⟨3892062080409219167587771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83030657715396675575205781 3892062080409219167587771)
      ·
        refine ⟨5838093120613828751381657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3892062080409219167587771 5838093120613828751381657)
        ·
          refine ⟨4378569840460371563536243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5838093120613828751381657 4378569840460371563536243)
          ·
            refine ⟨6567854760690557345304365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4378569840460371563536243 6567854760690557345304365)
            ·
              refine ⟨2462945535258959004489137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6567854760690557345304365 2462945535258959004489137)
              ·
                refine ⟨1847209151444219253366853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2462945535258959004489137 1847209151444219253366853)
                ·
                  refine ⟨346351715895791110006285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1847209151444219253366853 346351715895791110006285)
                  ·
                    rfl

theorem cell22_3035329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 4].length) (baseStart_3035329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035329 prefixEnd_3035329 := by exact prefixLift 3035329
  have htrace : WordTrace (prefixWord ++ tailWord_3035329) baseStart_3035329 baseEnd_3035329 := by
    simpa [prefixWord, tailWord_3035329, baseEnd_3035329] using wordTrace_append hprefix tailTrace_3035329
  have hstable : (prefixWord ++ tailWord_3035329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035329).length < 2 ^ (prefixWord ++ tailWord_3035329).sum := by decide
  have hdescent : baseEnd_3035329 < baseStart_3035329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035336 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 2, 6]
def baseStart_3035336 : Nat := 118140960795 + 3035336 * 2 ^ 59
def prefixEnd_3035336 : Nat := 4983230072969 + 3 ^ 40 * 3035336 * 2
def baseEnd_3035336 : Nat := 1039057543930427645093833

theorem tailTrace_3035336 : CollatzResearch.WordTrace tailWord_3035336 prefixEnd_3035336 1039057543930427645093833 := by
  unfold tailWord_3035336
  simp only [CollatzResearch.WordTrace]
  refine ⟨55353899465751770481222931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73805199287669027308297241 55353899465751770481222931)
  ·
    refine ⟨83030849198627655721834397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55353899465751770481222931 83030849198627655721834397)
    ·
      refine ⟨31136568449485370895687899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83030849198627655721834397 31136568449485370895687899)
      ·
        refine ⟨46704852674228056343531849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31136568449485370895687899 46704852674228056343531849)
        ·
          refine ⟨35028639505671042257648887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46704852674228056343531849 35028639505671042257648887)
          ·
            refine ⟨52542959258506563386473331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35028639505671042257648887 52542959258506563386473331)
            ·
              refine ⟨78814438887759845079709997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52542959258506563386473331 78814438887759845079709997)
              ·
                refine ⟨29555414582909941904891249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78814438887759845079709997 29555414582909941904891249)
                ·
                  refine ⟨22166560937182456428668437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29555414582909941904891249 22166560937182456428668437)
                  ·
                    refine ⟨1039057543930427645093833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22166560937182456428668437 1039057543930427645093833)
                    ·
                      rfl

theorem cell22_3035336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_3035336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035336 prefixEnd_3035336 := by exact prefixLift 3035336
  have htrace : WordTrace (prefixWord ++ tailWord_3035336) baseStart_3035336 baseEnd_3035336 := by
    simpa [prefixWord, tailWord_3035336, baseEnd_3035336] using wordTrace_append hprefix tailTrace_3035336
  have hstable : (prefixWord ++ tailWord_3035336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035336).length < 2 ^ (prefixWord ++ tailWord_3035336).sum := by decide
  have hdescent : baseEnd_3035336 < baseStart_3035336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035340 : List Nat := [2, 2, 1, 6, 1, 1, 2, 7]
def baseStart_3035340 : Nat := 118140960795 + 3035340 * 2 ^ 59
def prefixEnd_3035340 : Nat := 4983230072969 + 3 ^ 40 * 3035340 * 2
def baseEnd_3035340 : Nat := 115450990356908107554869

theorem tailTrace_3035340 : CollatzResearch.WordTrace tailWord_3035340 prefixEnd_3035340 115450990356908107554869 := by
  unfold tailWord_3035340
  simp only [CollatzResearch.WordTrace]
  refine ⟨55353972411744524822795737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73805296548992699763727649 55353972411744524822795737)
  ·
    refine ⟨41515479308808393617096803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55353972411744524822795737 41515479308808393617096803)
    ·
      refine ⟨62273218963212590425645205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41515479308808393617096803 62273218963212590425645205)
      ·
        refine ⟨2919057138900590176202119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62273218963212590425645205 2919057138900590176202119)
        ·
          refine ⟨4378585708350885264303179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2919057138900590176202119 4378585708350885264303179)
          ·
            refine ⟨6567878562526327896454769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4378585708350885264303179 6567878562526327896454769)
            ·
              refine ⟨4925908921894745922341077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6567878562526327896454769 4925908921894745922341077)
              ·
                refine ⟨115450990356908107554869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4925908921894745922341077 115450990356908107554869)
                ·
                  rfl

theorem cell22_3035340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 7].length) (baseStart_3035340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035340 prefixEnd_3035340 := by exact prefixLift 3035340
  have htrace : WordTrace (prefixWord ++ tailWord_3035340) baseStart_3035340 baseEnd_3035340 := by
    simpa [prefixWord, tailWord_3035340, baseEnd_3035340] using wordTrace_append hprefix tailTrace_3035340
  have hstable : (prefixWord ++ tailWord_3035340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035340).length < 2 ^ (prefixWord ++ tailWord_3035340).sum := by decide
  have hdescent : baseEnd_3035340 < baseStart_3035340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035432 : List Nat := [2, 1, 5, 1, 3, 1, 1, 3, 1, 4]
def baseStart_3035432 : Nat := 118140960795 + 3035432 * 2 ^ 59
def prefixEnd_3035432 : Nat := 4983230072969 + 3 ^ 40 * 3035432 * 2
def baseEnd_3035432 : Nat := 1039090406692315394693539

theorem tailTrace_3035432 : CollatzResearch.WordTrace tailWord_3035432 prefixEnd_3035432 1039090406692315394693539 := by
  unfold tailWord_3035432
  simp only [CollatzResearch.WordTrace]
  refine ⟨55355650169577874678970275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73807533559437166238627033 55355650169577874678970275)
  ·
    refine ⟨83033475254366812018455413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55355650169577874678970275 83033475254366812018455413)
    ·
      refine ⟨7784388305096888626730195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83033475254366812018455413 7784388305096888626730195)
      ·
        refine ⟨11676582457645332940095293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7784388305096888626730195 11676582457645332940095293)
        ·
          refine ⟨4378718421616999852535735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11676582457645332940095293 4378718421616999852535735)
          ·
            refine ⟨6568077632425499778803603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4378718421616999852535735 6568077632425499778803603)
            ·
              refine ⟨9852116448638249668205405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6568077632425499778803603 9852116448638249668205405)
              ·
                refine ⟨3694543668239343625577027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9852116448638249668205405 3694543668239343625577027)
                ·
                  refine ⟨5541815502359015438365541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694543668239343625577027 5541815502359015438365541)
                  ·
                    refine ⟨1039090406692315394693539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5541815502359015438365541 1039090406692315394693539)
                    ·
                      rfl

theorem cell22_3035432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_3035432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035432 prefixEnd_3035432 := by exact prefixLift 3035432
  have htrace : WordTrace (prefixWord ++ tailWord_3035432) baseStart_3035432 baseEnd_3035432 := by
    simpa [prefixWord, tailWord_3035432, baseEnd_3035432] using wordTrace_append hprefix tailTrace_3035432
  have hstable : (prefixWord ++ tailWord_3035432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035432).length < 2 ^ (prefixWord ++ tailWord_3035432).sum := by decide
  have hdescent : baseEnd_3035432 < baseStart_3035432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035443 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 4, 4]
def baseStart_3035443 : Nat := 118140960795 + 3035443 * 2 ^ 59
def prefixEnd_3035443 : Nat := 4983230072969 + 3 ^ 40 * 3035443 * 2
def baseEnd_3035443 : Nat := 1039094172217115032668505

theorem tailTrace_3035443 : CollatzResearch.WordTrace tailWord_3035443 prefixEnd_3035443 1039094172217115032668505 := by
  unfold tailWord_3035443
  simp only [CollatzResearch.WordTrace]
  refine ⟨110711701542115898236590983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73807801028077265491060655 110711701542115898236590983)
  ·
    refine ⟨166067552313173847354886475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110711701542115898236590983 166067552313173847354886475)
    ·
      refine ⟨249101328469760771032329713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166067552313173847354886475 249101328469760771032329713)
      ·
        refine ⟨186825996352320578274247285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249101328469760771032329713 186825996352320578274247285)
        ·
          refine ⟨17514937158030054213210683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 186825996352320578274247285 17514937158030054213210683)
          ·
            refine ⟨26272405737045081319816025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17514937158030054213210683 26272405737045081319816025)
            ·
              refine ⟨19704304302783810989862019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26272405737045081319816025 19704304302783810989862019)
              ·
                refine ⟨29556456454175716484793029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19704304302783810989862019 29556456454175716484793029)
                ·
                  refine ⟨5541835585157946840898693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29556456454175716484793029 5541835585157946840898693)
                  ·
                    refine ⟨1039094172217115032668505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5541835585157946840898693 1039094172217115032668505)
                    ·
                      rfl

theorem cell22_3035443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 4].length) (baseStart_3035443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035443 prefixEnd_3035443 := by exact prefixLift 3035443
  have htrace : WordTrace (prefixWord ++ tailWord_3035443) baseStart_3035443 baseEnd_3035443 := by
    simpa [prefixWord, tailWord_3035443, baseEnd_3035443] using wordTrace_append hprefix tailTrace_3035443
  have hstable : (prefixWord ++ tailWord_3035443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035443).length < 2 ^ (prefixWord ++ tailWord_3035443).sum := by decide
  have hdescent : baseEnd_3035443 < baseStart_3035443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035445 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 4, 3]
def baseStart_3035445 : Nat := 118140960795 + 3035445 * 2 ^ 59
def prefixEnd_3035445 : Nat := 4983230072969 + 3 ^ 40 * 3035445 * 2
def baseEnd_3035445 : Nat := 1039094856857987694118499

theorem tailTrace_3035445 : CollatzResearch.WordTrace tailWord_3035445 prefixEnd_3035445 1039094856857987694118499 := by
  unfold tailWord_3035445
  simp only [CollatzResearch.WordTrace]
  refine ⟨110711774488108652578163789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73807849658739101718775859 110711774488108652578163789)
  ·
    refine ⟨41516915433040744716811421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110711774488108652578163789 41516915433040744716811421)
    ·
      refine ⟨15568843287390279268804283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41516915433040744716811421 15568843287390279268804283)
      ·
        refine ⟨23353264931085418903206425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15568843287390279268804283 23353264931085418903206425)
        ·
          refine ⟨17514948698314064177404819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23353264931085418903206425 17514948698314064177404819)
          ·
            refine ⟨26272423047471096266107229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17514948698314064177404819 26272423047471096266107229)
            ·
              refine ⟨9852158642801661099790211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26272423047471096266107229 9852158642801661099790211)
              ·
                refine ⟨14778237964202491649685317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9852158642801661099790211 14778237964202491649685317)
                ·
                  refine ⟨2770919618287967184315997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14778237964202491649685317 2770919618287967184315997)
                  ·
                    refine ⟨1039094856857987694118499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2770919618287967184315997 1039094856857987694118499)
                    ·
                      rfl

theorem cell22_3035445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_3035445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035445 prefixEnd_3035445 := by exact prefixLift 3035445
  have htrace : WordTrace (prefixWord ++ tailWord_3035445) baseStart_3035445 baseEnd_3035445 := by
    simpa [prefixWord, tailWord_3035445, baseEnd_3035445] using wordTrace_append hprefix tailTrace_3035445
  have hstable : (prefixWord ++ tailWord_3035445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035445).length < 2 ^ (prefixWord ++ tailWord_3035445).sum := by decide
  have hdescent : baseEnd_3035445 < baseStart_3035445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035593 : List Nat := [1, 2, 1, 1, 2, 1, 4, 10]
def baseStart_3035593 : Nat := 118140960795 + 3035593 * 2 ^ 59
def prefixEnd_3035593 : Nat := 4983230072969 + 3 ^ 40 * 3035593 * 2
def baseEnd_3035593 : Nat := 115460613364729404602005

theorem tailTrace_3035593 : CollatzResearch.WordTrace tailWord_3035593 prefixEnd_3035593 115460613364729404602005 := by
  unfold tailWord_3035593
  simp only [CollatzResearch.WordTrace]
  refine ⟨110717172491572473854551433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73811448327714982569700955 110717172491572473854551433)
  ·
    refine ⟨83037879368679355390913575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110717172491572473854551433 83037879368679355390913575)
    ·
      refine ⟨124556819053019033086370363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83037879368679355390913575 124556819053019033086370363)
      ·
        refine ⟨186835228579528549629555545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124556819053019033086370363 186835228579528549629555545)
        ·
          refine ⟨140126421434646412222166659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186835228579528549629555545 140126421434646412222166659)
          ·
            refine ⟨210189632151969618333249989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140126421434646412222166659 210189632151969618333249989)
            ·
              refine ⟨39410556028494303437484373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210189632151969618333249989 39410556028494303437484373)
              ·
                refine ⟨115460613364729404602005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39410556028494303437484373 115460613364729404602005)
                ·
                  rfl

theorem cell22_3035593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 10].length) (baseStart_3035593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035593 prefixEnd_3035593 := by exact prefixLift 3035593
  have htrace : WordTrace (prefixWord ++ tailWord_3035593) baseStart_3035593 baseEnd_3035593 := by
    simpa [prefixWord, tailWord_3035593, baseEnd_3035593] using wordTrace_append hprefix tailTrace_3035593
  have hstable : (prefixWord ++ tailWord_3035593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035593).length < 2 ^ (prefixWord ++ tailWord_3035593).sum := by decide
  have hdescent : baseEnd_3035593 < baseStart_3035593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035749 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 1, 5]
def baseStart_3035749 : Nat := 118140960795 + 3035749 * 2 ^ 59
def prefixEnd_3035749 : Nat := 4983230072969 + 3 ^ 40 * 3035749 * 2
def baseEnd_3035749 : Nat := 1039198922270632234517567

theorem tailTrace_3035749 : CollatzResearch.WordTrace tailWord_3035749 prefixEnd_3035749 1039198922270632234517567 := by
  unfold tailWord_3035749
  simp only [CollatzResearch.WordTrace]
  refine ⟨110722862279007312497230301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73815241519338208331486867 110722862279007312497230301)
  ·
    refine ⟨41521073354627742186461363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110722862279007312497230301 41521073354627742186461363)
    ·
      refine ⟨62281610031941613279692045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41521073354627742186461363 62281610031941613279692045)
      ·
        refine ⟨23355603761978104979884517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62281610031941613279692045 23355603761978104979884517)
        ·
          refine ⟨4379175705370894683728347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23355603761978104979884517 4379175705370894683728347)
          ·
            refine ⟨6568763558056342025592521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4379175705370894683728347 6568763558056342025592521)
            ·
              refine ⟨4926572668542256519194391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6568763558056342025592521 4926572668542256519194391)
              ·
                refine ⟨7389859002813384778791587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4926572668542256519194391 7389859002813384778791587)
                ·
                  refine ⟨11084788504220077168187381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7389859002813384778791587 11084788504220077168187381)
                  ·
                    refine ⟨1039198922270632234517567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11084788504220077168187381 1039198922270632234517567)
                    ·
                      rfl

theorem cell22_3035749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_3035749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035749 prefixEnd_3035749 := by exact prefixLift 3035749
  have htrace : WordTrace (prefixWord ++ tailWord_3035749) baseStart_3035749 baseEnd_3035749 := by
    simpa [prefixWord, tailWord_3035749, baseEnd_3035749] using wordTrace_append hprefix tailTrace_3035749
  have hstable : (prefixWord ++ tailWord_3035749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035749).length < 2 ^ (prefixWord ++ tailWord_3035749).sum := by decide
  have hdescent : baseEnd_3035749 < baseStart_3035749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035775 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 1, 8]
def baseStart_3035775 : Nat := 118140960795 + 3035775 * 2 ^ 59
def prefixEnd_3035775 : Nat := 4983230072969 + 3 ^ 40 * 3035775 * 2
def baseEnd_3035775 : Nat := 1039207822601976833367487

theorem tailTrace_3035775 : CollatzResearch.WordTrace tailWord_3035775 prefixEnd_3035775 1039207822601976833367487 := by
  unfold tailWord_3035775
  simp only [CollatzResearch.WordTrace]
  refine ⟨110723810576913118937676779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73815873717942079291784519 110723810576913118937676779)
  ·
    refine ⟨166085715865369678406515169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110723810576913118937676779 166085715865369678406515169)
    ·
      refine ⟨124564286899027258804886377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166085715865369678406515169 124564286899027258804886377)
      ·
        refine ⟨93423215174270444103664783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124564286899027258804886377 93423215174270444103664783)
        ·
          refine ⟨140134822761405666155497175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93423215174270444103664783 140134822761405666155497175)
          ·
            refine ⟨210202234142108499233245763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140134822761405666155497175 210202234142108499233245763)
            ·
              refine ⟨315303351213162748849868645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210202234142108499233245763 315303351213162748849868645)
              ·
                refine ⟨59119378352468015409350371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315303351213162748849868645 59119378352468015409350371)
                ·
                  refine ⟨88679067528702023114025557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59119378352468015409350371 88679067528702023114025557)
                  ·
                    refine ⟨1039207822601976833367487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88679067528702023114025557 1039207822601976833367487)
                    ·
                      rfl

theorem cell22_3035775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_3035775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035775 prefixEnd_3035775 := by exact prefixLift 3035775
  have htrace : WordTrace (prefixWord ++ tailWord_3035775) baseStart_3035775 baseEnd_3035775 := by
    simpa [prefixWord, tailWord_3035775, baseEnd_3035775] using wordTrace_append hprefix tailTrace_3035775
  have hstable : (prefixWord ++ tailWord_3035775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035775).length < 2 ^ (prefixWord ++ tailWord_3035775).sum := by decide
  have hdescent : baseEnd_3035775 < baseStart_3035775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035858 : List Nat := [3, 2, 2, 2, 3, 2, 2, 1, 5]
def baseStart_3035858 : Nat := 118140960795 + 3035858 * 2 ^ 59
def prefixEnd_3035858 : Nat := 4983230072969 + 3 ^ 40 * 3035858 * 2
def baseEnd_3035858 : Nat := 346412078399397427847411

theorem tailTrace_3035858 : CollatzResearch.WordTrace tailWord_3035858 prefixEnd_3035858 346412078399397427847411 := by
  unfold tailWord_3035858
  simp only [CollatzResearch.WordTrace]
  refine ⟨27681709458903106028237057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73817891890408282741965485 27681709458903106028237057)
  ·
    refine ⟨20761282094177329521177793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27681709458903106028237057 20761282094177329521177793)
    ·
      refine ⟨15570961570632997140883345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20761282094177329521177793 15570961570632997140883345)
      ·
        refine ⟨11678221177974747855662509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15570961570632997140883345 11678221177974747855662509)
        ·
          refine ⟨4379332941740530445873441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11678221177974747855662509 4379332941740530445873441)
          ·
            refine ⟨3284499706305397834405081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4379332941740530445873441 3284499706305397834405081)
            ·
              refine ⟨2463374779729048375803811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3284499706305397834405081 2463374779729048375803811)
              ·
                refine ⟨3695062169593572563705717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2463374779729048375803811 3695062169593572563705717)
                ·
                  refine ⟨346412078399397427847411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3695062169593572563705717 346412078399397427847411)
                  ·
                    rfl

theorem cell22_3035858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_3035858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035858 prefixEnd_3035858 := by exact prefixLift 3035858
  have htrace : WordTrace (prefixWord ++ tailWord_3035858) baseStart_3035858 baseEnd_3035858 := by
    simpa [prefixWord, tailWord_3035858, baseEnd_3035858] using wordTrace_append hprefix tailTrace_3035858
  have hstable : (prefixWord ++ tailWord_3035858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035858).length < 2 ^ (prefixWord ++ tailWord_3035858).sum := by decide
  have hdescent : baseEnd_3035858 < baseStart_3035858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035871 : List Nat := [1, 1, 2, 3, 2, 5, 1, 2, 1, 4]
def baseStart_3035871 : Nat := 118140960795 + 3035871 * 2 ^ 59
def prefixEnd_3035871 : Nat := 4983230072969 + 3 ^ 40 * 3035871 * 2
def baseEnd_3035871 : Nat := 1039240685363864582967193

theorem tailTrace_3035871 : CollatzResearch.WordTrace tailWord_3035871 prefixEnd_3035871 1039240685363864582967193 := by
  unfold tailWord_3035871
  simp only [CollatzResearch.WordTrace]
  refine ⟨110727311984565327333171467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73818207989710218222114311 110727311984565327333171467)
  ·
    refine ⟨166090967976847990999757201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110727311984565327333171467 166090967976847990999757201)
    ·
      refine ⟨124568225982635993249817901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166090967976847990999757201 124568225982635993249817901)
      ·
        refine ⟨46713084743488497468681713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124568225982635993249817901 46713084743488497468681713)
        ·
          refine ⟨35034813557616373101511285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46713084743488497468681713 35034813557616373101511285)
          ·
            refine ⟨3284513771026534978266683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35034813557616373101511285 3284513771026534978266683)
            ·
              refine ⟨4926770656539802467400025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3284513771026534978266683 4926770656539802467400025)
              ·
                refine ⟨3695077992404851850550019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4926770656539802467400025 3695077992404851850550019)
                ·
                  refine ⟨5542616988607277775825029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3695077992404851850550019 5542616988607277775825029)
                  ·
                    refine ⟨1039240685363864582967193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5542616988607277775825029 1039240685363864582967193)
                    ·
                      rfl

theorem cell22_3035871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 4].length) (baseStart_3035871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035871 prefixEnd_3035871 := by exact prefixLift 3035871
  have htrace : WordTrace (prefixWord ++ tailWord_3035871) baseStart_3035871 baseEnd_3035871 := by
    simpa [prefixWord, tailWord_3035871, baseEnd_3035871] using wordTrace_append hprefix tailTrace_3035871
  have hstable : (prefixWord ++ tailWord_3035871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035871).length < 2 ^ (prefixWord ++ tailWord_3035871).sum := by decide
  have hdescent : baseEnd_3035871 < baseStart_3035871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035901 : List Nat := [1, 4, 1, 1, 1, 1, 6, 2, 2, 3]
def baseStart_3035901 : Nat := 118140960795 + 3035901 * 2 ^ 59
def prefixEnd_3035901 : Nat := 4983230072969 + 3 ^ 40 * 3035901 * 2
def baseEnd_3035901 : Nat := 1039250954976954504717101

theorem tailTrace_3035901 : CollatzResearch.WordTrace tailWord_3035901 prefixEnd_3035901 1039250954976954504717101 := by
  unfold tailWord_3035901
  simp only [CollatzResearch.WordTrace]
  refine ⟨110728406174456642456763557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73818937449637761637842371 110728406174456642456763557)
  ·
    refine ⟨20761576157710620460643167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110728406174456642456763557 20761576157710620460643167)
    ·
      refine ⟨31142364236565930690964751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20761576157710620460643167 31142364236565930690964751)
      ·
        refine ⟨46713546354848896036447127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31142364236565930690964751 46713546354848896036447127)
        ·
          refine ⟨70070319532273344054670691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46713546354848896036447127 70070319532273344054670691)
          ·
            refine ⟨105105479298410016082006037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70070319532273344054670691 105105479298410016082006037)
            ·
              refine ⟨4926819342112969503844033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105105479298410016082006037 4926819342112969503844033)
              ·
                refine ⟨3695114506584727127883025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4926819342112969503844033 3695114506584727127883025)
                ·
                  refine ⟨2771335879938545345912269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3695114506584727127883025 2771335879938545345912269)
                  ·
                    refine ⟨1039250954976954504717101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2771335879938545345912269 1039250954976954504717101)
                    ·
                      rfl

theorem cell22_3035901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_3035901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035901 prefixEnd_3035901 := by exact prefixLift 3035901
  have htrace : WordTrace (prefixWord ++ tailWord_3035901) baseStart_3035901 baseEnd_3035901 := by
    simpa [prefixWord, tailWord_3035901, baseEnd_3035901] using wordTrace_append hprefix tailTrace_3035901
  have hstable : (prefixWord ++ tailWord_3035901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035901).length < 2 ^ (prefixWord ++ tailWord_3035901).sum := by decide
  have hdescent : baseEnd_3035901 < baseStart_3035901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035976 : List Nat := [2, 1, 3, 1, 1, 3, 5, 1, 5]
def baseStart_3035976 : Nat := 118140960795 + 3035976 * 2 ^ 59
def prefixEnd_3035976 : Nat := 4983230072969 + 3 ^ 40 * 3035976 * 2
def baseEnd_3035976 : Nat := 346425543003226436363957

theorem tailTrace_3035976 : CollatzResearch.WordTrace tailWord_3035976 prefixEnd_3035976 346425543003226436363957 := by
  unfold tailWord_3035976
  simp only [CollatzResearch.WordTrace]
  refine ⟨55365570824592465132871891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73820761099456620177162521 55365570824592465132871891)
  ·
    refine ⟨83048356236888697699307837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55365570824592465132871891 83048356236888697699307837)
    ·
      refine ⟨31143133588833261637240439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83048356236888697699307837 31143133588833261637240439)
      ·
        refine ⟨46714700383249892455860659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31143133588833261637240439 46714700383249892455860659)
        ·
          refine ⟨70072050574874838683790989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46714700383249892455860659 70072050574874838683790989)
          ·
            refine ⟨26277018965578064506421621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70072050574874838683790989 26277018965578064506421621)
            ·
              refine ⟨2463470528022943547477027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26277018965578064506421621 2463470528022943547477027)
              ·
                refine ⟨3695205792034415321215541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2463470528022943547477027 3695205792034415321215541)
                ·
                  refine ⟨346425543003226436363957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3695205792034415321215541 346425543003226436363957)
                  ·
                    rfl

theorem cell22_3035976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 5].length) (baseStart_3035976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3035976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3035976 prefixEnd_3035976 := by exact prefixLift 3035976
  have htrace : WordTrace (prefixWord ++ tailWord_3035976) baseStart_3035976 baseEnd_3035976 := by
    simpa [prefixWord, tailWord_3035976, baseEnd_3035976] using wordTrace_append hprefix tailTrace_3035976
  have hstable : (prefixWord ++ tailWord_3035976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035976).length < 2 ^ (prefixWord ++ tailWord_3035976).sum := by decide
  have hdescent : baseEnd_3035976 < baseStart_3035976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036021 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 6]
def baseStart_3036021 : Nat := 118140960795 + 3036021 * 2 ^ 59
def prefixEnd_3036021 : Nat := 4983230072969 + 3 ^ 40 * 3036021 * 2
def baseEnd_3036021 : Nat := 346430677809771397238911

theorem tailTrace_3036021 : CollatzResearch.WordTrace tailWord_3036021 prefixEnd_3036021 346430677809771397238911 := by
  unfold tailWord_3036021
  simp only [CollatzResearch.WordTrace]
  refine ⟨110732782934021902951131917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73821855289347935300754611 110732782934021902951131917)
  ·
    refine ⟨41524793600258213606674469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110732782934021902951131917 41524793600258213606674469)
    ·
      refine ⟨7785898800048415051251463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41524793600258213606674469 7785898800048415051251463)
      ·
        refine ⟨11678848200072622576877195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7785898800048415051251463 11678848200072622576877195)
        ·
          refine ⟨17518272300108933865315793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11678848200072622576877195 17518272300108933865315793)
          ·
            refine ⟨13138704225081700398986845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17518272300108933865315793 13138704225081700398986845)
            ·
              refine ⟨4927014084405637649620067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13138704225081700398986845 4927014084405637649620067)
              ·
                refine ⟨7390521126608456474430101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4927014084405637649620067 7390521126608456474430101)
                ·
                  refine ⟨346430677809771397238911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7390521126608456474430101 346430677809771397238911)
                  ·
                    rfl

theorem cell22_3036021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_3036021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036021 prefixEnd_3036021 := by exact prefixLift 3036021
  have htrace : WordTrace (prefixWord ++ tailWord_3036021) baseStart_3036021 baseEnd_3036021 := by
    simpa [prefixWord, tailWord_3036021, baseEnd_3036021] using wordTrace_append hprefix tailTrace_3036021
  have hstable : (prefixWord ++ tailWord_3036021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036021).length < 2 ^ (prefixWord ++ tailWord_3036021).sum := by decide
  have hdescent : baseEnd_3036021 < baseStart_3036021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036100 : List Nat := [2, 3, 3, 3, 1, 1, 3, 6]
def baseStart_3036100 : Nat := 118140960795 + 3036100 * 2 ^ 59
def prefixEnd_3036100 : Nat := 4983230072969 + 3 ^ 40 * 3036100 * 2
def baseEnd_3036100 : Nat := 115479897415976035443499

theorem tailTrace_3036100 : CollatzResearch.WordTrace tailWord_3036100 prefixEnd_3036100 115479897415976035443499 := by
  unfold tailWord_3036100
  simp only [CollatzResearch.WordTrace]
  refine ⟨55367832150367849721628877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73823776200490466295505169 55367832150367849721628877)
  ·
    refine ⟨20762937056387943645610829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55367832150367849721628877 20762937056387943645610829)
    ·
      refine ⟨7786101396145478867104061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20762937056387943645610829 7786101396145478867104061)
      ·
        refine ⟨2919788023554554575164023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7786101396145478867104061 2919788023554554575164023)
        ·
          refine ⟨4379682035331831862746035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2919788023554554575164023 4379682035331831862746035)
          ·
            refine ⟨6569523052997747794119053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4379682035331831862746035 6569523052997747794119053)
            ·
              refine ⟨2463571144874155422794645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6569523052997747794119053 2463571144874155422794645)
              ·
                refine ⟨115479897415976035443499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2463571144874155422794645 115479897415976035443499)
                ·
                  rfl

theorem cell22_3036100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 6].length) (baseStart_3036100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036100 prefixEnd_3036100 := by exact prefixLift 3036100
  have htrace : WordTrace (prefixWord ++ tailWord_3036100) baseStart_3036100 baseEnd_3036100 := by
    simpa [prefixWord, tailWord_3036100, baseEnd_3036100] using wordTrace_append hprefix tailTrace_3036100
  have hstable : (prefixWord ++ tailWord_3036100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036100).length < 2 ^ (prefixWord ++ tailWord_3036100).sum := by decide
  have hdescent : baseEnd_3036100 < baseStart_3036100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036156 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 6]
def baseStart_3036156 : Nat := 118140960795 + 3036156 * 2 ^ 59
def prefixEnd_3036156 : Nat := 4983230072969 + 3 ^ 40 * 3036156 * 2
def baseEnd_3036156 : Nat := 346446082229406279863773

theorem tailTrace_3036156 : CollatzResearch.WordTrace tailWord_3036156 prefixEnd_3036156 346446082229406279863773 := by
  unfold tailWord_3036156
  simp only [CollatzResearch.WordTrace]
  refine ⟨55368853394266410503648161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73825137859021880671530881 55368853394266410503648161)
  ·
    refine ⟨41526640045699807877736121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55368853394266410503648161 41526640045699807877736121)
    ·
      refine ⟨31144980034274855908302091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41526640045699807877736121 31144980034274855908302091)
      ·
        refine ⟨46717470051412283862453137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31144980034274855908302091 46717470051412283862453137)
        ·
          refine ⟨35038102538559212896839853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46717470051412283862453137 35038102538559212896839853)
          ·
            refine ⟨13139288451959704836314945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35038102538559212896839853 13139288451959704836314945)
            ·
              refine ⟨9854466338969778627236209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13139288451959704836314945 9854466338969778627236209)
              ·
                refine ⟨7390849754227333970427157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9854466338969778627236209 7390849754227333970427157)
                ·
                  refine ⟨346446082229406279863773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7390849754227333970427157 346446082229406279863773)
                  ·
                    rfl

theorem cell22_3036156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_3036156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036156 prefixEnd_3036156 := by exact prefixLift 3036156
  have htrace : WordTrace (prefixWord ++ tailWord_3036156) baseStart_3036156 baseEnd_3036156 := by
    simpa [prefixWord, tailWord_3036156, baseEnd_3036156] using wordTrace_append hprefix tailTrace_3036156
  have hstable : (prefixWord ++ tailWord_3036156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036156).length < 2 ^ (prefixWord ++ tailWord_3036156).sum := by decide
  have hdescent : baseEnd_3036156 < baseStart_3036156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036263 : List Nat := [1, 1, 5, 1, 1, 3, 2, 3, 5]
def baseStart_3036263 : Nat := 118140960795 + 3036263 * 2 ^ 59
def prefixEnd_3036263 : Nat := 4983230072969 + 3 ^ 40 * 3036263 * 2
def baseEnd_3036263 : Nat := 346458291658302075721997

theorem tailTrace_3036263 : CollatzResearch.WordTrace tailWord_3036263 prefixEnd_3036263 346458291658302075721997 := by
  unfold tailWord_3036263
  simp only [CollatzResearch.WordTrace]
  refine ⟨110741609399145178281441443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73827739599430118854294295 110741609399145178281441443)
  ·
    refine ⟨166112414098717767422162165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110741609399145178281441443 166112414098717767422162165)
    ·
      refine ⟨15573038821754790695827703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166112414098717767422162165 15573038821754790695827703)
      ·
        refine ⟨23359558232632186043741555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15573038821754790695827703 23359558232632186043741555)
        ·
          refine ⟨35039337348948279065612333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23359558232632186043741555 35039337348948279065612333)
          ·
            refine ⟨13139751505855604649604625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35039337348948279065612333 13139751505855604649604625)
            ·
              refine ⟨9854813629391703487203469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13139751505855604649604625 9854813629391703487203469)
              ·
                refine ⟨3695555111021888807701301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9854813629391703487203469 3695555111021888807701301)
                ·
                  refine ⟨346458291658302075721997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3695555111021888807701301 346458291658302075721997)
                  ·
                    rfl

theorem cell22_3036263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 5].length) (baseStart_3036263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036263 prefixEnd_3036263 := by exact prefixLift 3036263
  have htrace : WordTrace (prefixWord ++ tailWord_3036263) baseStart_3036263 baseEnd_3036263 := by
    simpa [prefixWord, tailWord_3036263, baseEnd_3036263] using wordTrace_append hprefix tailTrace_3036263
  have hstable : (prefixWord ++ tailWord_3036263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036263).length < 2 ^ (prefixWord ++ tailWord_3036263).sum := by decide
  have hdescent : baseEnd_3036263 < baseStart_3036263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036278 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_3036278 : Nat := 118140960795 + 3036278 * 2 ^ 59
def prefixEnd_3036278 : Nat := 4983230072969 + 3 ^ 40 * 3036278 * 2
def baseEnd_3036278 : Nat := 1039380009781451188040945

theorem tailTrace_3036278 : CollatzResearch.WordTrace tailWord_3036278 prefixEnd_3036278 1039380009781451188040945 := by
  unfold tailWord_3036278
  simp only [CollatzResearch.WordTrace]
  refine ⟨6921384780880677240202343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73828104329393890562158325 6921384780880677240202343)
  ·
    refine ⟨10382077171321015860303515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6921384780880677240202343 10382077171321015860303515)
    ·
      refine ⟨15573115756981523790455273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10382077171321015860303515 15573115756981523790455273)
      ·
        refine ⟨11679836817736142842841455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15573115756981523790455273 11679836817736142842841455)
        ·
          refine ⟨17519755226604214264262183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11679836817736142842841455 17519755226604214264262183)
          ·
            refine ⟨26279632839906321396393275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17519755226604214264262183 26279632839906321396393275)
            ·
              refine ⟨39419449259859482094589913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26279632839906321396393275 39419449259859482094589913)
              ·
                refine ⟨29564586944894611570942435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39419449259859482094589913 29564586944894611570942435)
                ·
                  refine ⟨44346880417341917356413653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29564586944894611570942435 44346880417341917356413653)
                  ·
                    refine ⟨1039380009781451188040945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44346880417341917356413653 1039380009781451188040945)
                    ·
                      rfl

theorem cell22_3036278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_3036278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036278 prefixEnd_3036278 := by exact prefixLift 3036278
  have htrace : WordTrace (prefixWord ++ tailWord_3036278) baseStart_3036278 baseEnd_3036278 := by
    simpa [prefixWord, tailWord_3036278, baseEnd_3036278] using wordTrace_append hprefix tailTrace_3036278
  have hstable : (prefixWord ++ tailWord_3036278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036278).length < 2 ^ (prefixWord ++ tailWord_3036278).sum := by decide
  have hdescent : baseEnd_3036278 < baseStart_3036278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036291 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 8]
def baseStart_3036291 : Nat := 118140960795 + 3036291 * 2 ^ 59
def prefixEnd_3036291 : Nat := 4983230072969 + 3 ^ 40 * 3036291 * 2
def baseEnd_3036291 : Nat := 346461486649041162488635

theorem tailTrace_3036291 : CollatzResearch.WordTrace tailWord_3036291 prefixEnd_3036291 346461486649041162488635 := by
  unfold tailWord_3036291
  simp only [CollatzResearch.WordTrace]
  refine ⟨110742630643043739063460727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73828420428695826042307151 110742630643043739063460727)
  ·
    refine ⟨166113945964565608595191091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110742630643043739063460727 166113945964565608595191091)
    ·
      refine ⟨249170918946848412892786637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166113945964565608595191091 249170918946848412892786637)
      ·
        refine ⟨93439094605068154834794989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249170918946848412892786637 93439094605068154834794989)
        ·
          refine ⟨35039660476900558063048121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93439094605068154834794989 35039660476900558063048121)
          ·
            refine ⟨26279745357675418547286091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35039660476900558063048121 26279745357675418547286091)
            ·
              refine ⟨39419618036513127820929137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26279745357675418547286091 39419618036513127820929137)
              ·
                refine ⟨29564713527384845865696853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39419618036513127820929137 29564713527384845865696853)
                ·
                  refine ⟨346461486649041162488635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29564713527384845865696853 346461486649041162488635)
                  ·
                    rfl

theorem cell22_3036291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 8].length) (baseStart_3036291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036291 prefixEnd_3036291 := by exact prefixLift 3036291
  have htrace : WordTrace (prefixWord ++ tailWord_3036291) baseStart_3036291 baseEnd_3036291 := by
    simpa [prefixWord, tailWord_3036291, baseEnd_3036291] using wordTrace_append hprefix tailTrace_3036291
  have hstable : (prefixWord ++ tailWord_3036291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036291).length < 2 ^ (prefixWord ++ tailWord_3036291).sum := by decide
  have hdescent : baseEnd_3036291 < baseStart_3036291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036327 : List Nat := [1, 1, 6, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3036327 : Nat := 118140960795 + 3036327 * 2 ^ 59
def prefixEnd_3036327 : Nat := 4983230072969 + 3 ^ 40 * 3036327 * 2
def baseEnd_3036327 : Nat := 1039396783482831393565795

theorem tailTrace_3036327 : CollatzResearch.WordTrace tailWord_3036327 prefixEnd_3036327 1039396783482831393565795 := by
  unfold tailWord_3036327
  simp only [CollatzResearch.WordTrace]
  refine ⟨110743943670913317211771235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73829295780608878141180823 110743943670913317211771235)
  ·
    refine ⟨166115915506369975817656853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110743943670913317211771235 166115915506369975817656853)
    ·
      refine ⟨7786683539361092616452665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 166115915506369975817656853 7786683539361092616452665)
      ·
        refine ⟨5840012654520819462339499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7786683539361092616452665 5840012654520819462339499)
        ·
          refine ⟨8760018981781229193509249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5840012654520819462339499 8760018981781229193509249)
          ·
            refine ⟨6570014236335921895131937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8760018981781229193509249 6570014236335921895131937)
            ·
              refine ⟨4927510677251941421348953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6570014236335921895131937 4927510677251941421348953)
              ·
                refine ⟨3695633007938956066011715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4927510677251941421348953 3695633007938956066011715)
                ·
                  refine ⟨5543449511908434099017573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3695633007938956066011715 5543449511908434099017573)
                  ·
                    refine ⟨1039396783482831393565795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5543449511908434099017573 1039396783482831393565795)
                    ·
                      rfl

theorem cell22_3036327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3036327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036327 prefixEnd_3036327 := by exact prefixLift 3036327
  have htrace : WordTrace (prefixWord ++ tailWord_3036327) baseStart_3036327 baseEnd_3036327 := by
    simpa [prefixWord, tailWord_3036327, baseEnd_3036327] using wordTrace_append hprefix tailTrace_3036327
  have hstable : (prefixWord ++ tailWord_3036327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036327).length < 2 ^ (prefixWord ++ tailWord_3036327).sum := by decide
  have hdescent : baseEnd_3036327 < baseStart_3036327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036336 : List Nat := [2, 1, 1, 1, 2, 1, 2, 12]
def baseStart_3036336 : Nat := 118140960795 + 3036336 * 2 ^ 59
def prefixEnd_3036336 : Nat := 4983230072969 + 3 ^ 40 * 3036336 * 2
def baseEnd_3036336 : Nat := 115488873818528707787863

theorem tailTrace_3036336 : CollatzResearch.WordTrace tailWord_3036336 prefixEnd_3036336 115488873818528707787863 := by
  unfold tailWord_3036336
  simp only [CollatzResearch.WordTrace]
  refine ⟨55372135963940355874424431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73829514618587141165899241 55372135963940355874424431)
  ·
    refine ⟨83058203945910533811636647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55372135963940355874424431 83058203945910533811636647)
    ·
      refine ⟨124587305918865800717454971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83058203945910533811636647 124587305918865800717454971)
      ·
        refine ⟨186880958878298701076182457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124587305918865800717454971 186880958878298701076182457)
        ·
          refine ⟨140160719158724025807136843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186880958878298701076182457 140160719158724025807136843)
          ·
            refine ⟨210241078738086038710705265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140160719158724025807136843 210241078738086038710705265)
            ·
              refine ⟨157680809053564529033028949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210241078738086038710705265 157680809053564529033028949)
              ·
                refine ⟨115488873818528707787863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 157680809053564529033028949 115488873818528707787863)
                ·
                  rfl

theorem cell22_3036336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 12].length) (baseStart_3036336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036336 prefixEnd_3036336 := by exact prefixLift 3036336
  have htrace : WordTrace (prefixWord ++ tailWord_3036336) baseStart_3036336 baseEnd_3036336 := by
    simpa [prefixWord, tailWord_3036336, baseEnd_3036336] using wordTrace_append hprefix tailTrace_3036336
  have hstable : (prefixWord ++ tailWord_3036336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036336).length < 2 ^ (prefixWord ++ tailWord_3036336).sum := by decide
  have hdescent : baseEnd_3036336 < baseStart_3036336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036338 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_3036338 : Nat := 118140960795 + 3036338 * 2 ^ 59
def prefixEnd_3036338 : Nat := 4983230072969 + 3 ^ 40 * 3036338 * 2
def baseEnd_3036338 : Nat := 1039400549007631031540761

theorem tailTrace_3036338 : CollatzResearch.WordTrace tailWord_3036338 prefixEnd_3036338 1039400549007631031540761 := by
  unfold tailWord_3036338
  simp only [CollatzResearch.WordTrace]
  refine ⟨27686086218468366522605417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73829563249248977393614445 27686086218468366522605417)
  ·
    refine ⟨20764564663851274891954063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27686086218468366522605417 20764564663851274891954063)
    ·
      refine ⟨31146846995776912337931095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20764564663851274891954063 31146846995776912337931095)
      ·
        refine ⟨46720270493665368506896643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31146846995776912337931095 46720270493665368506896643)
        ·
          refine ⟨70080405740498052760344965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46720270493665368506896643 70080405740498052760344965)
          ·
            refine ⟨13140076076343384892564681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70080405740498052760344965 13140076076343384892564681)
            ·
              refine ⟨9855057057257538669423511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13140076076343384892564681 9855057057257538669423511)
              ·
                refine ⟨14782585585886308004135267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9855057057257538669423511 14782585585886308004135267)
                ·
                  refine ⟨22173878378829462006202901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14782585585886308004135267 22173878378829462006202901)
                  ·
                    refine ⟨1039400549007631031540761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22173878378829462006202901 1039400549007631031540761)
                    ·
                      rfl

theorem cell22_3036338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_3036338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036338 prefixEnd_3036338 := by exact prefixLift 3036338
  have htrace : WordTrace (prefixWord ++ tailWord_3036338) baseStart_3036338 baseEnd_3036338 := by
    simpa [prefixWord, tailWord_3036338, baseEnd_3036338] using wordTrace_append hprefix tailTrace_3036338
  have hstable : (prefixWord ++ tailWord_3036338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036338).length < 2 ^ (prefixWord ++ tailWord_3036338).sum := by decide
  have hdescent : baseEnd_3036338 < baseStart_3036338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036398 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 9]
def baseStart_3036398 : Nat := 118140960795 + 3036398 * 2 ^ 59
def prefixEnd_3036398 : Nat := 4983230072969 + 3 ^ 40 * 3036398 * 2
def baseEnd_3036398 : Nat := 346473696077936958346859

theorem tailTrace_3036398 : CollatzResearch.WordTrace tailWord_3036398 prefixEnd_3036398 346473696077936958346859 := by
  unfold tailWord_3036398
  simp only [CollatzResearch.WordTrace]
  refine ⟨13843316656707012042200731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73831022169104064225070565 13843316656707012042200731)
  ·
    refine ⟨20764974985060518063301097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13843316656707012042200731 20764974985060518063301097)
    ·
      refine ⟨15573731238795388547475823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20764974985060518063301097 15573731238795388547475823)
      ·
        refine ⟨23360596858193082821213735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15573731238795388547475823 23360596858193082821213735)
        ·
          refine ⟨35040895287289624231820603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23360596858193082821213735 35040895287289624231820603)
          ·
            refine ⟨52561342930934436347730905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35040895287289624231820603 52561342930934436347730905)
            ·
              refine ⟨39421007198200827260798179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52561342930934436347730905 39421007198200827260798179)
              ·
                refine ⟨59131510797301240891197269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39421007198200827260798179 59131510797301240891197269)
                ·
                  refine ⟨346473696077936958346859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59131510797301240891197269 346473696077936958346859)
                  ·
                    rfl

theorem cell22_3036398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_3036398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036398 prefixEnd_3036398 := by exact prefixLift 3036398
  have htrace : WordTrace (prefixWord ++ tailWord_3036398) baseStart_3036398 baseEnd_3036398 := by
    simpa [prefixWord, tailWord_3036398, baseEnd_3036398] using wordTrace_append hprefix tailTrace_3036398
  have hstable : (prefixWord ++ tailWord_3036398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036398).length < 2 ^ (prefixWord ++ tailWord_3036398).sum := by decide
  have hdescent : baseEnd_3036398 < baseStart_3036398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036404 : List Nat := [2, 6, 1, 2, 2, 9]
def baseStart_3036404 : Nat := 118140960795 + 3036404 * 2 ^ 59
def prefixEnd_3036404 : Nat := 4983230072969 + 3 ^ 40 * 3036404 * 2
def baseEnd_3036404 : Nat := 12832384471067022955439

theorem tailTrace_3036404 : CollatzResearch.WordTrace tailWord_3036404 prefixEnd_3036404 12832384471067022955439 := by
  unfold tailWord_3036404
  simp only [CollatzResearch.WordTrace]
  refine ⟨55373376045817179681162133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73831168061089572908216177 55373376045817179681162133)
  ·
    refine ⟨2595627002147680297554475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55373376045817179681162133 2595627002147680297554475)
    ·
      refine ⟨3893440503221520446331713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2595627002147680297554475 3893440503221520446331713)
      ·
        refine ⟨2920080377416140334748785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3893440503221520446331713 2920080377416140334748785)
        ·
          refine ⟨2190060283062105251061589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2920080377416140334748785 2190060283062105251061589)
          ·
            refine ⟨12832384471067022955439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2190060283062105251061589 12832384471067022955439)
            ·
              rfl

theorem cell22_3036404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 9].length) (baseStart_3036404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036404 prefixEnd_3036404 := by exact prefixLift 3036404
  have htrace : WordTrace (prefixWord ++ tailWord_3036404) baseStart_3036404 baseEnd_3036404 := by
    simpa [prefixWord, tailWord_3036404, baseEnd_3036404] using wordTrace_append hprefix tailTrace_3036404
  have hstable : (prefixWord ++ tailWord_3036404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036404).length < 2 ^ (prefixWord ++ tailWord_3036404).sum := by decide
  have hdescent : baseEnd_3036404 < baseStart_3036404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036415 : List Nat := [1, 1, 2, 2, 1, 6, 2, 2, 5]
def baseStart_3036415 : Nat := 118140960795 + 3036415 * 2 ^ 59
def prefixEnd_3036415 : Nat := 4983230072969 + 3 ^ 40 * 3036415 * 2
def baseEnd_3036415 : Nat := 346475635893742832455175

theorem tailTrace_3036415 : CollatzResearch.WordTrace tailWord_3036415 prefixEnd_3036415 346475635893742832455175 := by
  unfold tailWord_3036415
  simp only [CollatzResearch.WordTrace]
  refine ⟨110747153294594508240974699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73831435529729672160649799 110747153294594508240974699)
  ·
    refine ⟨166120729941891762361462049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110747153294594508240974699 166120729941891762361462049)
    ·
      refine ⟨124590547456418821771096537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166120729941891762361462049 124590547456418821771096537)
      ·
        refine ⟨93442910592314116328322403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124590547456418821771096537 93442910592314116328322403)
        ·
          refine ⟨140164365888471174492483605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93442910592314116328322403 140164365888471174492483605)
          ·
            refine ⟨6570204651022086304335169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140164365888471174492483605 6570204651022086304335169)
            ·
              refine ⟨4927653488266564728251377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6570204651022086304335169 4927653488266564728251377)
              ·
                refine ⟨3695740116199923546188533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4927653488266564728251377 3695740116199923546188533)
                ·
                  refine ⟨346475635893742832455175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3695740116199923546188533 346475635893742832455175)
                  ·
                    rfl

theorem cell22_3036415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 5].length) (baseStart_3036415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036415 prefixEnd_3036415 := by exact prefixLift 3036415
  have htrace : WordTrace (prefixWord ++ tailWord_3036415) baseStart_3036415 baseEnd_3036415 := by
    simpa [prefixWord, tailWord_3036415, baseEnd_3036415] using wordTrace_append hprefix tailTrace_3036415
  have hstable : (prefixWord ++ tailWord_3036415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036415).length < 2 ^ (prefixWord ++ tailWord_3036415).sum := by decide
  have hdescent : baseEnd_3036415 < baseStart_3036415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036419 : List Nat := [1, 1, 1, 3, 2, 4, 4, 2, 1, 3]
def baseStart_3036419 : Nat := 118140960795 + 3036419 * 2 ^ 59
def prefixEnd_3036419 : Nat := 4983230072969 + 3 ^ 40 * 3036419 * 2
def baseEnd_3036419 : Nat := 1039428276962973820265513

theorem tailTrace_3036419 : CollatzResearch.WordTrace tailWord_3036419 prefixEnd_3036419 1039428276962973820265513 := by
  unfold tailWord_3036419
  simp only [CollatzResearch.WordTrace]
  refine ⟨110747299186580016924120311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73831532791053344616080207 110747299186580016924120311)
  ·
    refine ⟨166120948779870025386180467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110747299186580016924120311 166120948779870025386180467)
    ·
      refine ⟨249181423169805038079270701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166120948779870025386180467 249181423169805038079270701)
      ·
        refine ⟨93443033688676889279726513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249181423169805038079270701 93443033688676889279726513)
        ·
          refine ⟨70082275266507666959794885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93443033688676889279726513 70082275266507666959794885)
          ·
            refine ⟨13140426612470187554961541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70082275266507666959794885 13140426612470187554961541)
            ·
              refine ⟨2463829989838160166555289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13140426612470187554961541 2463829989838160166555289)
              ·
                refine ⟨1847872492378620124916467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2463829989838160166555289 1847872492378620124916467)
                ·
                  refine ⟨2771808738567930187374701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1847872492378620124916467 2771808738567930187374701)
                  ·
                    refine ⟨1039428276962973820265513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2771808738567930187374701 1039428276962973820265513)
                    ·
                      rfl

theorem cell22_3036419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 1, 3].length) (baseStart_3036419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036419 prefixEnd_3036419 := by exact prefixLift 3036419
  have htrace : WordTrace (prefixWord ++ tailWord_3036419) baseStart_3036419 baseEnd_3036419 := by
    simpa [prefixWord, tailWord_3036419, baseEnd_3036419] using wordTrace_append hprefix tailTrace_3036419
  have hstable : (prefixWord ++ tailWord_3036419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036419).length < 2 ^ (prefixWord ++ tailWord_3036419).sum := by decide
  have hdescent : baseEnd_3036419 < baseStart_3036419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036430 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_3036430 : Nat := 118140960795 + 3036430 * 2 ^ 59
def prefixEnd_3036430 : Nat := 4983230072969 + 3 ^ 40 * 3036430 * 2
def baseEnd_3036430 : Nat := 1039432042487773458240479

theorem tailTrace_3036430 : CollatzResearch.WordTrace tailWord_3036430 prefixEnd_3036430 1039432042487773458240479 := by
  unfold tailWord_3036430
  simp only [CollatzResearch.WordTrace]
  refine ⟨13843462548692520725346343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73831800259693443868513829 13843462548692520725346343)
  ·
    refine ⟨20765193823038781088019515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13843462548692520725346343 20765193823038781088019515)
    ·
      refine ⟨31147790734558171632029273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20765193823038781088019515 31147790734558171632029273)
      ·
        refine ⟨23360843050918628724021955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31147790734558171632029273 23360843050918628724021955)
        ·
          refine ⟨35041264576377943086032933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23360843050918628724021955 35041264576377943086032933)
          ·
            refine ⟨6570237108070864328631175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35041264576377943086032933 6570237108070864328631175)
            ·
              refine ⟨9855355662106296492946763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6570237108070864328631175 9855355662106296492946763)
              ·
                refine ⟨14783033493159444739420145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9855355662106296492946763 14783033493159444739420145)
                ·
                  refine ⟨11087275119869583554565109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14783033493159444739420145 11087275119869583554565109)
                  ·
                    refine ⟨1039432042487773458240479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11087275119869583554565109 1039432042487773458240479)
                    ·
                      rfl

theorem cell22_3036430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_3036430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036430 prefixEnd_3036430 := by exact prefixLift 3036430
  have htrace : WordTrace (prefixWord ++ tailWord_3036430) baseStart_3036430 baseEnd_3036430 := by
    simpa [prefixWord, tailWord_3036430, baseEnd_3036430] using wordTrace_append hprefix tailTrace_3036430
  have hstable : (prefixWord ++ tailWord_3036430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036430).length < 2 ^ (prefixWord ++ tailWord_3036430).sum := by decide
  have hdescent : baseEnd_3036430 < baseStart_3036430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036488 : List Nat := [2, 1, 3, 1, 1, 2, 1, 11]
def baseStart_3036488 : Nat := 118140960795 + 3036488 * 2 ^ 59
def prefixEnd_3036488 : Nat := 4983230072969 + 3 ^ 40 * 3036488 * 2
def baseEnd_3036488 : Nat := 115494655230342293365589

theorem tailTrace_3036488 : CollatzResearch.WordTrace tailWord_3036488 prefixEnd_3036488 115494655230342293365589 := by
  unfold tailWord_3036488
  simp only [CollatzResearch.WordTrace]
  refine ⟨55374907911665020854191059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73833210548886694472254745 55374907911665020854191059)
  ·
    refine ⟨83062361867497531281286589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55374907911665020854191059 83062361867497531281286589)
    ·
      refine ⟨31148385700311574230482471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83062361867497531281286589 31148385700311574230482471)
      ·
        refine ⟨46722578550467361345723707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31148385700311574230482471 46722578550467361345723707)
        ·
          refine ⟨70083867825701042018585561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46722578550467361345723707 70083867825701042018585561)
          ·
            refine ⟨52562900869275781513939171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70083867825701042018585561 52562900869275781513939171)
            ·
              refine ⟨78844351303913672270908757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52562900869275781513939171 78844351303913672270908757)
              ·
                refine ⟨115494655230342293365589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 78844351303913672270908757 115494655230342293365589)
                ·
                  rfl

theorem cell22_3036488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 11].length) (baseStart_3036488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036488 prefixEnd_3036488 := by exact prefixLift 3036488
  have htrace : WordTrace (prefixWord ++ tailWord_3036488) baseStart_3036488 baseEnd_3036488 := by
    simpa [prefixWord, tailWord_3036488, baseEnd_3036488] using wordTrace_append hprefix tailTrace_3036488
  have hstable : (prefixWord ++ tailWord_3036488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036488).length < 2 ^ (prefixWord ++ tailWord_3036488).sum := by decide
  have hdescent : baseEnd_3036488 < baseStart_3036488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036492 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 1, 5]
def baseStart_3036492 : Nat := 118140960795 + 3036492 * 2 ^ 59
def prefixEnd_3036492 : Nat := 4983230072969 + 3 ^ 40 * 3036492 * 2
def baseEnd_3036492 : Nat := 1039453266354825963190289

theorem tailTrace_3036492 : CollatzResearch.WordTrace tailWord_3036492 prefixEnd_3036492 1039453266354825963190289 := by
  unfold tailWord_3036492
  simp only [CollatzResearch.WordTrace]
  refine ⟨55374980857657775195763865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73833307810210366927685153 55374980857657775195763865)
  ·
    refine ⟨41531235643243331396822899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55374980857657775195763865 41531235643243331396822899)
    ·
      refine ⟨62296853464864997095234349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41531235643243331396822899 62296853464864997095234349)
      ·
        refine ⟨23361320049324373910712881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62296853464864997095234349 23361320049324373910712881)
        ·
          refine ⟨17520990036993280433034661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23361320049324373910712881 17520990036993280433034661)
          ·
            refine ⟨3285185631936240081193999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17520990036993280433034661 3285185631936240081193999)
            ·
              refine ⟨4927778447904360121790999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3285185631936240081193999 4927778447904360121790999)
              ·
                refine ⟨7391667671856540182686499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4927778447904360121790999 7391667671856540182686499)
                ·
                  refine ⟨11087501507784810274029749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7391667671856540182686499 11087501507784810274029749)
                  ·
                    refine ⟨1039453266354825963190289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11087501507784810274029749 1039453266354825963190289)
                    ·
                      rfl

theorem cell22_3036492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_3036492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036492 prefixEnd_3036492 := by exact prefixLift 3036492
  have htrace : WordTrace (prefixWord ++ tailWord_3036492) baseStart_3036492 baseEnd_3036492 := by
    simpa [prefixWord, tailWord_3036492, baseEnd_3036492] using wordTrace_append hprefix tailTrace_3036492
  have hstable : (prefixWord ++ tailWord_3036492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036492).length < 2 ^ (prefixWord ++ tailWord_3036492).sum := by decide
  have hdescent : baseEnd_3036492 < baseStart_3036492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036505 : List Nat := [1, 2, 1, 2, 2, 2, 6, 6]
def baseStart_3036505 : Nat := 118140960795 + 3036505 * 2 ^ 59
def prefixEnd_3036505 : Nat := 4983230072969 + 3 ^ 40 * 3036505 * 2
def baseEnd_3036505 : Nat := 115495301835610918068361

theorem tailTrace_3036505 : CollatzResearch.WordTrace tailWord_3036505 prefixEnd_3036505 115495301835610918068361 := by
  unfold tailWord_3036505
  simp only [CollatzResearch.WordTrace]
  refine ⟨110750435864268453611750969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73833623909512302407833979 110750435864268453611750969)
  ·
    refine ⟨83062826898201340208813227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110750435864268453611750969 83062826898201340208813227)
    ·
      refine ⟨124594240347302010313219841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83062826898201340208813227 124594240347302010313219841)
      ·
        refine ⟨93445680260476507734914881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124594240347302010313219841 93445680260476507734914881)
        ·
          refine ⟨70084260195357380801186161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93445680260476507734914881 70084260195357380801186161)
          ·
            refine ⟨52563195146518035600889621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70084260195357380801186161 52563195146518035600889621)
            ·
              refine ⟨2463899772493032918791701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52563195146518035600889621 2463899772493032918791701)
              ·
                refine ⟨115495301835610918068361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2463899772493032918791701 115495301835610918068361)
                ·
                  rfl

theorem cell22_3036505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 6].length) (baseStart_3036505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036505 prefixEnd_3036505 := by exact prefixLift 3036505
  have htrace : WordTrace (prefixWord ++ tailWord_3036505) baseStart_3036505 baseEnd_3036505 := by
    simpa [prefixWord, tailWord_3036505, baseEnd_3036505] using wordTrace_append hprefix tailTrace_3036505
  have hstable : (prefixWord ++ tailWord_3036505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036505).length < 2 ^ (prefixWord ++ tailWord_3036505).sum := by decide
  have hdescent : baseEnd_3036505 < baseStart_3036505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036522 : List Nat := [3, 1, 3, 3, 2, 2, 8]
def baseStart_3036522 : Nat := 118140960795 + 3036522 * 2 ^ 59
def prefixEnd_3036522 : Nat := 4983230072969 + 3 ^ 40 * 3036522 * 2
def baseEnd_3036522 : Nat := 38498649480293180923711

theorem tailTrace_3036522 : CollatzResearch.WordTrace tailWord_3036522 prefixEnd_3036522 38498649480293180923711 := by
  unfold tailWord_3036522
  simp only [CollatzResearch.WordTrace]
  refine ⟨27687763976301716378779955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73834037270137910343413213 27687763976301716378779955)
  ·
    refine ⟨41531645964452574568169933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27687763976301716378779955 41531645964452574568169933)
    ·
      refine ⟨15574367236669715463063725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41531645964452574568169933 15574367236669715463063725)
      ·
        refine ⟨5840387713751143298648897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15574367236669715463063725 5840387713751143298648897)
        ·
          refine ⟨4380290785313357473986673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5840387713751143298648897 4380290785313357473986673)
          ·
            refine ⟨3285218088985018105490005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4380290785313357473986673 3285218088985018105490005)
            ·
              refine ⟨38498649480293180923711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3285218088985018105490005 38498649480293180923711)
              ·
                rfl

theorem cell22_3036522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 8].length) (baseStart_3036522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036522 prefixEnd_3036522 := by exact prefixLift 3036522
  have htrace : WordTrace (prefixWord ++ tailWord_3036522) baseStart_3036522 baseEnd_3036522 := by
    simpa [prefixWord, tailWord_3036522, baseEnd_3036522] using wordTrace_append hprefix tailTrace_3036522
  have hstable : (prefixWord ++ tailWord_3036522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036522).length < 2 ^ (prefixWord ++ tailWord_3036522).sum := by decide
  have hdescent : baseEnd_3036522 < baseStart_3036522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036537 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 3, 3]
def baseStart_3036537 : Nat := 118140960795 + 3036537 * 2 ^ 59
def prefixEnd_3036537 : Nat := 4983230072969 + 3 ^ 40 * 3036537 * 2
def baseEnd_3036537 : Nat := 1039468670774460845815151

theorem tailTrace_3036537 : CollatzResearch.WordTrace tailWord_3036537 prefixEnd_3036537 1039468670774460845815151 := by
  unfold tailWord_3036537
  simp only [CollatzResearch.WordTrace]
  refine ⟨110751603000152523076915865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73834402000101682051277243 110751603000152523076915865)
  ·
    refine ⟨83063702250114392307686899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110751603000152523076915865 83063702250114392307686899)
    ·
      refine ⟨124595553375171588461530349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83063702250114392307686899 124595553375171588461530349)
      ·
        refine ⟨46723332515689345673073881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124595553375171588461530349 46723332515689345673073881)
        ·
          refine ⟨35042499386767009254805411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46723332515689345673073881 35042499386767009254805411)
          ·
            refine ⟨52563749080150513882208117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35042499386767009254805411 52563749080150513882208117)
            ·
              refine ⟨4927851476264110676457011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52563749080150513882208117 4927851476264110676457011)
              ·
                refine ⟨7391777214396166014685517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4927851476264110676457011 7391777214396166014685517)
                ·
                  refine ⟨2771916455398562255507069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7391777214396166014685517 2771916455398562255507069)
                  ·
                    refine ⟨1039468670774460845815151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2771916455398562255507069 1039468670774460845815151)
                    ·
                      rfl

theorem cell22_3036537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 3].length) (baseStart_3036537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036537 prefixEnd_3036537 := by exact prefixLift 3036537
  have htrace : WordTrace (prefixWord ++ tailWord_3036537) baseStart_3036537 baseEnd_3036537 := by
    simpa [prefixWord, tailWord_3036537, baseEnd_3036537] using wordTrace_append hprefix tailTrace_3036537
  have hstable : (prefixWord ++ tailWord_3036537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036537).length < 2 ^ (prefixWord ++ tailWord_3036537).sum := by decide
  have hdescent : baseEnd_3036537 < baseStart_3036537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036597 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 3, 4]
def baseStart_3036597 : Nat := 118140960795 + 3036597 * 2 ^ 59
def prefixEnd_3036597 : Nat := 4983230072969 + 3 ^ 40 * 3036597 * 2
def baseEnd_3036597 : Nat := 1039489210000640689314967

theorem tailTrace_3036597 : CollatzResearch.WordTrace tailWord_3036597 prefixEnd_3036597 1039489210000640689314967 := by
  unfold tailWord_3036597
  simp only [CollatzResearch.WordTrace]
  refine ⟨110753791379935153324100045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73835860919956768882733363 110753791379935153324100045)
  ·
    refine ⟨41532671767475682496537517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110753791379935153324100045 41532671767475682496537517)
    ·
      refine ⟨15574751912803380936201569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41532671767475682496537517 15574751912803380936201569)
      ·
        refine ⟨11681063934602535702151177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15574751912803380936201569 11681063934602535702151177)
        ·
          refine ⟨8760797950951901776613383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11681063934602535702151177 8760797950951901776613383)
          ·
            refine ⟨13141196926427852664920075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8760797950951901776613383 13141196926427852664920075)
            ·
              refine ⟨19711795389641778997380113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13141196926427852664920075 19711795389641778997380113)
              ·
                refine ⟨14783846542231334248035085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19711795389641778997380113 14783846542231334248035085)
                ·
                  refine ⟨5543942453336750343013157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14783846542231334248035085 5543942453336750343013157)
                  ·
                    refine ⟨1039489210000640689314967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5543942453336750343013157 1039489210000640689314967)
                    ·
                      rfl

theorem cell22_3036597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_3036597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036597 prefixEnd_3036597 := by exact prefixLift 3036597
  have htrace : WordTrace (prefixWord ++ tailWord_3036597) baseStart_3036597 baseEnd_3036597 := by
    simpa [prefixWord, tailWord_3036597, baseEnd_3036597] using wordTrace_append hprefix tailTrace_3036597
  have hstable : (prefixWord ++ tailWord_3036597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036597).length < 2 ^ (prefixWord ++ tailWord_3036597).sum := by decide
  have hdescent : baseEnd_3036597 < baseStart_3036597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036612 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 8]
def baseStart_3036612 : Nat := 118140960795 + 3036612 * 2 ^ 59
def prefixEnd_3036612 : Nat := 4983230072969 + 3 ^ 40 * 3036612 * 2
def baseEnd_3036612 : Nat := 346498114935728550063307

theorem tailTrace_3036612 : CollatzResearch.WordTrace tailWord_3036612 prefixEnd_3036612 346498114935728550063307 := by
  unfold tailWord_3036612
  simp only [CollatzResearch.WordTrace]
  refine ⟨55377169237440405442948045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73836225649920540590597393 55377169237440405442948045)
  ·
    refine ⟨20766438464040152041105517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55377169237440405442948045 20766438464040152041105517)
    ·
      refine ⟨7787414424015057015414569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20766438464040152041105517 7787414424015057015414569)
      ·
        refine ⟨5840560818011292761560927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7787414424015057015414569 5840560818011292761560927)
        ·
          refine ⟨8760841227016939142341391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5840560818011292761560927 8760841227016939142341391)
          ·
            refine ⟨13141261840525408713512087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8760841227016939142341391 13141261840525408713512087)
            ·
              refine ⟨19711892760788113070268131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13141261840525408713512087 19711892760788113070268131)
              ·
                refine ⟨29567839141182169605402197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19711892760788113070268131 29567839141182169605402197)
                ·
                  refine ⟨346498114935728550063307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29567839141182169605402197 346498114935728550063307)
                  ·
                    rfl

theorem cell22_3036612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_3036612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036612 prefixEnd_3036612 := by exact prefixLift 3036612
  have htrace : WordTrace (prefixWord ++ tailWord_3036612) baseStart_3036612 baseEnd_3036612 := by
    simpa [prefixWord, tailWord_3036612, baseEnd_3036612] using wordTrace_append hprefix tailTrace_3036612
  have hstable : (prefixWord ++ tailWord_3036612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036612).length < 2 ^ (prefixWord ++ tailWord_3036612).sum := by decide
  have hdescent : baseEnd_3036612 < baseStart_3036612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036629 : List Nat := [1, 3, 2, 3, 1, 1, 4, 3, 4]
def baseStart_3036629 : Nat := 118140960795 + 3036629 * 2 ^ 59
def prefixEnd_3036629 : Nat := 4983230072969 + 3 ^ 40 * 3036629 * 2
def baseEnd_3036629 : Nat := 346500054751534424171623

theorem tailTrace_3036629 : CollatzResearch.WordTrace tailWord_3036629 prefixEnd_3036629 346500054751534424171623 := by
  unfold tailWord_3036629
  simp only [CollatzResearch.WordTrace]
  refine ⟨110754958515819222789264941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73836639010546148526176627 110754958515819222789264941)
  ·
    refine ⟨41533109443432208545974353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110754958515819222789264941 41533109443432208545974353)
    ·
      refine ⟨31149832082574156409480765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41533109443432208545974353 31149832082574156409480765)
      ·
        refine ⟨11681187030965308653555287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31149832082574156409480765 11681187030965308653555287)
        ·
          refine ⟨17521780546447962980332931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11681187030965308653555287 17521780546447962980332931)
          ·
            refine ⟨26282670819671944470499397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17521780546447962980332931 26282670819671944470499397)
            ·
              refine ⟨4928000778688489588218637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26282670819671944470499397 4928000778688489588218637)
              ·
                refine ⟨1848000292008183595581989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4928000778688489588218637 1848000292008183595581989)
                ·
                  refine ⟨346500054751534424171623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1848000292008183595581989 346500054751534424171623)
                  ·
                    rfl

theorem cell22_3036629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_3036629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036629 prefixEnd_3036629 := by exact prefixLift 3036629
  have htrace : WordTrace (prefixWord ++ tailWord_3036629) baseStart_3036629 baseEnd_3036629 := by
    simpa [prefixWord, tailWord_3036629, baseEnd_3036629] using wordTrace_append hprefix tailTrace_3036629
  have hstable : (prefixWord ++ tailWord_3036629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036629).length < 2 ^ (prefixWord ++ tailWord_3036629).sum := by decide
  have hdescent : baseEnd_3036629 < baseStart_3036629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036661 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 1, 5]
def baseStart_3036661 : Nat := 118140960795 + 3036661 * 2 ^ 59
def prefixEnd_3036661 : Nat := 4983230072969 + 3 ^ 40 * 3036661 * 2
def baseEnd_3036661 : Nat := 1039511118508565855714771

theorem tailTrace_3036661 : CollatzResearch.WordTrace tailWord_3036661 prefixEnd_3036661 1039511118508565855714771 := by
  unfold tailWord_3036661
  simp only [CollatzResearch.WordTrace]
  refine ⟨110756125651703292254429837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73837417101135528169619891 110756125651703292254429837)
  ·
    refine ⟨41533547119388734595411189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110756125651703292254429837 41533547119388734595411189)
    ·
      refine ⟨3893770042442693868319799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41533547119388734595411189 3893770042442693868319799)
      ·
        refine ⟨5840655063664040802479699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3893770042442693868319799 5840655063664040802479699)
        ·
          refine ⟨8760982595496061203719549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5840655063664040802479699 8760982595496061203719549)
          ·
            refine ⟨3285368473311022951394831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8760982595496061203719549 3285368473311022951394831)
            ·
              refine ⟨4928052709966534427092247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3285368473311022951394831 4928052709966534427092247)
              ·
                refine ⟨7392079064949801640638371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4928052709966534427092247 7392079064949801640638371)
                ·
                  refine ⟨11088118597424702460957557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7392079064949801640638371 11088118597424702460957557)
                  ·
                    refine ⟨1039511118508565855714771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11088118597424702460957557 1039511118508565855714771)
                    ·
                      rfl

theorem cell22_3036661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_3036661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036661 prefixEnd_3036661 := by exact prefixLift 3036661
  have htrace : WordTrace (prefixWord ++ tailWord_3036661) baseStart_3036661 baseEnd_3036661 := by
    simpa [prefixWord, tailWord_3036661, baseEnd_3036661] using wordTrace_append hprefix tailTrace_3036661
  have hstable : (prefixWord ++ tailWord_3036661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036661).length < 2 ^ (prefixWord ++ tailWord_3036661).sum := by decide
  have hdescent : baseEnd_3036661 < baseStart_3036661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036674 : List Nat := [3, 4, 1, 2, 1, 2, 1, 8]
def baseStart_3036674 : Nat := 118140960795 + 3036674 * 2 ^ 59
def prefixEnd_3036674 : Nat := 4983230072969 + 3 ^ 40 * 3036674 * 2
def baseEnd_3036674 : Nat := 115501729852693128348859

theorem tailTrace_3036674 : CollatzResearch.WordTrace tailWord_3036674 prefixEnd_3036674 115501729852693128348859 := by
  unfold tailWord_3036674
  simp only [CollatzResearch.WordTrace]
  refine ⟨27689149950164048868663269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73837733200437463649768717 27689149950164048868663269)
  ·
    refine ⟨5191715615655759162874363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27689149950164048868663269 5191715615655759162874363)
    ·
      refine ⟨7787573423483638744311545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5191715615655759162874363 7787573423483638744311545)
      ·
        refine ⟨5840680067612729058233659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7787573423483638744311545 5840680067612729058233659)
        ·
          refine ⟨8761020101419093587350489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5840680067612729058233659 8761020101419093587350489)
          ·
            refine ⟨6570765076064320190512867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8761020101419093587350489 6570765076064320190512867)
            ·
              refine ⟨9856147614096480285769301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6570765076064320190512867 9856147614096480285769301)
              ·
                refine ⟨115501729852693128348859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9856147614096480285769301 115501729852693128348859)
                ·
                  rfl

theorem cell22_3036674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 8].length) (baseStart_3036674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036674 prefixEnd_3036674 := by exact prefixLift 3036674
  have htrace : WordTrace (prefixWord ++ tailWord_3036674) baseStart_3036674 baseEnd_3036674 := by
    simpa [prefixWord, tailWord_3036674, baseEnd_3036674] using wordTrace_append hprefix tailTrace_3036674
  have hstable : (prefixWord ++ tailWord_3036674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036674).length < 2 ^ (prefixWord ++ tailWord_3036674).sum := by decide
  have hdescent : baseEnd_3036674 < baseStart_3036674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036706 : List Nat := [3, 3, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_3036706 : Nat := 118140960795 + 3036706 * 2 ^ 59
def prefixEnd_3036706 : Nat := 4983230072969 + 3 ^ 40 * 3036706 * 2
def baseEnd_3036706 : Nat := 1039526522928200738339633

theorem tailTrace_3036706 : CollatzResearch.WordTrace tailWord_3036706 prefixEnd_3036706 1039526522928200738339633 := by
  unfold tailWord_3036706
  simp only [CollatzResearch.WordTrace]
  refine ⟨27689441734135066234954493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73838511291026843293211981 27689441734135066234954493)
  ·
    refine ⟨10383540650300649838107935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27689441734135066234954493 10383540650300649838107935)
    ·
      refine ⟨15575310975450974757161903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10383540650300649838107935 15575310975450974757161903)
      ·
        refine ⟨23362966463176462135742855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15575310975450974757161903 23362966463176462135742855)
        ·
          refine ⟨35044449694764693203614283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23362966463176462135742855 35044449694764693203614283)
          ·
            refine ⟨52566674542147039805421425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35044449694764693203614283 52566674542147039805421425)
            ·
              refine ⟨39425005906610279854066069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52566674542147039805421425 39425005906610279854066069)
              ·
                refine ⟨1848047151872356868159347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39425005906610279854066069 1848047151872356868159347)
                ·
                  refine ⟨2772070727808535302239021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1848047151872356868159347 2772070727808535302239021)
                  ·
                    refine ⟨1039526522928200738339633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2772070727808535302239021 1039526522928200738339633)
                    ·
                      rfl

theorem cell22_3036706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_3036706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036706 prefixEnd_3036706 := by exact prefixLift 3036706
  have htrace : WordTrace (prefixWord ++ tailWord_3036706) baseStart_3036706 baseEnd_3036706 := by
    simpa [prefixWord, tailWord_3036706, baseEnd_3036706] using wordTrace_append hprefix tailTrace_3036706
  have hstable : (prefixWord ++ tailWord_3036706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036706).length < 2 ^ (prefixWord ++ tailWord_3036706).sum := by decide
  have hdescent : baseEnd_3036706 < baseStart_3036706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036715 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 1, 10]
def baseStart_3036715 : Nat := 118140960795 + 3036715 * 2 ^ 59
def prefixEnd_3036715 : Nat := 4983230072969 + 3 ^ 40 * 3036715 * 2
def baseEnd_3036715 : Nat := 1039529603812127714864605

theorem tailTrace_3036715 : CollatzResearch.WordTrace tailWord_3036715 prefixEnd_3036715 1039529603812127714864605 := by
  unfold tailWord_3036715
  simp only [CollatzResearch.WordTrace]
  refine ⟨110758095193507659476895599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73838730129005106317930399 110758095193507659476895599)
  ·
    refine ⟨166137142790261489215343399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110758095193507659476895599 166137142790261489215343399)
    ·
      refine ⟨249205714185392233823015099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166137142790261489215343399 249205714185392233823015099)
      ·
        refine ⟨373808571278088350734522649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249205714185392233823015099 373808571278088350734522649)
        ·
          refine ⟨280356428458566263050891987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373808571278088350734522649 280356428458566263050891987)
          ·
            refine ⟨420534642687849394576337981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280356428458566263050891987 420534642687849394576337981)
            ·
              refine ⟨157700491007943522966126743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 420534642687849394576337981 157700491007943522966126743)
              ·
                refine ⟨236550736511915284449190115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157700491007943522966126743 236550736511915284449190115)
                ·
                  refine ⟨354826104767872926673785173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236550736511915284449190115 354826104767872926673785173)
                  ·
                    refine ⟨1039529603812127714864605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 354826104767872926673785173 1039529603812127714864605)
                    ·
                      rfl

theorem cell22_3036715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 10].length) (baseStart_3036715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036715 prefixEnd_3036715 := by exact prefixLift 3036715
  have htrace : WordTrace (prefixWord ++ tailWord_3036715) baseStart_3036715 baseEnd_3036715 := by
    simpa [prefixWord, tailWord_3036715, baseEnd_3036715] using wordTrace_append hprefix tailTrace_3036715
  have hstable : (prefixWord ++ tailWord_3036715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036715).length < 2 ^ (prefixWord ++ tailWord_3036715).sum := by decide
  have hdescent : baseEnd_3036715 < baseStart_3036715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036777 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 4, 4]
def baseStart_3036777 : Nat := 118140960795 + 3036777 * 2 ^ 59
def prefixEnd_3036777 : Nat := 4983230072969 + 3 ^ 40 * 3036777 * 2
def baseEnd_3036777 : Nat := 1039550827679180219814415

theorem tailTrace_3036777 : CollatzResearch.WordTrace tailWord_3036777 prefixEnd_3036777 1039550827679180219814415 := by
  unfold tailWord_3036777
  simp only [CollatzResearch.WordTrace]
  refine ⟨110760356519283044065652585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73840237679522029377101723 110760356519283044065652585)
  ·
    refine ⟨83070267389462283049239439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110760356519283044065652585 83070267389462283049239439)
    ·
      refine ⟨124605401084193424573859159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83070267389462283049239439 124605401084193424573859159)
      ·
        refine ⟨186908101626290136860788739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124605401084193424573859159 186908101626290136860788739)
        ·
          refine ⟨280362152439435205291183109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186908101626290136860788739 280362152439435205291183109)
          ·
            refine ⟨52567903582394100992096833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280362152439435205291183109 52567903582394100992096833)
            ·
              refine ⟨39425927686795575744072625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52567903582394100992096833 39425927686795575744072625)
              ·
                refine ⟨29569445765096681808054469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39425927686795575744072625 29569445765096681808054469)
                ·
                  refine ⟨5544271080955627839010213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29569445765096681808054469 5544271080955627839010213)
                  ·
                    refine ⟨1039550827679180219814415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5544271080955627839010213 1039550827679180219814415)
                    ·
                      rfl

theorem cell22_3036777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_3036777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036777 prefixEnd_3036777 := by exact prefixLift 3036777
  have htrace : WordTrace (prefixWord ++ tailWord_3036777) baseStart_3036777 baseEnd_3036777 := by
    simpa [prefixWord, tailWord_3036777, baseEnd_3036777] using wordTrace_append hprefix tailTrace_3036777
  have hstable : (prefixWord ++ tailWord_3036777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036777).length < 2 ^ (prefixWord ++ tailWord_3036777).sum := by decide
  have hdescent : baseEnd_3036777 < baseStart_3036777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036830 : List Nat := [4, 3, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_3036830 : Nat := 118140960795 + 3036830 * 2 ^ 59
def prefixEnd_3036830 : Nat := 4983230072969 + 3 ^ 40 * 3036830 * 2
def baseEnd_3036830 : Nat := 1039568970662305748239253

theorem tailTrace_3036830 : CollatzResearch.WordTrace tailWord_3036830 prefixEnd_3036830 1039568970662305748239253 := by
  unfold tailWord_3036830
  simp only [CollatzResearch.WordTrace]
  refine ⟨13845286198511379264666493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73841526392060689411554629 13845286198511379264666493)
  ·
    refine ⟨5191982324441767224249935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13845286198511379264666493 5191982324441767224249935)
    ·
      refine ⟨7787973486662650836374903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5191982324441767224249935 7787973486662650836374903)
      ·
        refine ⟨11681960229993976254562355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7787973486662650836374903 11681960229993976254562355)
        ·
          refine ⟨17522940344990964381843533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11681960229993976254562355 17522940344990964381843533)
          ·
            refine ⟨6571102629371611643191325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17522940344990964381843533 6571102629371611643191325)
            ·
              refine ⟨2464163486014354366196747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6571102629371611643191325 2464163486014354366196747)
              ·
                refine ⟨3696245229021531549295121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2464163486014354366196747 3696245229021531549295121)
                ·
                  refine ⟨2772183921766148661971341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3696245229021531549295121 2772183921766148661971341)
                  ·
                    refine ⟨1039568970662305748239253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2772183921766148661971341 1039568970662305748239253)
                    ·
                      rfl

theorem cell22_3036830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_3036830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036830 prefixEnd_3036830 := by exact prefixLift 3036830
  have htrace : WordTrace (prefixWord ++ tailWord_3036830) baseStart_3036830 baseEnd_3036830 := by
    simpa [prefixWord, tailWord_3036830, baseEnd_3036830] using wordTrace_append hprefix tailTrace_3036830
  have hstable : (prefixWord ++ tailWord_3036830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036830).length < 2 ^ (prefixWord ++ tailWord_3036830).sum := by decide
  have hdescent : baseEnd_3036830 < baseStart_3036830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036858 : List Nat := [3, 1, 1, 1, 2, 4, 3, 3, 1, 3]
def baseStart_3036858 : Nat := 118140960795 + 3036858 * 2 ^ 59
def prefixEnd_3036858 : Nat := 4983230072969 + 3 ^ 40 * 3036858 * 2
def baseEnd_3036858 : Nat := 1039578555634523008539167

theorem tailTrace_3036858 : CollatzResearch.WordTrace tailWord_3036858 prefixEnd_3036858 1039578555634523008539167 := by
  unfold tailWord_3036858
  simp only [CollatzResearch.WordTrace]
  refine ⟨27690827707997398724837807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73842207221326396599567485 27690827707997398724837807)
  ·
    refine ⟨41536241561996098087256711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27690827707997398724837807 41536241561996098087256711)
    ·
      refine ⟨62304362342994147130885067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41536241561996098087256711 62304362342994147130885067)
      ·
        refine ⟨93456543514491220696327601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62304362342994147130885067 93456543514491220696327601)
        ·
          refine ⟨70092407635868415522245701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93456543514491220696327601 70092407635868415522245701)
          ·
            refine ⟨13142326431725327910421069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70092407635868415522245701 13142326431725327910421069)
            ·
              refine ⟨4928372411896997966407901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13142326431725327910421069 4928372411896997966407901)
              ·
                refine ⟨1848139654461374237402963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4928372411896997966407901 1848139654461374237402963)
                ·
                  refine ⟨2772209481692061356104445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1848139654461374237402963 2772209481692061356104445)
                  ·
                    refine ⟨1039578555634523008539167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2772209481692061356104445 1039578555634523008539167)
                    ·
                      rfl

theorem cell22_3036858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_3036858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036858 prefixEnd_3036858 := by exact prefixLift 3036858
  have htrace : WordTrace (prefixWord ++ tailWord_3036858) baseStart_3036858 baseEnd_3036858 := by
    simpa [prefixWord, tailWord_3036858, baseEnd_3036858] using wordTrace_append hprefix tailTrace_3036858
  have hstable : (prefixWord ++ tailWord_3036858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036858).length < 2 ^ (prefixWord ++ tailWord_3036858).sum := by decide
  have hdescent : baseEnd_3036858 < baseStart_3036858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036931 : List Nat := [1, 1, 1, 3, 2, 2, 3, 4, 2, 3]
def baseStart_3036931 : Nat := 118140960795 + 3036931 * 2 ^ 59
def prefixEnd_3036931 : Nat := 4983230072969 + 3 ^ 40 * 3036931 * 2
def baseEnd_3036931 : Nat := 1039603545026375151463943

theorem tailTrace_3036931 : CollatzResearch.WordTrace tailWord_3036931 prefixEnd_3036931 1039603545026375151463943 := by
  unfold tailWord_3036931
  simp only [CollatzResearch.WordTrace]
  refine ⟨110765973360725128366758647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73843982240483418911172431 110765973360725128366758647)
  ·
    refine ⟨166148960041087692550137971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110765973360725128366758647 166148960041087692550137971)
    ·
      refine ⟨249223440061631538825206957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166148960041087692550137971 249223440061631538825206957)
      ·
        refine ⟨93458790023111827059452609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249223440061631538825206957 93458790023111827059452609)
        ·
          refine ⟨70094092517333870294589457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93458790023111827059452609 70094092517333870294589457)
          ·
            refine ⟨52570569388000402720942093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70094092517333870294589457 52570569388000402720942093)
            ·
              refine ⟨19713963520500151020353285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52570569388000402720942093 19713963520500151020353285)
              ·
                refine ⟨3696368160093778316316241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19713963520500151020353285 3696368160093778316316241)
                ·
                  refine ⟨2772276120070333737237181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3696368160093778316316241 2772276120070333737237181)
                  ·
                    refine ⟨1039603545026375151463943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2772276120070333737237181 1039603545026375151463943)
                    ·
                      rfl

theorem cell22_3036931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 3].length) (baseStart_3036931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036931 prefixEnd_3036931 := by exact prefixLift 3036931
  have htrace : WordTrace (prefixWord ++ tailWord_3036931) baseStart_3036931 baseEnd_3036931 := by
    simpa [prefixWord, tailWord_3036931, baseEnd_3036931] using wordTrace_append hprefix tailTrace_3036931
  have hstable : (prefixWord ++ tailWord_3036931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036931).length < 2 ^ (prefixWord ++ tailWord_3036931).sum := by decide
  have hdescent : baseEnd_3036931 < baseStart_3036931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036961 : List Nat := [1, 2, 3, 2, 1, 4, 3, 6]
def baseStart_3036961 : Nat := 118140960795 + 3036961 * 2 ^ 59
def prefixEnd_3036961 : Nat := 4983230072969 + 3 ^ 40 * 3036961 * 2
def baseEnd_3036961 : Nat := 115512646071051674801539

theorem tailTrace_3036961 : CollatzResearch.WordTrace tailWord_3036961 prefixEnd_3036961 115512646071051674801539 := by
  unfold tailWord_3036961
  simp only [CollatzResearch.WordTrace]
  refine ⟨110767067550616443490350737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73844711700410962326900491 110767067550616443490350737)
  ·
    refine ⟨83075300662962332617763053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110767067550616443490350737 83075300662962332617763053)
    ·
      refine ⟨31153237748610874731661145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83075300662962332617763053 31153237748610874731661145)
      ·
        refine ⟨23364928311458156048745859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31153237748610874731661145 23364928311458156048745859)
        ·
          refine ⟨35047392467187234073118789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23364928311458156048745859 35047392467187234073118789)
          ·
            refine ⟨6571386087597606388709773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35047392467187234073118789 6571386087597606388709773)
            ·
              refine ⟨2464269782849102395766165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6571386087597606388709773 2464269782849102395766165)
              ·
                refine ⟨115512646071051674801539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2464269782849102395766165 115512646071051674801539)
                ·
                  rfl

theorem cell22_3036961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 6].length) (baseStart_3036961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036961 prefixEnd_3036961 := by exact prefixLift 3036961
  have htrace : WordTrace (prefixWord ++ tailWord_3036961) baseStart_3036961 baseEnd_3036961 := by
    simpa [prefixWord, tailWord_3036961, baseEnd_3036961] using wordTrace_append hprefix tailTrace_3036961
  have hstable : (prefixWord ++ tailWord_3036961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036961).length < 2 ^ (prefixWord ++ tailWord_3036961).sum := by decide
  have hdescent : baseEnd_3036961 < baseStart_3036961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036982 : List Nat := [5, 1, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_3036982 : Nat := 118140960795 + 3036982 * 2 ^ 59
def prefixEnd_3036982 : Nat := 4983230072969 + 3 ^ 40 * 3036982 * 2
def baseEnd_3036982 : Nat := 1039621003368628018438787

theorem tailTrace_3036982 : CollatzResearch.WordTrace tailWord_3036982 prefixEnd_3036982 1039621003368628018438787 := by
  unfold tailWord_3036982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6922989592721272754804075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73845222322360242717910133 6922989592721272754804075)
  ·
    refine ⟨10384484389081909132206113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6922989592721272754804075 10384484389081909132206113)
    ·
      refine ⟨7788363291811431849154585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10384484389081909132206113 7788363291811431849154585)
      ·
        refine ⟨5841272468858573886865939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7788363291811431849154585 5841272468858573886865939)
        ·
          refine ⟨8761908703287860830298909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5841272468858573886865939 8761908703287860830298909)
          ·
            refine ⟨3285715763732947811362091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8761908703287860830298909 3285715763732947811362091)
            ·
              refine ⟨4928573645599421717043137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3285715763732947811362091 4928573645599421717043137)
              ·
                refine ⟨3696430234199566287782353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4928573645599421717043137 3696430234199566287782353)
                ·
                  refine ⟨2772322675649674715836765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3696430234199566287782353 2772322675649674715836765)
                  ·
                    refine ⟨1039621003368628018438787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2772322675649674715836765 1039621003368628018438787)
                    ·
                      rfl

theorem cell22_3036982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_3036982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3036982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3036982 prefixEnd_3036982 := by exact prefixLift 3036982
  have htrace : WordTrace (prefixWord ++ tailWord_3036982) baseStart_3036982 baseEnd_3036982 := by
    simpa [prefixWord, tailWord_3036982, baseEnd_3036982] using wordTrace_append hprefix tailTrace_3036982
  have hstable : (prefixWord ++ tailWord_3036982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036982).length < 2 ^ (prefixWord ++ tailWord_3036982).sum := by decide
  have hdescent : baseEnd_3036982 < baseStart_3036982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037027 : List Nat := [1, 1, 1, 5, 4, 2, 1, 3, 1, 3]
def baseStart_3037027 : Nat := 118140960795 + 3037027 * 2 ^ 59
def prefixEnd_3037027 : Nat := 4983230072969 + 3 ^ 40 * 3037027 * 2
def baseEnd_3037027 : Nat := 1039636407788262901063649

theorem tailTrace_3037027 : CollatzResearch.WordTrace tailWord_3037027 prefixEnd_3037027 1039636407788262901063649 := by
  unfold tailWord_3037027
  simp only [CollatzResearch.WordTrace]
  refine ⟨110769474768377336762253335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73846316512251557841502223 110769474768377336762253335)
  ·
    refine ⟨166154212152566005143380003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110769474768377336762253335 166154212152566005143380003)
    ·
      refine ⟨249231318228849007715070005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166154212152566005143380003 249231318228849007715070005)
      ·
        refine ⟨23365436083954594473287813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 249231318228849007715070005 23365436083954594473287813)
        ·
          refine ⟨4381019265741486463741465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23365436083954594473287813 4381019265741486463741465)
          ·
            refine ⟨3285764449306114847806099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4381019265741486463741465 3285764449306114847806099)
            ·
              refine ⟨4928646673959172271709149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3285764449306114847806099 4928646673959172271709149)
              ·
                refine ⟨1848242502734689601890931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4928646673959172271709149 1848242502734689601890931)
                ·
                  refine ⟨2772363754102034402836397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1848242502734689601890931 2772363754102034402836397)
                  ·
                    refine ⟨1039636407788262901063649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2772363754102034402836397 1039636407788262901063649)
                    ·
                      rfl

theorem cell22_3037027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 1, 3].length) (baseStart_3037027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037027 prefixEnd_3037027 := by exact prefixLift 3037027
  have htrace : WordTrace (prefixWord ++ tailWord_3037027) baseStart_3037027 baseEnd_3037027 := by
    simpa [prefixWord, tailWord_3037027, baseEnd_3037027] using wordTrace_append hprefix tailTrace_3037027
  have hstable : (prefixWord ++ tailWord_3037027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037027).length < 2 ^ (prefixWord ++ tailWord_3037027).sum := by decide
  have hdescent : baseEnd_3037027 < baseStart_3037027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037057 : List Nat := [1, 2, 4, 4, 1, 2, 2, 1, 5]
def baseStart_3037057 : Nat := 118140960795 + 3037057 * 2 ^ 59
def prefixEnd_3037057 : Nat := 4983230072969 + 3 ^ 40 * 3037057 * 2
def baseEnd_3037057 : Nat := 346548892467117607604519

theorem tailTrace_3037057 : CollatzResearch.WordTrace tailWord_3037057 prefixEnd_3037057 346548892467117607604519 := by
  unfold tailWord_3037057
  simp only [CollatzResearch.WordTrace]
  refine ⟨110770568958268651885845425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73847045972179101257230283 110770568958268651885845425)
  ·
    refine ⟨83077926718701488914384069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110770568958268651885845425 83077926718701488914384069)
    ·
      refine ⟨15577111259756529171447013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83077926718701488914384069 15577111259756529171447013)
      ·
        refine ⟨2920708361204349219646315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15577111259756529171447013 2920708361204349219646315)
        ·
          refine ⟨4381062541806523829469473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2920708361204349219646315 4381062541806523829469473)
          ·
            refine ⟨3285796906354892872102105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4381062541806523829469473 3285796906354892872102105)
            ·
              refine ⟨2464347679766169654076579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3285796906354892872102105 2464347679766169654076579)
              ·
                refine ⟨3696521519649254481114869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2464347679766169654076579 3696521519649254481114869)
                ·
                  refine ⟨346548892467117607604519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3696521519649254481114869 346548892467117607604519)
                  ·
                    rfl

theorem cell22_3037057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 5].length) (baseStart_3037057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037057 prefixEnd_3037057 := by exact prefixLift 3037057
  have htrace : WordTrace (prefixWord ++ tailWord_3037057) baseStart_3037057 baseEnd_3037057 := by
    simpa [prefixWord, tailWord_3037057, baseEnd_3037057] using wordTrace_append hprefix tailTrace_3037057
  have hstable : (prefixWord ++ tailWord_3037057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037057).length < 2 ^ (prefixWord ++ tailWord_3037057).sum := by decide
  have hdescent : baseEnd_3037057 < baseStart_3037057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037070 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 3, 4]
def baseStart_3037070 : Nat := 118140960795 + 3037070 * 2 ^ 59
def prefixEnd_3037070 : Nat := 4983230072969 + 3 ^ 40 * 3037070 * 2
def baseEnd_3037070 : Nat := 1039651127567025122238517

theorem tailTrace_3037070 : CollatzResearch.WordTrace tailWord_3037070 prefixEnd_3037070 1039651127567025122238517 := by
  unfold tailWord_3037070
  simp only [CollatzResearch.WordTrace]
  refine ⟨13846380388402694388258583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73847362071481036737379109 13846380388402694388258583)
  ·
    refine ⟨20769570582604041582387875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13846380388402694388258583 20769570582604041582387875)
    ·
      refine ⟨31154355873906062373581813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20769570582604041582387875 31154355873906062373581813)
      ·
        refine ⟨2920720863178693347523295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31154355873906062373581813 2920720863178693347523295)
        ·
          refine ⟨4381081294768040021284943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2920720863178693347523295 4381081294768040021284943)
          ·
            refine ⟨6571621942152060031927415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4381081294768040021284943 6571621942152060031927415)
            ·
              refine ⟨9857432913228090047891123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6571621942152060031927415 9857432913228090047891123)
              ·
                refine ⟨14786149369842135071836685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9857432913228090047891123 14786149369842135071836685)
                ·
                  refine ⟨5544806013690800651938757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14786149369842135071836685 5544806013690800651938757)
                  ·
                    refine ⟨1039651127567025122238517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5544806013690800651938757 1039651127567025122238517)
                    ·
                      rfl

theorem cell22_3037070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_3037070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037070 prefixEnd_3037070 := by exact prefixLift 3037070
  have htrace : WordTrace (prefixWord ++ tailWord_3037070) baseStart_3037070 baseEnd_3037070 := by
    simpa [prefixWord, tailWord_3037070, baseEnd_3037070] using wordTrace_append hprefix tailTrace_3037070
  have hstable : (prefixWord ++ tailWord_3037070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037070).length < 2 ^ (prefixWord ++ tailWord_3037070).sum := by decide
  have hdescent : baseEnd_3037070 < baseStart_3037070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037081 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 2, 4]
def baseStart_3037081 : Nat := 118140960795 + 3037081 * 2 ^ 59
def prefixEnd_3037081 : Nat := 4983230072969 + 3 ^ 40 * 3037081 * 2
def baseEnd_3037081 : Nat := 1039654893091824760213483

theorem tailTrace_3037081 : CollatzResearch.WordTrace tailWord_3037081 prefixEnd_3037081 1039654893091824760213483 := by
  unfold tailWord_3037081
  simp only [CollatzResearch.WordTrace]
  refine ⟨110771444310181703984719097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73847629540121135989812731 110771444310181703984719097)
  ·
    refine ⟨83078583232636277988539323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110771444310181703984719097 83078583232636277988539323)
    ·
      refine ⟨124617874848954416982808985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83078583232636277988539323 124617874848954416982808985)
      ·
        refine ⟨93463406136715812737106739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124617874848954416982808985 93463406136715812737106739)
        ·
          refine ⟨140195109205073719105660109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93463406136715812737106739 140195109205073719105660109)
          ·
            refine ⟨52573165951902644664622541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140195109205073719105660109 52573165951902644664622541)
            ·
              refine ⟨19714937231963491749233453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52573165951902644664622541 19714937231963491749233453)
              ·
                refine ⟨7393101461986309405962545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19714937231963491749233453 7393101461986309405962545)
                ·
                  refine ⟨5544826096489732054471909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7393101461986309405962545 5544826096489732054471909)
                  ·
                    refine ⟨1039654893091824760213483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5544826096489732054471909 1039654893091824760213483)
                    ·
                      rfl

theorem cell22_3037081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_3037081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037081 prefixEnd_3037081 := by exact prefixLift 3037081
  have htrace : WordTrace (prefixWord ++ tailWord_3037081) baseStart_3037081 baseEnd_3037081 := by
    simpa [prefixWord, tailWord_3037081, baseEnd_3037081] using wordTrace_append hprefix tailTrace_3037081
  have hstable : (prefixWord ++ tailWord_3037081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037081).length < 2 ^ (prefixWord ++ tailWord_3037081).sum := by decide
  have hdescent : baseEnd_3037081 < baseStart_3037081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037128 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 5, 3]
def baseStart_3037128 : Nat := 118140960795 + 3037128 * 2 ^ 59
def prefixEnd_3037128 : Nat := 4983230072969 + 3 ^ 40 * 3037128 * 2
def baseEnd_3037128 : Nat := 1039670982152332304288339

theorem tailTrace_3037128 : CollatzResearch.WordTrace tailWord_3037128 prefixEnd_3037128 1039670982152332304288339 := by
  unfold tailWord_3037128
  simp only [CollatzResearch.WordTrace]
  refine ⟨55386579270505715505840019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73848772360674287341120025 55386579270505715505840019)
  ·
    refine ⟨83079868905758573258760029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55386579270505715505840019 83079868905758573258760029)
    ·
      refine ⟨31154950839659464972035011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83079868905758573258760029 31154950839659464972035011)
      ·
        refine ⟨46732426259489197458052517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31154950839659464972035011 46732426259489197458052517)
        ·
          refine ⟨8762329923654224523384847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46732426259489197458052517 8762329923654224523384847)
          ·
            refine ⟨13143494885481336785077271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8762329923654224523384847 13143494885481336785077271)
            ·
              refine ⟨19715242328222005177615907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13143494885481336785077271 19715242328222005177615907)
              ·
                refine ⟨29572863492333007766423861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19715242328222005177615907 29572863492333007766423861)
                ·
                  refine ⟨2772455952406219478102237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29572863492333007766423861 2772455952406219478102237)
                  ·
                    refine ⟨1039670982152332304288339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2772455952406219478102237 1039670982152332304288339)
                    ·
                      rfl

theorem cell22_3037128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_3037128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037128 prefixEnd_3037128 := by exact prefixLift 3037128
  have htrace : WordTrace (prefixWord ++ tailWord_3037128) baseStart_3037128 baseEnd_3037128 := by
    simpa [prefixWord, tailWord_3037128, baseEnd_3037128] using wordTrace_append hprefix tailTrace_3037128
  have hstable : (prefixWord ++ tailWord_3037128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037128).length < 2 ^ (prefixWord ++ tailWord_3037128).sum := by decide
  have hdescent : baseEnd_3037128 < baseStart_3037128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037156 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_3037156 : Nat := 118140960795 + 3037156 * 2 ^ 59
def prefixEnd_3037156 : Nat := 4983230072969 + 3 ^ 40 * 3037156 * 2
def baseEnd_3037156 : Nat := 1039680567124549564588253

theorem tailTrace_3037156 : CollatzResearch.WordTrace tailWord_3037156 prefixEnd_3037156 1039680567124549564588253 := by
  unfold tailWord_3037156
  simp only [CollatzResearch.WordTrace]
  refine ⟨55387089892454995896849661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73849453189939994529132881 55387089892454995896849661)
  ·
    refine ⟨20770158709670623461318623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55387089892454995896849661 20770158709670623461318623)
    ·
      refine ⟨31155238064505935191977935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20770158709670623461318623 31155238064505935191977935)
      ·
        refine ⟨46732857096758902787966903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31155238064505935191977935 46732857096758902787966903)
        ·
          refine ⟨70099285645138354181950355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46732857096758902787966903 70099285645138354181950355)
          ·
            refine ⟨105148928467707531272925533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70099285645138354181950355 105148928467707531272925533)
            ·
              refine ⟨39430848175390324227347075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105148928467707531272925533 39430848175390324227347075)
              ·
                refine ⟨59146272263085486341020613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39430848175390324227347075 59146272263085486341020613)
                ·
                  refine ⟨11089926049328528688941365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59146272263085486341020613 11089926049328528688941365)
                  ·
                    refine ⟨1039680567124549564588253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11089926049328528688941365 1039680567124549564588253)
                    ·
                      rfl

theorem cell22_3037156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_3037156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037156 prefixEnd_3037156 := by exact prefixLift 3037156
  have htrace : WordTrace (prefixWord ++ tailWord_3037156) baseStart_3037156 baseEnd_3037156 := by
    simpa [prefixWord, tailWord_3037156, baseEnd_3037156] using wordTrace_append hprefix tailTrace_3037156
  have hstable : (prefixWord ++ tailWord_3037156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037156).length < 2 ^ (prefixWord ++ tailWord_3037156).sum := by decide
  have hdescent : baseEnd_3037156 < baseStart_3037156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037171 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 5, 4]
def baseStart_3037171 : Nat := 118140960795 + 3037171 * 2 ^ 59
def prefixEnd_3037171 : Nat := 4983230072969 + 3 ^ 40 * 3037171 * 2
def baseEnd_3037171 : Nat := 1039685701931094525463207

theorem tailTrace_3037171 : CollatzResearch.WordTrace tailWord_3037171 prefixEnd_3037171 1039685701931094525463207 := by
  unfold tailWord_3037171
  simp only [CollatzResearch.WordTrace]
  refine ⟨110774726879855649355495367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73849817919903766236996911 110774726879855649355495367)
  ·
    refine ⟨166162090319783474033243051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110774726879855649355495367 166162090319783474033243051)
    ·
      refine ⟨249243135479675211049864577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166162090319783474033243051 249243135479675211049864577)
      ·
        refine ⟨186932351609756408287398433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249243135479675211049864577 186932351609756408287398433)
        ·
          refine ⟨140199263707317306215548825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186932351609756408287398433 140199263707317306215548825)
          ·
            refine ⟨105149447780487979661661619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140199263707317306215548825 105149447780487979661661619)
            ·
              refine ⟨157724171670731969492492429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105149447780487979661661619 157724171670731969492492429)
              ·
                refine ⟨59146564376524488559684661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157724171670731969492492429 59146564376524488559684661)
                ·
                  refine ⟨5544990410299170802470437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59146564376524488559684661 5544990410299170802470437)
                  ·
                    refine ⟨1039685701931094525463207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5544990410299170802470437 1039685701931094525463207)
                    ·
                      rfl

theorem cell22_3037171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 4].length) (baseStart_3037171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037171 prefixEnd_3037171 := by exact prefixLift 3037171
  have htrace : WordTrace (prefixWord ++ tailWord_3037171) baseStart_3037171 baseEnd_3037171 := by
    simpa [prefixWord, tailWord_3037171, baseEnd_3037171] using wordTrace_append hprefix tailTrace_3037171
  have hstable : (prefixWord ++ tailWord_3037171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037171).length < 2 ^ (prefixWord ++ tailWord_3037171).sum := by decide
  have hdescent : baseEnd_3037171 < baseStart_3037171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037263 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 5, 3]
def baseStart_3037263 : Nat := 118140960795 + 3037263 * 2 ^ 59
def prefixEnd_3037263 : Nat := 4983230072969 + 3 ^ 40 * 3037263 * 2
def baseEnd_3037263 : Nat := 1039717195411236952162925

theorem tailTrace_3037263 : CollatzResearch.WordTrace tailWord_3037263 prefixEnd_3037263 1039717195411236952162925 := by
  unfold tailWord_3037263
  simp only [CollatzResearch.WordTrace]
  refine ⟨110778082395522349067844443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73852054930348232711896295 110778082395522349067844443)
  ·
    refine ⟨166167123593283523601766665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110778082395522349067844443 166167123593283523601766665)
    ·
      refine ⟨124625342694962642701324999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166167123593283523601766665 124625342694962642701324999)
      ·
        refine ⟨186938014042443964051987499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124625342694962642701324999 186938014042443964051987499)
        ·
          refine ⟨280407021063665946077981249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186938014042443964051987499 280407021063665946077981249)
          ·
            refine ⟨210305265797749459558485937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280407021063665946077981249 210305265797749459558485937)
            ·
              refine ⟨157728949348312094668864453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210305265797749459558485937 157728949348312094668864453)
              ·
                refine ⟨29574178002808517750412085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157728949348312094668864453 29574178002808517750412085)
                ·
                  refine ⟨2772579187763298539101133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29574178002808517750412085 2772579187763298539101133)
                  ·
                    refine ⟨1039717195411236952162925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2772579187763298539101133 1039717195411236952162925)
                    ·
                      rfl

theorem cell22_3037263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 3].length) (baseStart_3037263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037263 prefixEnd_3037263 := by exact prefixLift 3037263
  have htrace : WordTrace (prefixWord ++ tailWord_3037263) baseStart_3037263 baseEnd_3037263 := by
    simpa [prefixWord, tailWord_3037263, baseEnd_3037263] using wordTrace_append hprefix tailTrace_3037263
  have hstable : (prefixWord ++ tailWord_3037263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037263).length < 2 ^ (prefixWord ++ tailWord_3037263).sum := by decide
  have hdescent : baseEnd_3037263 < baseStart_3037263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037282 : List Nat := [3, 3, 2, 2, 2, 2, 1, 7]
def baseStart_3037282 : Nat := 118140960795 + 3037282 * 2 ^ 59
def prefixEnd_3037282 : Nat := 4983230072969 + 3 ^ 40 * 3037282 * 2
def baseEnd_3037282 : Nat := 115524855499947470659763

theorem tailTrace_3037282 : CollatzResearch.WordTrace tailWord_3037282 prefixEnd_3037282 115524855499947470659763 := by
  unfold tailWord_3037282
  simp only [CollatzResearch.WordTrace]
  refine ⟨27694693845613378828196525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73852516921635676875190733 27694693845613378828196525)
  ·
    refine ⟨10385510192105017060573697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27694693845613378828196525 10385510192105017060573697)
    ·
      refine ⟨7789132644078762795430273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10385510192105017060573697 7789132644078762795430273)
      ·
        refine ⟨5841849483059072096572705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7789132644078762795430273 5841849483059072096572705)
        ·
          refine ⟨4381387112294304072429529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5841849483059072096572705 4381387112294304072429529)
          ·
            refine ⟨3286040334220728054322147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4381387112294304072429529 3286040334220728054322147)
            ·
              refine ⟨4929060501331092081483221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3286040334220728054322147 4929060501331092081483221)
              ·
                refine ⟨115524855499947470659763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4929060501331092081483221 115524855499947470659763)
                ·
                  rfl

theorem cell22_3037282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 7].length) (baseStart_3037282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037282 prefixEnd_3037282 := by exact prefixLift 3037282
  have htrace : WordTrace (prefixWord ++ tailWord_3037282) baseStart_3037282 baseEnd_3037282 := by
    simpa [prefixWord, tailWord_3037282, baseEnd_3037282] using wordTrace_append hprefix tailTrace_3037282
  have hstable : (prefixWord ++ tailWord_3037282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037282).length < 2 ^ (prefixWord ++ tailWord_3037282).sum := by decide
  have hdescent : baseEnd_3037282 < baseStart_3037282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037357 : List Nat := [1, 5, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_3037357 : Nat := 118140960795 + 3037357 * 2 ^ 59
def prefixEnd_3037357 : Nat := 4983230072969 + 3 ^ 40 * 3037357 * 2
def baseEnd_3037357 : Nat := 1039749373532252040312637

theorem tailTrace_3037357 : CollatzResearch.WordTrace tailWord_3037357 prefixEnd_3037357 1039749373532252040312637 := by
  unfold tailWord_3037357
  simp only [CollatzResearch.WordTrace]
  refine ⟨110781510857181803121766325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73854340571454535414510883 110781510857181803121766325)
  ·
    refine ⟨10385766642860794042665593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110781510857181803121766325 10385766642860794042665593)
    ·
      refine ⟨7789324982145595531999195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10385766642860794042665593 7789324982145595531999195)
      ·
        refine ⟨11683987473218393297998793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7789324982145595531999195 11683987473218393297998793)
        ·
          refine ⟨8762990604913794973499095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11683987473218393297998793 8762990604913794973499095)
          ·
            refine ⟨13144485907370692460248643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8762990604913794973499095 13144485907370692460248643)
            ·
              refine ⟨19716728861056038690372965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13144485907370692460248643 19716728861056038690372965)
              ·
                refine ⟨3696886661448007254444931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19716728861056038690372965 3696886661448007254444931)
                ·
                  refine ⟨5545329992172010881667397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3696886661448007254444931 5545329992172010881667397)
                  ·
                    refine ⟨1039749373532252040312637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5545329992172010881667397 1039749373532252040312637)
                    ·
                      rfl

theorem cell22_3037357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_3037357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037357 prefixEnd_3037357 := by exact prefixLift 3037357
  have htrace : WordTrace (prefixWord ++ tailWord_3037357) baseStart_3037357 baseEnd_3037357 := by
    simpa [prefixWord, tailWord_3037357, baseEnd_3037357] using wordTrace_append hprefix tailTrace_3037357
  have hstable : (prefixWord ++ tailWord_3037357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037357).length < 2 ^ (prefixWord ++ tailWord_3037357).sum := by decide
  have hdescent : baseEnd_3037357 < baseStart_3037357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037368 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 1, 6]
def baseStart_3037368 : Nat := 118140960795 + 3037368 * 2 ^ 59
def prefixEnd_3037368 : Nat := 4983230072969 + 3 ^ 40 * 3037368 * 2
def baseEnd_3037368 : Nat := 1039753139057051678287603

theorem tailTrace_3037368 : CollatzResearch.WordTrace tailWord_3037368 prefixEnd_3037368 1039753139057051678287603 := by
  unfold tailWord_3037368
  simp only [CollatzResearch.WordTrace]
  refine ⟨55390956030070976000208379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73854608040094634666944505 55390956030070976000208379)
  ·
    refine ⟨83086434045106464000312569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55390956030070976000208379 83086434045106464000312569)
    ·
      refine ⟨62314825533829848000234427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83086434045106464000312569 62314825533829848000234427)
      ·
        refine ⟨93472238300744772000351641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62314825533829848000234427 93472238300744772000351641)
        ·
          refine ⟨70104178725558579000263731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93472238300744772000351641 70104178725558579000263731)
          ·
            refine ⟨105156268088337868500395597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70104178725558579000263731 105156268088337868500395597)
            ·
              refine ⟨39433600533126700687648349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105156268088337868500395597 39433600533126700687648349)
              ·
                refine ⟨14787600199922512757868131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39433600533126700687648349 14787600199922512757868131)
                ·
                  refine ⟨22181400299883769136802197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14787600199922512757868131 22181400299883769136802197)
                  ·
                    refine ⟨1039753139057051678287603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22181400299883769136802197 1039753139057051678287603)
                    ·
                      rfl

theorem cell22_3037368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_3037368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037368 prefixEnd_3037368 := by exact prefixLift 3037368
  have htrace : WordTrace (prefixWord ++ tailWord_3037368) baseStart_3037368 baseEnd_3037368 := by
    simpa [prefixWord, tailWord_3037368, baseEnd_3037368] using wordTrace_append hprefix tailTrace_3037368
  have hstable : (prefixWord ++ tailWord_3037368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037368).length < 2 ^ (prefixWord ++ tailWord_3037368).sum := by decide
  have hdescent : baseEnd_3037368 < baseStart_3037368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037370 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 4, 3]
def baseStart_3037370 : Nat := 118140960795 + 3037370 * 2 ^ 59
def prefixEnd_3037370 : Nat := 4983230072969 + 3 ^ 40 * 3037370 * 2
def baseEnd_3037370 : Nat := 1039753823697924339737597

theorem tailTrace_3037370 : CollatzResearch.WordTrace tailWord_3037370 prefixEnd_3037370 1039753823697924339737597 := by
  unfold tailWord_3037370
  simp only [CollatzResearch.WordTrace]
  refine ⟨27695496251533676585497391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73854656670756470894659709 27695496251533676585497391)
  ·
    refine ⟨41543244377300514878246087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27695496251533676585497391 41543244377300514878246087)
    ·
      refine ⟨62314866565950772317369131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41543244377300514878246087 62314866565950772317369131)
      ·
        refine ⟨93472299848926158476053697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62314866565950772317369131 93472299848926158476053697)
        ·
          refine ⟨70104224886694618857040273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93472299848926158476053697 70104224886694618857040273)
          ·
            refine ⟨52578168665020964142780205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70104224886694618857040273 52578168665020964142780205)
            ·
              refine ⟨19716813249382861553542577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52578168665020964142780205 19716813249382861553542577)
              ·
                refine ⟨14787609937037146165156933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19716813249382861553542577 14787609937037146165156933)
                ·
                  refine ⟨2772676863194464905966925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14787609937037146165156933 2772676863194464905966925)
                  ·
                    refine ⟨1039753823697924339737597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2772676863194464905966925 1039753823697924339737597)
                    ·
                      rfl

theorem cell22_3037370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_3037370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037370 prefixEnd_3037370 := by exact prefixLift 3037370
  have htrace : WordTrace (prefixWord ++ tailWord_3037370) baseStart_3037370 baseEnd_3037370 := by
    simpa [prefixWord, tailWord_3037370, baseEnd_3037370] using wordTrace_append hprefix tailTrace_3037370
  have hstable : (prefixWord ++ tailWord_3037370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037370).length < 2 ^ (prefixWord ++ tailWord_3037370).sum := by decide
  have hdescent : baseEnd_3037370 < baseStart_3037370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037400 : List Nat := [2, 1, 2, 2, 4, 2, 2, 7]
def baseStart_3037400 : Nat := 118140960795 + 3037400 * 2 ^ 59
def prefixEnd_3037400 : Nat := 4983230072969 + 3 ^ 40 * 3037400 * 2
def baseEnd_3037400 : Nat := 115529343701223806831945

theorem tailTrace_3037400 : CollatzResearch.WordTrace tailWord_3037400 prefixEnd_3037400 115529343701223806831945 := by
  unfold tailWord_3037400
  simp only [CollatzResearch.WordTrace]
  refine ⟨55391539598013010732790827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73855386130684014310387769 55391539598013010732790827)
  ·
    refine ⟨83087309397019516099186241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55391539598013010732790827 83087309397019516099186241)
    ·
      refine ⟨62315482047764637074389681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83087309397019516099186241 62315482047764637074389681)
      ·
        refine ⟨46736611535823477805792261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62315482047764637074389681 46736611535823477805792261)
        ·
          refine ⟨8763114662966902088586049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46736611535823477805792261 8763114662966902088586049)
          ·
            refine ⟨6572335997225176566439537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8763114662966902088586049 6572335997225176566439537)
            ·
              refine ⟨4929251997918882424829653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6572335997225176566439537 4929251997918882424829653)
              ·
                refine ⟨115529343701223806831945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4929251997918882424829653 115529343701223806831945)
                ·
                  rfl

theorem cell22_3037400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 7].length) (baseStart_3037400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037400 prefixEnd_3037400 := by exact prefixLift 3037400
  have htrace : WordTrace (prefixWord ++ tailWord_3037400) baseStart_3037400 baseEnd_3037400 := by
    simpa [prefixWord, tailWord_3037400, baseEnd_3037400] using wordTrace_append hprefix tailTrace_3037400
  have hstable : (prefixWord ++ tailWord_3037400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037400).length < 2 ^ (prefixWord ++ tailWord_3037400).sum := by decide
  have hdescent : baseEnd_3037400 < baseStart_3037400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037449 : List Nat := [1, 2, 1, 1, 3, 5, 1, 4, 1, 3]
def baseStart_3037449 : Nat := 118140960795 + 3037449 * 2 ^ 59
def prefixEnd_3037449 : Nat := 4983230072969 + 3 ^ 40 * 3037449 * 2
def baseEnd_3037449 : Nat := 1039780867012394467012355

theorem tailTrace_3037449 : CollatzResearch.WordTrace tailWord_3037449 prefixEnd_3037449 1039780867012394467012355 := by
  unfold tailWord_3037449
  simp only [CollatzResearch.WordTrace]
  refine ⟨110784866372848502834115401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73856577581899001889410267 110784866372848502834115401)
  ·
    refine ⟨83088649779636377125586551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110784866372848502834115401 83088649779636377125586551)
    ·
      refine ⟨124632974669454565688379827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83088649779636377125586551 124632974669454565688379827)
      ·
        refine ⟨186949462004181848532569741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124632974669454565688379827 186949462004181848532569741)
        ·
          refine ⟨70106048251568193199713653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186949462004181848532569741 70106048251568193199713653)
          ·
            refine ⟨6572442023584518112473155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70106048251568193199713653 6572442023584518112473155)
            ·
              refine ⟨9858663035376777168709733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6572442023584518112473155 9858663035376777168709733)
              ·
                refine ⟨1848499319133145719133075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9858663035376777168709733 1848499319133145719133075)
                ·
                  refine ⟨2772748978699718578699613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1848499319133145719133075 2772748978699718578699613)
                  ·
                    refine ⟨1039780867012394467012355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2772748978699718578699613 1039780867012394467012355)
                    ·
                      rfl

theorem cell22_3037449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 1, 3].length) (baseStart_3037449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037449 prefixEnd_3037449 := by exact prefixLift 3037449
  have htrace : WordTrace (prefixWord ++ tailWord_3037449) baseStart_3037449 baseEnd_3037449 := by
    simpa [prefixWord, tailWord_3037449, baseEnd_3037449] using wordTrace_append hprefix tailTrace_3037449
  have hstable : (prefixWord ++ tailWord_3037449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037449).length < 2 ^ (prefixWord ++ tailWord_3037449).sum := by decide
  have hdescent : baseEnd_3037449 < baseStart_3037449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037475 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 3, 4]
def baseStart_3037475 : Nat := 118140960795 + 3037475 * 2 ^ 59
def prefixEnd_3037475 : Nat := 4983230072969 + 3 ^ 40 * 3037475 * 2
def baseEnd_3037475 : Nat := 1039789767343739065862275

theorem tailTrace_3037475 : CollatzResearch.WordTrace tailWord_3037475 prefixEnd_3037475 1039789767343739065862275 := by
  unfold tailWord_3037475
  simp only [CollatzResearch.WordTrace]
  refine ⟨110785814670754309274561879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73857209780502872849707919 110785814670754309274561879)
  ·
    refine ⟨166178722006131463911842819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110785814670754309274561879 166178722006131463911842819)
    ·
      refine ⟨249268083009197195867764229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166178722006131463911842819 249268083009197195867764229)
      ·
        refine ⟨46737765564224474225205793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249268083009197195867764229 46737765564224474225205793)
        ·
          refine ⟨35053324173168355668904345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46737765564224474225205793 35053324173168355668904345)
          ·
            refine ⟨26289993129876266751678259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35053324173168355668904345 26289993129876266751678259)
            ·
              refine ⟨39434989694814400127517389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26289993129876266751678259 39434989694814400127517389)
              ·
                refine ⟨14788121135555400047819021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39434989694814400127517389 14788121135555400047819021)
                ·
                  refine ⟨5545545425833275017932133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14788121135555400047819021 5545545425833275017932133)
                  ·
                    refine ⟨1039789767343739065862275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5545545425833275017932133 1039789767343739065862275)
                    ·
                      rfl

theorem cell22_3037475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 4].length) (baseStart_3037475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037475 prefixEnd_3037475 := by exact prefixLift 3037475
  have htrace : WordTrace (prefixWord ++ tailWord_3037475) baseStart_3037475 baseEnd_3037475 := by
    simpa [prefixWord, tailWord_3037475, baseEnd_3037475] using wordTrace_append hprefix tailTrace_3037475
  have hstable : (prefixWord ++ tailWord_3037475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037475).length < 2 ^ (prefixWord ++ tailWord_3037475).sum := by decide
  have hdescent : baseEnd_3037475 < baseStart_3037475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037507 : List Nat := [1, 1, 1, 3, 1, 3, 4, 4, 4]
def baseStart_3037507 : Nat := 118140960795 + 3037507 * 2 ^ 59
def prefixEnd_3037507 : Nat := 4983230072969 + 3 ^ 40 * 3037507 * 2
def baseEnd_3037507 : Nat := 346600240532567216354059

theorem tailTrace_3037507 : CollatzResearch.WordTrace tailWord_3037507 prefixEnd_3037507 346600240532567216354059 := by
  unfold tailWord_3037507
  simp only [CollatzResearch.WordTrace]
  refine ⟨110786981806638378739726775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73857987871092252493151183 110786981806638378739726775)
  ·
    refine ⟨166180472709957568109590163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110786981806638378739726775 166180472709957568109590163)
    ·
      refine ⟨249270709064936352164385245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166180472709957568109590163 249270709064936352164385245)
      ·
        refine ⟨93476515899351132061644467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249270709064936352164385245 93476515899351132061644467)
        ·
          refine ⟨140214773849026698092466701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93476515899351132061644467 140214773849026698092466701)
          ·
            refine ⟨52580540193385011784675013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140214773849026698092466701 52580540193385011784675013)
            ·
              refine ⟨9858851286259689709626565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52580540193385011784675013 9858851286259689709626565)
              ·
                refine ⟨1848534616173691820554981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9858851286259689709626565 1848534616173691820554981)
                ·
                  refine ⟨346600240532567216354059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1848534616173691820554981 346600240532567216354059)
                  ·
                    rfl

theorem cell22_3037507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 4].length) (baseStart_3037507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037507 prefixEnd_3037507 := by exact prefixLift 3037507
  have htrace : WordTrace (prefixWord ++ tailWord_3037507) baseStart_3037507 baseEnd_3037507 := by
    simpa [prefixWord, tailWord_3037507, baseEnd_3037507] using wordTrace_append hprefix tailTrace_3037507
  have hstable : (prefixWord ++ tailWord_3037507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037507).length < 2 ^ (prefixWord ++ tailWord_3037507).sum := by decide
  have hdescent : baseEnd_3037507 < baseStart_3037507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037520 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 1, 6]
def baseStart_3037520 : Nat := 118140960795 + 3037520 * 2 ^ 59
def prefixEnd_3037520 : Nat := 4983230072969 + 3 ^ 40 * 3037520 * 2
def baseEnd_3037520 : Nat := 1039805171763373948487137

theorem tailTrace_3037520 : CollatzResearch.WordTrace tailWord_3037520 prefixEnd_3037520 1039805171763373948487137 := by
  unfold tailWord_3037520
  simp only [CollatzResearch.WordTrace]
  refine ⟨55393727977795640979975007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73858303970394187973300009 55393727977795640979975007)
  ·
    refine ⟨83090591966693461469962511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55393727977795640979975007 83090591966693461469962511)
    ·
      refine ⟨124635887950040192204943767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83090591966693461469962511 124635887950040192204943767)
      ·
        refine ⟨186953831925060288307415651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124635887950040192204943767 186953831925060288307415651)
        ·
          refine ⟨280430747887590432461123477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186953831925060288307415651 280430747887590432461123477)
          ·
            refine ⟨13145191307230801521615163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 280430747887590432461123477 13145191307230801521615163)
            ·
              refine ⟨19717786960846202282422745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13145191307230801521615163 19717786960846202282422745)
              ·
                refine ⟨14788340220634651711817059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19717786960846202282422745 14788340220634651711817059)
                ·
                  refine ⟨22182510330951977567725589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14788340220634651711817059 22182510330951977567725589)
                  ·
                    refine ⟨1039805171763373948487137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22182510330951977567725589 1039805171763373948487137)
                    ·
                      rfl

theorem cell22_3037520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_3037520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037520 prefixEnd_3037520 := by exact prefixLift 3037520
  have htrace : WordTrace (prefixWord ++ tailWord_3037520) baseStart_3037520 baseEnd_3037520 := by
    simpa [prefixWord, tailWord_3037520, baseEnd_3037520] using wordTrace_append hprefix tailTrace_3037520
  have hstable : (prefixWord ++ tailWord_3037520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037520).length < 2 ^ (prefixWord ++ tailWord_3037520).sum := by decide
  have hdescent : baseEnd_3037520 < baseStart_3037520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037522 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_3037522 : Nat := 118140960795 + 3037522 * 2 ^ 59
def prefixEnd_3037522 : Nat := 4983230072969 + 3 ^ 40 * 3037522 * 2
def baseEnd_3037522 : Nat := 1039805856404246609937131

theorem tailTrace_3037522 : CollatzResearch.WordTrace tailWord_3037522 prefixEnd_3037522 1039805856404246609937131 := by
  unfold tailWord_3037522
  simp only [CollatzResearch.WordTrace]
  refine ⟨27696882225396009075380705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73858352601056024201015213 27696882225396009075380705)
  ·
    refine ⟨20772661669047006806535529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27696882225396009075380705 20772661669047006806535529)
    ·
      refine ⟨15579496251785255104901647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20772661669047006806535529 15579496251785255104901647)
      ·
        refine ⟨23369244377677882657352471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15579496251785255104901647 23369244377677882657352471)
        ·
          refine ⟨35053866566516823986028707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23369244377677882657352471 35053866566516823986028707)
          ·
            refine ⟨52580799849775235979043061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35053866566516823986028707 52580799849775235979043061)
            ·
              refine ⟨4929449985916428373035287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52580799849775235979043061 4929449985916428373035287)
              ·
                refine ⟨7394174978874642559552931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4929449985916428373035287 7394174978874642559552931)
                ·
                  refine ⟨11091262468311963839329397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7394174978874642559552931 11091262468311963839329397)
                  ·
                    refine ⟨1039805856404246609937131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11091262468311963839329397 1039805856404246609937131)
                    ·
                      rfl

theorem cell22_3037522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_3037522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037522 prefixEnd_3037522 := by exact prefixLift 3037522
  have htrace : WordTrace (prefixWord ++ tailWord_3037522) baseStart_3037522 baseEnd_3037522 := by
    simpa [prefixWord, tailWord_3037522, baseEnd_3037522] using wordTrace_append hprefix tailTrace_3037522
  have hstable : (prefixWord ++ tailWord_3037522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037522).length < 2 ^ (prefixWord ++ tailWord_3037522).sum := by decide
  have hdescent : baseEnd_3037522 < baseStart_3037522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037534 : List Nat := [4, 4, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3037534 : Nat := 118140960795 + 3037534 * 2 ^ 59
def prefixEnd_3037534 : Nat := 4983230072969 + 3 ^ 40 * 3037534 * 2
def baseEnd_3037534 : Nat := 1039809964249482578637095

theorem tailTrace_3037534 : CollatzResearch.WordTrace tailWord_3037534 prefixEnd_3037534 1039809964249482578637095 := by
  unfold tailWord_3037534
  simp only [CollatzResearch.WordTrace]
  refine ⟨13848495822192570293869957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73858644385027041567306437 13848495822192570293869957)
  ·
    refine ⟨2596592966661106930100617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13848495822192570293869957 2596592966661106930100617)
    ·
      refine ⟨1947444724995830197575463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2596592966661106930100617 1947444724995830197575463)
      ·
        refine ⟨2921167087493745296363195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1947444724995830197575463 2921167087493745296363195)
        ·
          refine ⟨4381750631240617944544793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2921167087493745296363195 4381750631240617944544793)
          ·
            refine ⟨3286312973430463458408595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4381750631240617944544793 3286312973430463458408595)
            ·
              refine ⟨4929469460145695187612893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3286312973430463458408595 4929469460145695187612893)
              ·
                refine ⟨1848551047554635695354835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4929469460145695187612893 1848551047554635695354835)
                ·
                  refine ⟨2772826571331953543032253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1848551047554635695354835 2772826571331953543032253)
                  ·
                    refine ⟨1039809964249482578637095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2772826571331953543032253 1039809964249482578637095)
                    ·
                      rfl

theorem cell22_3037534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3037534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037534 prefixEnd_3037534 := by exact prefixLift 3037534
  have htrace : WordTrace (prefixWord ++ tailWord_3037534) baseStart_3037534 baseEnd_3037534 := by
    simpa [prefixWord, tailWord_3037534, baseEnd_3037534] using wordTrace_append hprefix tailTrace_3037534
  have hstable : (prefixWord ++ tailWord_3037534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037534).length < 2 ^ (prefixWord ++ tailWord_3037534).sum := by decide
  have hdescent : baseEnd_3037534 < baseStart_3037534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037558 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_3037558 : Nat := 118140960795 + 3037558 * 2 ^ 59
def prefixEnd_3037558 : Nat := 4983230072969 + 3 ^ 40 * 3037558 * 2
def baseEnd_3037558 : Nat := 346606059979984838679007

theorem tailTrace_3037558 : CollatzResearch.WordTrace tailWord_3037558 prefixEnd_3037558 346606059979984838679007 := by
  unfold tailWord_3037558
  simp only [CollatzResearch.WordTrace]
  refine ⟨6924302620590850903114583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73859227952969076299888885 6924302620590850903114583)
  ·
    refine ⟨10386453930886276354671875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6924302620590850903114583 10386453930886276354671875)
    ·
      refine ⟨15579680896329414532007813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10386453930886276354671875 15579680896329414532007813)
      ·
        refine ⟨2921190168061765224751465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15579680896329414532007813 2921190168061765224751465)
        ·
          refine ⟨2190892626046323918563599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2921190168061765224751465 2190892626046323918563599)
          ·
            refine ⟨3286338939069485877845399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2190892626046323918563599 3286338939069485877845399)
            ·
              refine ⟨4929508408604228816768099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3286338939069485877845399 4929508408604228816768099)
              ·
                refine ⟨7394262612906343225152149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4929508408604228816768099 7394262612906343225152149)
                ·
                  refine ⟨346606059979984838679007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7394262612906343225152149 346606059979984838679007)
                  ·
                    rfl

theorem cell22_3037558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_3037558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037558 prefixEnd_3037558 := by exact prefixLift 3037558
  have htrace : WordTrace (prefixWord ++ tailWord_3037558) baseStart_3037558 baseEnd_3037558 := by
    simpa [prefixWord, tailWord_3037558, baseEnd_3037558] using wordTrace_append hprefix tailTrace_3037558
  have hstable : (prefixWord ++ tailWord_3037558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037558).length < 2 ^ (prefixWord ++ tailWord_3037558).sum := by decide
  have hdescent : baseEnd_3037558 < baseStart_3037558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037642 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 6]
def baseStart_3037642 : Nat := 118140960795 + 3037642 * 2 ^ 59
def prefixEnd_3037642 : Nat := 4983230072969 + 3 ^ 40 * 3037642 * 2
def baseEnd_3037642 : Nat := 346615644952202098978921

theorem tailTrace_3037642 : CollatzResearch.WordTrace tailWord_3037642 prefixEnd_3037642 346615644952202098978921 := by
  unfold tailWord_3037642
  simp only [CollatzResearch.WordTrace]
  refine ⟨27697976415287324198972795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73861270440766197863927453 27697976415287324198972795)
  ·
    refine ⟨41546964622930986298459193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27697976415287324198972795 41546964622930986298459193)
    ·
      refine ⟨31160223467198239723844395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41546964622930986298459193 31160223467198239723844395)
      ·
        refine ⟨46740335200797359585766593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31160223467198239723844395 46740335200797359585766593)
        ·
          refine ⟨35055251400598019689324945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46740335200797359585766593 35055251400598019689324945)
          ·
            refine ⟨26291438550448514766993709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35055251400598019689324945 26291438550448514766993709)
            ·
              refine ⟨9859289456418193037622641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26291438550448514766993709 9859289456418193037622641)
              ·
                refine ⟨7394467092313644778216981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9859289456418193037622641 7394467092313644778216981)
                ·
                  refine ⟨346615644952202098978921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7394467092313644778216981 346615644952202098978921)
                  ·
                    rfl

theorem cell22_3037642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_3037642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037642 prefixEnd_3037642 := by exact prefixLift 3037642
  have htrace : WordTrace (prefixWord ++ tailWord_3037642) baseStart_3037642 baseEnd_3037642 := by
    simpa [prefixWord, tailWord_3037642, baseEnd_3037642] using wordTrace_append hprefix tailTrace_3037642
  have hstable : (prefixWord ++ tailWord_3037642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037642).length < 2 ^ (prefixWord ++ tailWord_3037642).sum := by decide
  have hdescent : baseEnd_3037642 < baseStart_3037642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037657 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 1, 5]
def baseStart_3037657 : Nat := 118140960795 + 3037657 * 2 ^ 59
def prefixEnd_3037657 : Nat := 4983230072969 + 3 ^ 40 * 3037657 * 2
def baseEnd_3037657 : Nat := 1039852069663151257811717

theorem tailTrace_3037657 : CollatzResearch.WordTrace tailWord_3037657 prefixEnd_3037657 1039852069663151257811717 := by
  unfold tailWord_3037657
  simp only [CollatzResearch.WordTrace]
  refine ⟨110792452756094954357687225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73861635170729969571791483 110792452756094954357687225)
  ·
    refine ⟨83094339567071215768265419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110792452756094954357687225 83094339567071215768265419)
    ·
      refine ⟨124641509350606823652398129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83094339567071215768265419 124641509350606823652398129)
      ·
        refine ⟨93481132012955117739298597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124641509350606823652398129 93481132012955117739298597)
        ·
          refine ⟨17527712252429084576118487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93481132012955117739298597 17527712252429084576118487)
          ·
            refine ⟨26291568378643626864177731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17527712252429084576118487 26291568378643626864177731)
            ·
              refine ⟨39437352567965440296266597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26291568378643626864177731 39437352567965440296266597)
              ·
                refine ⟨7394503606493520055549987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39437352567965440296266597 7394503606493520055549987)
                ·
                  refine ⟨11091755409740280083324981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7394503606493520055549987 11091755409740280083324981)
                  ·
                    refine ⟨1039852069663151257811717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11091755409740280083324981 1039852069663151257811717)
                    ·
                      rfl

theorem cell22_3037657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_3037657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037657 prefixEnd_3037657 := by exact prefixLift 3037657
  have htrace : WordTrace (prefixWord ++ tailWord_3037657) baseStart_3037657 baseEnd_3037657 := by
    simpa [prefixWord, tailWord_3037657, baseEnd_3037657] using wordTrace_append hprefix tailTrace_3037657
  have hstable : (prefixWord ++ tailWord_3037657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037657).length < 2 ^ (prefixWord ++ tailWord_3037657).sum := by decide
  have hdescent : baseEnd_3037657 < baseStart_3037657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037742 : List Nat := [4, 1, 3, 1, 4, 1, 2, 1, 2, 3]
def baseStart_3037742 : Nat := 118140960795 + 3037742 * 2 ^ 59
def prefixEnd_3037742 : Nat := 4983230072969 + 3 ^ 40 * 3037742 * 2
def baseEnd_3037742 : Nat := 1039881166900239369436457

theorem tailTrace_3037742 : CollatzResearch.WordTrace tailWord_3037742 prefixEnd_3037742 1039881166900239369436457 := by
  unfold tailWord_3037742
  simp only [CollatzResearch.WordTrace]
  refine ⟨13849444120098376734316435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73863701973858009249687653 13849444120098376734316435)
  ·
    refine ⟨20774166180147565101474653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13849444120098376734316435 20774166180147565101474653)
    ·
      refine ⟨7790312317555336913052995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20774166180147565101474653 7790312317555336913052995)
      ·
        refine ⟨11685468476333005369579493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7790312317555336913052995 11685468476333005369579493)
        ·
          refine ⟨2191025339312438506796155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11685468476333005369579493 2191025339312438506796155)
          ·
            refine ⟨3286538008968657760194233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191025339312438506796155 3286538008968657760194233)
            ·
              refine ⟨2464903506726493320145675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3286538008968657760194233 2464903506726493320145675)
              ·
                refine ⟨3697355260089739980218513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2464903506726493320145675 3697355260089739980218513)
                ·
                  refine ⟨2773016445067304985163885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3697355260089739980218513 2773016445067304985163885)
                  ·
                    refine ⟨1039881166900239369436457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2773016445067304985163885 1039881166900239369436457)
                    ·
                      rfl

theorem cell22_3037742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_3037742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037742 prefixEnd_3037742 := by exact prefixLift 3037742
  have htrace : WordTrace (prefixWord ++ tailWord_3037742) baseStart_3037742 baseEnd_3037742 := by
    simpa [prefixWord, tailWord_3037742, baseEnd_3037742] using wordTrace_append hprefix tailTrace_3037742
  have hstable : (prefixWord ++ tailWord_3037742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037742).length < 2 ^ (prefixWord ++ tailWord_3037742).sum := by decide
  have hdescent : baseEnd_3037742 < baseStart_3037742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037747 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 1, 7]
def baseStart_3037747 : Nat := 118140960795 + 3037747 * 2 ^ 59
def prefixEnd_3037747 : Nat := 4983230072969 + 3 ^ 40 * 3037747 * 2
def baseEnd_3037747 : Nat := 1039882878502421023061441

theorem tailTrace_3037747 : CollatzResearch.WordTrace tailWord_3037747 prefixEnd_3037747 1039882878502421023061441 := by
  unfold tailWord_3037747
  simp only [CollatzResearch.WordTrace]
  refine ⟨110795735325768899728463495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73863823550512599818975663 110795735325768899728463495)
  ·
    refine ⟨166193602988653349592695243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110795735325768899728463495 166193602988653349592695243)
    ·
      refine ⟨249290404482980024389042865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166193602988653349592695243 249290404482980024389042865)
      ·
        refine ⟨186967803362235018291782149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249290404482980024389042865 186967803362235018291782149)
        ·
          refine ⟨35056463130419065929709153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186967803362235018291782149 35056463130419065929709153)
          ·
            refine ⟨26292347347814299447281865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35056463130419065929709153 26292347347814299447281865)
            ·
              refine ⟨19719260510860724585461399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26292347347814299447281865 19719260510860724585461399)
              ·
                refine ⟨29578890766291086878192099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19719260510860724585461399 29578890766291086878192099)
                ·
                  refine ⟨44368336149436630317288149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29578890766291086878192099 44368336149436630317288149)
                  ·
                    refine ⟨1039882878502421023061441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44368336149436630317288149 1039882878502421023061441)
                    ·
                      rfl

theorem cell22_3037747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 7].length) (baseStart_3037747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037747 prefixEnd_3037747 := by exact prefixLift 3037747
  have htrace : WordTrace (prefixWord ++ tailWord_3037747) baseStart_3037747 baseEnd_3037747 := by
    simpa [prefixWord, tailWord_3037747, baseEnd_3037747] using wordTrace_append hprefix tailTrace_3037747
  have hstable : (prefixWord ++ tailWord_3037747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037747).length < 2 ^ (prefixWord ++ tailWord_3037747).sum := by decide
  have hdescent : baseEnd_3037747 < baseStart_3037747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037749 : List Nat := [1, 3, 3, 1, 1, 2, 3, 3, 5]
def baseStart_3037749 : Nat := 118140960795 + 3037749 * 2 ^ 59
def prefixEnd_3037749 : Nat := 4983230072969 + 3 ^ 40 * 3037749 * 2
def baseEnd_3037749 : Nat := 346627854381097894837145

theorem tailTrace_3037749 : CollatzResearch.WordTrace tailWord_3037749 prefixEnd_3037749 346627854381097894837145 := by
  unfold tailWord_3037749
  simp only [CollatzResearch.WordTrace]
  refine ⟨110795808271761654070036301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73863872181174436046690867 110795808271761654070036301)
  ·
    refine ⟨41548428101910620276263613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110795808271761654070036301 41548428101910620276263613)
    ·
      refine ⟨15580660538216482603598855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41548428101910620276263613 15580660538216482603598855)
      ·
        refine ⟨23370990807324723905398283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15580660538216482603598855 23370990807324723905398283)
        ·
          refine ⟨35056486210987085858097425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23370990807324723905398283 35056486210987085858097425)
          ·
            refine ⟨26292364658240314393573069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35056486210987085858097425 26292364658240314393573069)
            ·
              refine ⟨9859636746840117897589901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26292364658240314393573069 9859636746840117897589901)
              ·
                refine ⟨3697363780065044211596213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9859636746840117897589901 3697363780065044211596213)
                ·
                  refine ⟨346627854381097894837145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3697363780065044211596213 346627854381097894837145)
                  ·
                    rfl

theorem cell22_3037749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_3037749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037749 prefixEnd_3037749 := by exact prefixLift 3037749
  have htrace : WordTrace (prefixWord ++ tailWord_3037749) baseStart_3037749 baseEnd_3037749 := by
    simpa [prefixWord, tailWord_3037749, baseEnd_3037749] using wordTrace_append hprefix tailTrace_3037749
  have hstable : (prefixWord ++ tailWord_3037749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037749).length < 2 ^ (prefixWord ++ tailWord_3037749).sum := by decide
  have hdescent : baseEnd_3037749 < baseStart_3037749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037809 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 8, 3]
def baseStart_3037809 : Nat := 118140960795 + 3037809 * 2 ^ 59
def prefixEnd_3037809 : Nat := 4983230072969 + 3 ^ 40 * 3037809 * 2
def baseEnd_3037809 : Nat := 1039904102369473528011251

theorem tailTrace_3037809 : CollatzResearch.WordTrace tailWord_3037809 prefixEnd_3037809 1039904102369473528011251 := by
  unfold tailWord_3037809
  simp only [CollatzResearch.WordTrace]
  refine ⟨110797996651544284317220481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73865331101029522878146987 110797996651544284317220481)
  ·
    refine ⟨83098497488658213237915361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110797996651544284317220481 83098497488658213237915361)
    ·
      refine ⟨62323873116493659928436521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83098497488658213237915361 62323873116493659928436521)
      ·
        refine ⟨46742904837370244946327391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62323873116493659928436521 46742904837370244946327391)
        ·
          refine ⟨70114357256055367419491087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46742904837370244946327391 70114357256055367419491087)
          ·
            refine ⟨105171535884083051129236631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70114357256055367419491087 105171535884083051129236631)
            ·
              refine ⟨157757303826124576693854947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105171535884083051129236631 157757303826124576693854947)
              ·
                refine ⟨236635955739186865040782421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157757303826124576693854947 236635955739186865040782421)
                ·
                  refine ⟨2773077606318596074696669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 236635955739186865040782421 2773077606318596074696669)
                  ·
                    refine ⟨1039904102369473528011251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2773077606318596074696669 1039904102369473528011251)
                    ·
                      rfl

theorem cell22_3037809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_3037809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037809 prefixEnd_3037809 := by exact prefixLift 3037809
  have htrace : WordTrace (prefixWord ++ tailWord_3037809) baseStart_3037809 baseEnd_3037809 := by
    simpa [prefixWord, tailWord_3037809, baseEnd_3037809] using wordTrace_append hprefix tailTrace_3037809
  have hstable : (prefixWord ++ tailWord_3037809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037809).length < 2 ^ (prefixWord ++ tailWord_3037809).sum := by decide
  have hdescent : baseEnd_3037809 < baseStart_3037809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037824 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 1, 6]
def baseStart_3037824 : Nat := 118140960795 + 3037824 * 2 ^ 59
def prefixEnd_3037824 : Nat := 4983230072969 + 3 ^ 40 * 3037824 * 2
def baseEnd_3037824 : Nat := 1039909237176018488886205

theorem tailTrace_3037824 : CollatzResearch.WordTrace tailWord_3037824 prefixEnd_3037824 1039909237176018488886205 := by
  unfold tailWord_3037824
  simp only [CollatzResearch.WordTrace]
  refine ⟨55399271873244970939508263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73865695830993294586011017 55399271873244970939508263)
  ·
    refine ⟨83098907809867456409262395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55399271873244970939508263 83098907809867456409262395)
    ·
      refine ⟨124648361714801184613893593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83098907809867456409262395 124648361714801184613893593)
      ·
        refine ⟨93486271286100888460420195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124648361714801184613893593 93486271286100888460420195)
        ·
          refine ⟨140229406929151332690630293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93486271286100888460420195 140229406929151332690630293)
          ·
            refine ⟨6573253449803968719873295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140229406929151332690630293 6573253449803968719873295)
            ·
              refine ⟨9859880174705953079809943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6573253449803968719873295 9859880174705953079809943)
              ·
                refine ⟨14789820262058929619714915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9859880174705953079809943 14789820262058929619714915)
                ·
                  refine ⟨22184730393088394429572373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14789820262058929619714915 22184730393088394429572373)
                  ·
                    refine ⟨1039909237176018488886205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22184730393088394429572373 1039909237176018488886205)
                    ·
                      rfl

theorem cell22_3037824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_3037824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037824 prefixEnd_3037824 := by exact prefixLift 3037824
  have htrace : WordTrace (prefixWord ++ tailWord_3037824) baseStart_3037824 baseEnd_3037824 := by
    simpa [prefixWord, tailWord_3037824, baseEnd_3037824] using wordTrace_append hprefix tailTrace_3037824
  have hstable : (prefixWord ++ tailWord_3037824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037824).length < 2 ^ (prefixWord ++ tailWord_3037824).sum := by decide
  have hdescent : baseEnd_3037824 < baseStart_3037824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037828 : List Nat := [2, 3, 2, 1, 3, 2, 2, 3, 4]
def baseStart_3037828 : Nat := 118140960795 + 3037828 * 2 ^ 59
def prefixEnd_3037828 : Nat := 4983230072969 + 3 ^ 40 * 3037828 * 2
def baseEnd_3037828 : Nat := 346636868819254603928731

theorem tailTrace_3037828 : CollatzResearch.WordTrace tailWord_3037828 prefixEnd_3037828 346636868819254603928731 := by
  unfold tailWord_3037828
  simp only [CollatzResearch.WordTrace]
  refine ⟨55399344819237725281081069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73865793092316967041441425 55399344819237725281081069)
  ·
    refine ⟨20774754307214146980405401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55399344819237725281081069 20774754307214146980405401)
    ·
      refine ⟨15581065730410610235304051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20774754307214146980405401 15581065730410610235304051)
      ·
        refine ⟨23371598595615915352956077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15581065730410610235304051 23371598595615915352956077)
        ·
          refine ⟨8764349473355968257358529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23371598595615915352956077 8764349473355968257358529)
          ·
            refine ⟨6573262105016976193018897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8764349473355968257358529 6573262105016976193018897)
            ·
              refine ⟨4929946578762732144764173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6573262105016976193018897 4929946578762732144764173)
              ·
                refine ⟨1848729967036024554286565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4929946578762732144764173 1848729967036024554286565)
                ·
                  refine ⟨346636868819254603928731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1848729967036024554286565 346636868819254603928731)
                  ·
                    rfl

theorem cell22_3037828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_3037828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037828 prefixEnd_3037828 := by exact prefixLift 3037828
  have htrace : WordTrace (prefixWord ++ tailWord_3037828) baseStart_3037828 baseEnd_3037828 := by
    simpa [prefixWord, tailWord_3037828, baseEnd_3037828] using wordTrace_append hprefix tailTrace_3037828
  have hstable : (prefixWord ++ tailWord_3037828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037828).length < 2 ^ (prefixWord ++ tailWord_3037828).sum := by decide
  have hdescent : baseEnd_3037828 < baseStart_3037828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037871 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 3, 3]
def baseStart_3037871 : Nat := 118140960795 + 3037871 * 2 ^ 59
def prefixEnd_3037871 : Nat := 4983230072969 + 3 ^ 40 * 3037871 * 2
def baseEnd_3037871 : Nat := 1039925326236526032961061

theorem tailTrace_3037871 : CollatzResearch.WordTrace tailWord_3037871 prefixEnd_3037871 1039925326236526032961061 := by
  unfold tailWord_3037871
  simp only [CollatzResearch.WordTrace]
  refine ⟨110800257977319668905977467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73866838651546445937318311 110800257977319668905977467)
  ·
    refine ⟨166200386965979503358966201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110800257977319668905977467 166200386965979503358966201)
    ·
      refine ⟨124650290224484627519224651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166200386965979503358966201 124650290224484627519224651)
      ·
        refine ⟨186975435336726941278836977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124650290224484627519224651 186975435336726941278836977)
        ·
          refine ⟨140231576502545205959127733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186975435336726941278836977 140231576502545205959127733)
          ·
            refine ⟨13146710297113613058668225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140231576502545205959127733 13146710297113613058668225)
            ·
              refine ⟨9860032722835209794001169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13146710297113613058668225 9860032722835209794001169)
              ·
                refine ⟨7395024542126407345500877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9860032722835209794001169 7395024542126407345500877)
                ·
                  refine ⟨2773134203297402754562829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7395024542126407345500877 2773134203297402754562829)
                  ·
                    refine ⟨1039925326236526032961061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2773134203297402754562829 1039925326236526032961061)
                    ·
                      rfl

theorem cell22_3037871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 3].length) (baseStart_3037871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037871 prefixEnd_3037871 := by exact prefixLift 3037871
  have htrace : WordTrace (prefixWord ++ tailWord_3037871) baseStart_3037871 baseEnd_3037871 := by
    simpa [prefixWord, tailWord_3037871, baseEnd_3037871] using wordTrace_append hprefix tailTrace_3037871
  have hstable : (prefixWord ++ tailWord_3037871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037871).length < 2 ^ (prefixWord ++ tailWord_3037871).sum := by decide
  have hdescent : baseEnd_3037871 < baseStart_3037871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037884 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 9]
def baseStart_3037884 : Nat := 118140960795 + 3037884 * 2 ^ 59
def prefixEnd_3037884 : Nat := 4983230072969 + 3 ^ 40 * 3037884 * 2
def baseEnd_3037884 : Nat := 346643258800732777462007

theorem tailTrace_3037884 : CollatzResearch.WordTrace tailWord_3037884 prefixEnd_3037884 346643258800732777462007 := by
  unfold tailWord_3037884
  simp only [CollatzResearch.WordTrace]
  refine ⟨55400366063136286063100353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73867154750848381417467137 55400366063136286063100353)
  ·
    refine ⟨41550274547352214547325265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55400366063136286063100353 41550274547352214547325265)
    ·
      refine ⟨31162705910514160910493949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41550274547352214547325265 31162705910514160910493949)
      ·
        refine ⟨11686014716442810341435231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31162705910514160910493949 11686014716442810341435231)
        ·
          refine ⟨17529022074664215512152847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11686014716442810341435231 17529022074664215512152847)
          ·
            refine ⟨26293533111996323268229271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17529022074664215512152847 26293533111996323268229271)
            ·
              refine ⟨39440299667994484902343907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26293533111996323268229271 39440299667994484902343907)
              ·
                refine ⟨59160449501991727353515861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39440299667994484902343907 59160449501991727353515861)
                ·
                  refine ⟨346643258800732777462007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59160449501991727353515861 346643258800732777462007)
                  ·
                    rfl

theorem cell22_3037884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_3037884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037884 prefixEnd_3037884 := by exact prefixLift 3037884
  have htrace : WordTrace (prefixWord ++ tailWord_3037884) baseStart_3037884 baseEnd_3037884 := by
    simpa [prefixWord, tailWord_3037884, baseEnd_3037884] using wordTrace_append hprefix tailTrace_3037884
  have hstable : (prefixWord ++ tailWord_3037884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037884).length < 2 ^ (prefixWord ++ tailWord_3037884).sum := by decide
  have hdescent : baseEnd_3037884 < baseStart_3037884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037905 : List Nat := [1, 2, 2, 1, 2, 3, 5, 2, 1, 3]
def baseStart_3037905 : Nat := 118140960795 + 3037905 * 2 ^ 59
def prefixEnd_3037905 : Nat := 4983230072969 + 3 ^ 40 * 3037905 * 2
def baseEnd_3037905 : Nat := 1039936965131361277610957

theorem tailTrace_3037905 : CollatzResearch.WordTrace tailWord_3037905 prefixEnd_3037905 1039936965131361277610957 := by
  unfold tailWord_3037905
  simp only [CollatzResearch.WordTrace]
  refine ⟨110801498059196492712715169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73867665372797661808476779 110801498059196492712715169)
  ·
    refine ⟨83101123544397369534536377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110801498059196492712715169 83101123544397369534536377)
    ·
      refine ⟨62325842658298027150902283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83101123544397369534536377 62325842658298027150902283)
      ·
        refine ⟨93488763987447040726353425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62325842658298027150902283 93488763987447040726353425)
        ·
          refine ⟨70116572990585280544765069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93488763987447040726353425 70116572990585280544765069)
          ·
            refine ⟨26293714871469480204286901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70116572990585280544765069 26293714871469480204286901)
            ·
              refine ⟨2465035769200263769151897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26293714871469480204286901 2465035769200263769151897)
              ·
                refine ⟨1848776826900197826863923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2465035769200263769151897 1848776826900197826863923)
                ·
                  refine ⟨2773165240350296740295885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1848776826900197826863923 2773165240350296740295885)
                  ·
                    refine ⟨1039936965131361277610957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2773165240350296740295885 1039936965131361277610957)
                    ·
                      rfl

theorem cell22_3037905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_3037905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037905 prefixEnd_3037905 := by exact prefixLift 3037905
  have htrace : WordTrace (prefixWord ++ tailWord_3037905) baseStart_3037905 baseEnd_3037905 := by
    simpa [prefixWord, tailWord_3037905, baseEnd_3037905] using wordTrace_append hprefix tailTrace_3037905
  have hstable : (prefixWord ++ tailWord_3037905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037905).length < 2 ^ (prefixWord ++ tailWord_3037905).sum := by decide
  have hdescent : baseEnd_3037905 < baseStart_3037905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037929 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 6]
def baseStart_3037929 : Nat := 118140960795 + 3037929 * 2 ^ 59
def prefixEnd_3037929 : Nat := 4983230072969 + 3 ^ 40 * 3037929 * 2
def baseEnd_3037929 : Nat := 346648393607277738336961

theorem tailTrace_3037929 : CollatzResearch.WordTrace tailWord_3037929 prefixEnd_3037929 346648393607277738336961 := by
  unfold tailWord_3037929
  simp only [CollatzResearch.WordTrace]
  refine ⟨110802373411109544811588841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73868248940739696541059227 110802373411109544811588841)
  ·
    refine ⟨83101780058332158608691631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110802373411109544811588841 83101780058332158608691631)
    ·
      refine ⟨124652670087498237913037447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83101780058332158608691631 124652670087498237913037447)
      ·
        refine ⟨186979005131247356869556171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124652670087498237913037447 186979005131247356869556171)
        ·
          refine ⟨280468507696871035304334257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186979005131247356869556171 280468507696871035304334257)
          ·
            refine ⟨210351380772653276478250693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280468507696871035304334257 210351380772653276478250693)
            ·
              refine ⟨39440883894872489339672005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210351380772653276478250693 39440883894872489339672005)
              ·
                refine ⟨7395165730288591751188501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39440883894872489339672005 7395165730288591751188501)
                ·
                  refine ⟨346648393607277738336961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7395165730288591751188501 346648393607277738336961)
                  ·
                    rfl

theorem cell22_3037929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 6].length) (baseStart_3037929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037929 prefixEnd_3037929 := by exact prefixLift 3037929
  have htrace : WordTrace (prefixWord ++ tailWord_3037929) baseStart_3037929 baseEnd_3037929 := by
    simpa [prefixWord, tailWord_3037929, baseEnd_3037929] using wordTrace_append hprefix tailTrace_3037929
  have hstable : (prefixWord ++ tailWord_3037929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037929).length < 2 ^ (prefixWord ++ tailWord_3037929).sum := by decide
  have hdescent : baseEnd_3037929 < baseStart_3037929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037961 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 4, 3]
def baseStart_3037961 : Nat := 118140960795 + 3037961 * 2 ^ 59
def prefixEnd_3037961 : Nat := 4983230072969 + 3 ^ 40 * 3037961 * 2
def baseEnd_3037961 : Nat := 1039956135075795798210785

theorem tailTrace_3037961 : CollatzResearch.WordTrace tailWord_3037961 prefixEnd_3037961 1039956135075795798210785 := by
  unfold tailWord_3037961
  simp only [CollatzResearch.WordTrace]
  refine ⟨110803540546993614276753737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73869027031329076184502491 110803540546993614276753737)
  ·
    refine ⟨83102655410245210707565303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110803540546993614276753737 83102655410245210707565303)
    ·
      refine ⟨124653983115367816061347955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83102655410245210707565303 124653983115367816061347955)
      ·
        refine ⟨186980974673051724092021933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124653983115367816061347955 186980974673051724092021933)
        ·
          refine ⟨70117865502394396534508225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186980974673051724092021933 70117865502394396534508225)
          ·
            refine ⟨52588399126795797400881169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70117865502394396534508225 52588399126795797400881169)
            ·
              refine ⟨39441299345096848050660877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52588399126795797400881169 39441299345096848050660877)
              ·
                refine ⟨14790487254411318018997829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39441299345096848050660877 14790487254411318018997829)
                ·
                  refine ⟨2773216360202122128562093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14790487254411318018997829 2773216360202122128562093)
                  ·
                    refine ⟨1039956135075795798210785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2773216360202122128562093 1039956135075795798210785)
                    ·
                      rfl

theorem cell22_3037961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 3].length) (baseStart_3037961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037961 prefixEnd_3037961 := by exact prefixLift 3037961
  have htrace : WordTrace (prefixWord ++ tailWord_3037961) baseStart_3037961 baseEnd_3037961 := by
    simpa [prefixWord, tailWord_3037961, baseEnd_3037961] using wordTrace_append hprefix tailTrace_3037961
  have hstable : (prefixWord ++ tailWord_3037961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037961).length < 2 ^ (prefixWord ++ tailWord_3037961).sum := by decide
  have hdescent : baseEnd_3037961 < baseStart_3037961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037978 : List Nat := [3, 1, 1, 3, 2, 1, 1, 5, 2, 3]
def baseStart_3037978 : Nat := 118140960795 + 3037978 * 2 ^ 59
def prefixEnd_3037978 : Nat := 4983230072969 + 3 ^ 40 * 3037978 * 2
def baseEnd_3037978 : Nat := 1039961954523213420535733

theorem tailTrace_3037978 : CollatzResearch.WordTrace tailWord_3037978 prefixEnd_3037978 1039961954523213420535733 := by
  unfold tailWord_3037978
  simp only [CollatzResearch.WordTrace]
  refine ⟨27701040146983006545030647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73869440391954684120081725 27701040146983006545030647)
  ·
    refine ⟨41551560220474509817545971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27701040146983006545030647 41551560220474509817545971)
    ·
      refine ⟨62327340330711764726318957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41551560220474509817545971 62327340330711764726318957)
      ·
        refine ⟨23372752624016911772369609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62327340330711764726318957 23372752624016911772369609)
        ·
          refine ⟨17529564468012683829277207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23372752624016911772369609 17529564468012683829277207)
          ·
            refine ⟨26294346702019025743915811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17529564468012683829277207 26294346702019025743915811)
            ·
              refine ⟨39441520053028538615873717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26294346702019025743915811 39441520053028538615873717)
              ·
                refine ⟨3697642504971425495238161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39441520053028538615873717 3697642504971425495238161)
                ·
                  refine ⟨2773231878728569121428621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3697642504971425495238161 2773231878728569121428621)
                  ·
                    refine ⟨1039961954523213420535733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2773231878728569121428621 1039961954523213420535733)
                    ·
                      rfl

theorem cell22_3037978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_3037978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3037978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3037978 prefixEnd_3037978 := by exact prefixLift 3037978
  have htrace : WordTrace (prefixWord ++ tailWord_3037978) baseStart_3037978 baseEnd_3037978 := by
    simpa [prefixWord, tailWord_3037978, baseEnd_3037978] using wordTrace_append hprefix tailTrace_3037978
  have hstable : (prefixWord ++ tailWord_3037978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037978).length < 2 ^ (prefixWord ++ tailWord_3037978).sum := by decide
  have hdescent : baseEnd_3037978 < baseStart_3037978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038029 : List Nat := [1, 6, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_3038029 : Nat := 118140960795 + 3038029 * 2 ^ 59
def prefixEnd_3038029 : Nat := 4983230072969 + 3 ^ 40 * 3038029 * 2
def baseEnd_3038029 : Nat := 1039979412865466287510577

theorem tailTrace_3038029 : CollatzResearch.WordTrace tailWord_3038029 prefixEnd_3038029 1039979412865466287510577 := by
  unfold tailWord_3038029
  simp only [CollatzResearch.WordTrace]
  refine ⟨110806020710747261890229141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73870680473831507926819427 110806020710747261890229141)
  ·
    refine ⟨5194032220816277901104491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110806020710747261890229141 5194032220816277901104491)
    ·
      refine ⟨7791048331224416851656737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5194032220816277901104491 7791048331224416851656737)
      ·
        refine ⟨5843286248418312638742553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7791048331224416851656737 5843286248418312638742553)
        ·
          refine ⟨4382464686313734479056915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5843286248418312638742553 4382464686313734479056915)
          ·
            refine ⟨6573697029470601718585373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4382464686313734479056915 6573697029470601718585373)
            ·
              refine ⟨2465136386051475644469515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6573697029470601718585373 2465136386051475644469515)
              ·
                refine ⟨3697704579077213466704273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2465136386051475644469515 3697704579077213466704273)
                ·
                  refine ⟨2773278434307910100028205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3697704579077213466704273 2773278434307910100028205)
                  ·
                    refine ⟨1039979412865466287510577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2773278434307910100028205 1039979412865466287510577)
                    ·
                      rfl

theorem cell22_3038029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_3038029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3038029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3038029 prefixEnd_3038029 := by exact prefixLift 3038029
  have htrace : WordTrace (prefixWord ++ tailWord_3038029) baseStart_3038029 baseEnd_3038029 := by
    simpa [prefixWord, tailWord_3038029, baseEnd_3038029] using wordTrace_append hprefix tailTrace_3038029
  have hstable : (prefixWord ++ tailWord_3038029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038029).length < 2 ^ (prefixWord ++ tailWord_3038029).sum := by decide
  have hdescent : baseEnd_3038029 < baseStart_3038029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038113 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 3, 5]
def baseStart_3038113 : Nat := 118140960795 + 3038113 * 2 ^ 59
def prefixEnd_3038113 : Nat := 4983230072969 + 3 ^ 40 * 3038113 * 2
def baseEnd_3038113 : Nat := 1040008167782118068410319

theorem tailTrace_3038113 : CollatzResearch.WordTrace tailWord_3038113 prefixEnd_3038113 1040008167782118068410319 := by
  unfold tailWord_3038113
  simp only [CollatzResearch.WordTrace]
  refine ⟨110809084442442944236286993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73872722961628629490857995 110809084442442944236286993)
  ·
    refine ⟨83106813331832208177215245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110809084442442944236286993 83106813331832208177215245)
    ·
      refine ⟨31165054999437078066455717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83106813331832208177215245 31165054999437078066455717)
      ·
        refine ⟨5843447812394452137460447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31165054999437078066455717 5843447812394452137460447)
        ·
          refine ⟨8765171718591678206190671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5843447812394452137460447 8765171718591678206190671)
          ·
            refine ⟨13147757577887517309286007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8765171718591678206190671 13147757577887517309286007)
            ·
              refine ⟨19721636366831275963929011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13147757577887517309286007 19721636366831275963929011)
              ·
                refine ⟨29582454550246913945893517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19721636366831275963929011 29582454550246913945893517)
                ·
                  refine ⟨11093420456342592729710069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29582454550246913945893517 11093420456342592729710069)
                  ·
                    refine ⟨1040008167782118068410319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11093420456342592729710069 1040008167782118068410319)
                    ·
                      rfl

theorem cell22_3038113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_3038113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3038113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3038113 prefixEnd_3038113 := by exact prefixLift 3038113
  have htrace : WordTrace (prefixWord ++ tailWord_3038113) baseStart_3038113 baseEnd_3038113 := by
    simpa [prefixWord, tailWord_3038113, baseEnd_3038113] using wordTrace_append hprefix tailTrace_3038113
  have hstable : (prefixWord ++ tailWord_3038113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038113).length < 2 ^ (prefixWord ++ tailWord_3038113).sum := by decide
  have hdescent : baseEnd_3038113 < baseStart_3038113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038162 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 2, 4]
def baseStart_3038162 : Nat := 118140960795 + 3038162 * 2 ^ 59
def prefixEnd_3038162 : Nat := 4983230072969 + 3 ^ 40 * 3038162 * 2
def baseEnd_3038162 : Nat := 1040024941483498273935169

theorem tailTrace_3038162 : CollatzResearch.WordTrace tailWord_3038162 prefixEnd_3038162 1040024941483498273935169 := by
  unfold tailWord_3038162
  simp only [CollatzResearch.WordTrace]
  refine ⟨27702717904816356401205185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73873914412843617069880493 27702717904816356401205185)
  ·
    refine ⟨20777038428612267300903889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27702717904816356401205185 20777038428612267300903889)
    ·
      refine ⟨15582778821459200475677917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20777038428612267300903889 15582778821459200475677917)
      ·
        refine ⟨5843542058047200178379219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15582778821459200475677917 5843542058047200178379219)
        ·
          refine ⟨8765313087070800267568829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5843542058047200178379219 8765313087070800267568829)
          ·
            refine ⟨3286992407651550100338311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8765313087070800267568829 3286992407651550100338311)
            ·
              refine ⟨4930488611477325150507467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3286992407651550100338311 4930488611477325150507467)
              ·
                refine ⟨7395732917215987725761201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4930488611477325150507467 7395732917215987725761201)
                ·
                  refine ⟨5546799687911990794320901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7395732917215987725761201 5546799687911990794320901)
                  ·
                    refine ⟨1040024941483498273935169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5546799687911990794320901 1040024941483498273935169)
                    ·
                      rfl

theorem cell22_3038162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_3038162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3038162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3038162 prefixEnd_3038162 := by exact prefixLift 3038162
  have htrace : WordTrace (prefixWord ++ tailWord_3038162) baseStart_3038162 baseEnd_3038162 := by
    simpa [prefixWord, tailWord_3038162, baseEnd_3038162] using wordTrace_append hprefix tailTrace_3038162
  have hstable : (prefixWord ++ tailWord_3038162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038162).length < 2 ^ (prefixWord ++ tailWord_3038162).sum := by decide
  have hdescent : baseEnd_3038162 < baseStart_3038162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038181 : List Nat := [1, 3, 1, 6, 2, 1, 1, 2, 2, 3]
def baseStart_3038181 : Nat := 118140960795 + 3038181 * 2 ^ 59
def prefixEnd_3038181 : Nat := 4983230072969 + 3 ^ 40 * 3038181 * 2
def baseEnd_3038181 : Nat := 1040031445571788557710111

theorem tailTrace_3038181 : CollatzResearch.WordTrace tailWord_3038181 prefixEnd_3038181 1040031445571788557710111 := by
  unfold tailWord_3038181
  simp only [CollatzResearch.WordTrace]
  refine ⟨110811564606196591849762397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73874376404131061233174931 110811564606196591849762397)
  ·
    refine ⟨41554336727323721943660899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110811564606196591849762397 41554336727323721943660899)
    ·
      refine ⟨62331505090985582915491349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41554336727323721943660899 62331505090985582915491349)
      ·
        refine ⟨2921789301139949199163657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62331505090985582915491349 2921789301139949199163657)
        ·
          refine ⟨2191341975854961899372743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2921789301139949199163657 2191341975854961899372743)
          ·
            refine ⟨3287012963782442849059115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191341975854961899372743 3287012963782442849059115)
            ·
              refine ⟨4930519445673664273588673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3287012963782442849059115 4930519445673664273588673)
              ·
                refine ⟨3697889584255248205191505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4930519445673664273588673 3697889584255248205191505)
                ·
                  refine ⟨2773417188191436153893629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3697889584255248205191505 2773417188191436153893629)
                  ·
                    refine ⟨1040031445571788557710111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2773417188191436153893629 1040031445571788557710111)
                    ·
                      rfl

theorem cell22_3038181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_3038181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3038181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3038181 prefixEnd_3038181 := by exact prefixLift 3038181
  have htrace : WordTrace (prefixWord ++ tailWord_3038181) baseStart_3038181 baseEnd_3038181 := by
    simpa [prefixWord, tailWord_3038181, baseEnd_3038181] using wordTrace_append hprefix tailTrace_3038181
  have hstable : (prefixWord ++ tailWord_3038181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038181).length < 2 ^ (prefixWord ++ tailWord_3038181).sum := by decide
  have hdescent : baseEnd_3038181 < baseStart_3038181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038263 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 6, 4]
def baseStart_3038263 : Nat := 118140960795 + 3038263 * 2 ^ 59
def prefixEnd_3038263 : Nat := 4983230072969 + 3 ^ 40 * 3038263 * 2
def baseEnd_3038263 : Nat := 1040059515847567677159859

theorem tailTrace_3038263 : CollatzResearch.WordTrace tailWord_3038263 prefixEnd_3038263 1040059515847567677159859 := by
  unfold tailWord_3038263
  simp only [CollatzResearch.WordTrace]
  refine ⟨110814555391899519854247443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73876370261266346569498295 110814555391899519854247443)
  ·
    refine ⟨166221833087849279781371165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110814555391899519854247443 166221833087849279781371165)
    ·
      refine ⟨62333187407943479918014187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166221833087849279781371165 62333187407943479918014187)
      ·
        refine ⟨93499781111915219877021281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62333187407943479918014187 93499781111915219877021281)
        ·
          refine ⟨70124835833936414907765961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93499781111915219877021281 70124835833936414907765961)
          ·
            refine ⟨52593626875452311180824471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70124835833936414907765961 52593626875452311180824471)
            ·
              refine ⟨78890440313178466771236707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52593626875452311180824471 78890440313178466771236707)
              ·
                refine ⟨118335660469767700156855061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78890440313178466771236707 118335660469767700156855061)
                ·
                  refine ⟨5546984084520360944852581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118335660469767700156855061 5546984084520360944852581)
                  ·
                    refine ⟨1040059515847567677159859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5546984084520360944852581 1040059515847567677159859)
                    ·
                      rfl

theorem cell22_3038263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_3038263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3038263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3038263 prefixEnd_3038263 := by exact prefixLift 3038263
  have htrace : WordTrace (prefixWord ++ tailWord_3038263) baseStart_3038263 baseEnd_3038263 := by
    simpa [prefixWord, tailWord_3038263, baseEnd_3038263] using wordTrace_append hprefix tailTrace_3038263
  have hstable : (prefixWord ++ tailWord_3038263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038263).length < 2 ^ (prefixWord ++ tailWord_3038263).sum := by decide
  have hdescent : baseEnd_3038263 < baseStart_3038263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038280 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 2, 4]
def baseStart_3038280 : Nat := 118140960795 + 3038280 * 2 ^ 59
def prefixEnd_3038280 : Nat := 4983230072969 + 3 ^ 40 * 3038280 * 2
def baseEnd_3038280 : Nat := 1040065335294985299484807

theorem tailTrace_3038280 : CollatzResearch.WordTrace tailWord_3038280 prefixEnd_3038280 1040065335294985299484807 := by
  unfold tailWord_3038280
  simp only [CollatzResearch.WordTrace]
  refine ⟨55407587716418965878808147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73876783621891954505077529 55407587716418965878808147)
  ·
    refine ⟨83111381574628448818212221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55407587716418965878808147 83111381574628448818212221)
    ·
      refine ⟨31166768090485668306829583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83111381574628448818212221 31166768090485668306829583)
      ·
        refine ⟨46750152135728502460244375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31166768090485668306829583 46750152135728502460244375)
        ·
          refine ⟨70125228203592753690366563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46750152135728502460244375 70125228203592753690366563)
          ·
            refine ⟨105187842305389130535549845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70125228203592753690366563 105187842305389130535549845)
            ·
              refine ⟨4930680108065115493853899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105187842305389130535549845 4930680108065115493853899)
              ·
                refine ⟨7396020162097673240780849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4930680108065115493853899 7396020162097673240780849)
                ·
                  refine ⟨5547015121573254930585637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7396020162097673240780849 5547015121573254930585637)
                  ·
                    refine ⟨1040065335294985299484807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5547015121573254930585637 1040065335294985299484807)
                    ·
                      rfl

theorem cell22_3038280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_3038280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3038280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3038280 prefixEnd_3038280 := by exact prefixLift 3038280
  have htrace : WordTrace (prefixWord ++ tailWord_3038280) baseStart_3038280 baseEnd_3038280 := by
    simpa [prefixWord, tailWord_3038280, baseEnd_3038280] using wordTrace_append hprefix tailTrace_3038280
  have hstable : (prefixWord ++ tailWord_3038280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038280).length < 2 ^ (prefixWord ++ tailWord_3038280).sum := by decide
  have hdescent : baseEnd_3038280 < baseStart_3038280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038417 : List Nat := [1, 2, 2, 1, 2, 2, 1, 6, 2, 3]
def baseStart_3038417 : Nat := 118140960795 + 3038417 * 2 ^ 59
def prefixEnd_3038417 : Nat := 4983230072969 + 3 ^ 40 * 3038417 * 2
def baseEnd_3038417 : Nat := 1040112233194762608809387

theorem tailTrace_3038417 : CollatzResearch.WordTrace tailWord_3038417 prefixEnd_3038417 1040112233194762608809387 := by
  unfold tailWord_3038417
  simp only [CollatzResearch.WordTrace]
  refine ⟨110820172233341604155353505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73880114822227736103569003 110820172233341604155353505)
  ·
    refine ⟨83115129175006203116515129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110820172233341604155353505 83115129175006203116515129)
    ·
      refine ⟨62336346881254652337386347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83115129175006203116515129 62336346881254652337386347)
      ·
        refine ⟨93504520321881978506079521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62336346881254652337386347 93504520321881978506079521)
        ·
          refine ⟨70128390241411483879559641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93504520321881978506079521 70128390241411483879559641)
          ·
            refine ⟨52596292681058612909669731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70128390241411483879559641 52596292681058612909669731)
            ·
              refine ⟨78894439021587919364504597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52596292681058612909669731 78894439021587919364504597)
              ·
                refine ⟨3698176829136933720211153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78894439021587919364504597 3698176829136933720211153)
                ·
                  refine ⟨2773632621852700290158365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3698176829136933720211153 2773632621852700290158365)
                  ·
                    refine ⟨1040112233194762608809387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2773632621852700290158365 1040112233194762608809387)
                    ·
                      rfl

theorem cell22_3038417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_3038417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3038417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3038417 prefixEnd_3038417 := by exact prefixLift 3038417
  have htrace : WordTrace (prefixWord ++ tailWord_3038417) baseStart_3038417 baseEnd_3038417 := by
    simpa [prefixWord, tailWord_3038417, baseEnd_3038417] using wordTrace_append hprefix tailTrace_3038417
  have hstable : (prefixWord ++ tailWord_3038417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038417).length < 2 ^ (prefixWord ++ tailWord_3038417).sum := by decide
  have hdescent : baseEnd_3038417 < baseStart_3038417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038492 : List Nat := [2, 2, 3, 1, 1, 1, 4, 3, 5]
def baseStart_3038492 : Nat := 118140960795 + 3038492 * 2 ^ 59
def prefixEnd_3038492 : Nat := 4983230072969 + 3 ^ 40 * 3038492 * 2
def baseEnd_3038492 : Nat := 346712635742495804394719

theorem tailTrace_3038492 : CollatzResearch.WordTrace tailWord_3038492 prefixEnd_3038492 346712635742495804394719 := by
  unfold tailWord_3038492
  simp only [CollatzResearch.WordTrace]
  refine ⟨55411453854034945982166865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73881938472046594642889153 55411453854034945982166865)
  ·
    refine ⟨41558590390526209486625149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55411453854034945982166865 41558590390526209486625149)
    ·
      refine ⟨15584471396447328557484431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41558590390526209486625149 15584471396447328557484431)
      ·
        refine ⟨23376707094670992836226647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15584471396447328557484431 23376707094670992836226647)
        ·
          refine ⟨35065060642006489254339971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23376707094670992836226647 35065060642006489254339971)
          ·
            refine ⟨52597590963009733881509957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35065060642006489254339971 52597590963009733881509957)
            ·
              refine ⟨9862048305564325102783117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52597590963009733881509957 9862048305564325102783117)
              ·
                refine ⟨3698268114586621913543669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9862048305564325102783117 3698268114586621913543669)
                ·
                  refine ⟨346712635742495804394719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3698268114586621913543669 346712635742495804394719)
                  ·
                    rfl

theorem cell22_3038492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_3038492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3038492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3038492 prefixEnd_3038492 := by exact prefixLift 3038492
  have htrace : WordTrace (prefixWord ++ tailWord_3038492) baseStart_3038492 baseEnd_3038492 := by
    simpa [prefixWord, tailWord_3038492, baseEnd_3038492] using wordTrace_append hprefix tailTrace_3038492
  have hstable : (prefixWord ++ tailWord_3038492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038492).length < 2 ^ (prefixWord ++ tailWord_3038492).sum := by decide
  have hdescent : baseEnd_3038492 < baseStart_3038492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038520 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 10]
def baseStart_3038520 : Nat := 118140960795 + 3038520 * 2 ^ 59
def prefixEnd_3038520 : Nat := 4983230072969 + 3 ^ 40 * 3038520 * 2
def baseEnd_3038520 : Nat := 346715830733234891161357

theorem tailTrace_3038520 : CollatzResearch.WordTrace tailWord_3038520 prefixEnd_3038520 346715830733234891161357 := by
  unfold tailWord_3038520
  simp only [CollatzResearch.WordTrace]
  refine ⟨55411964475984226373176507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73882619301312301830902009 55411964475984226373176507)
  ·
    refine ⟨83117946713976339559764761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55411964475984226373176507 83117946713976339559764761)
    ·
      refine ⟨62338460035482254669823571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83117946713976339559764761 62338460035482254669823571)
      ·
        refine ⟨93507690053223382004735357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62338460035482254669823571 93507690053223382004735357)
        ·
          refine ⟨35065383769958768251775759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93507690053223382004735357 35065383769958768251775759)
          ·
            refine ⟨52598075654938152377663639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35065383769958768251775759 52598075654938152377663639)
            ·
              refine ⟨78897113482407228566495459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52598075654938152377663639 78897113482407228566495459)
              ·
                refine ⟨118345670223610842849743189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78897113482407228566495459 118345670223610842849743189)
                ·
                  refine ⟨346715830733234891161357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 118345670223610842849743189 346715830733234891161357)
                  ·
                    rfl

theorem cell22_3038520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 10].length) (baseStart_3038520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3038520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3038520 prefixEnd_3038520 := by exact prefixLift 3038520
  have htrace : WordTrace (prefixWord ++ tailWord_3038520) baseStart_3038520 baseEnd_3038520 := by
    simpa [prefixWord, tailWord_3038520, baseEnd_3038520] using wordTrace_append hprefix tailTrace_3038520
  have hstable : (prefixWord ++ tailWord_3038520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038520).length < 2 ^ (prefixWord ++ tailWord_3038520).sum := by decide
  have hdescent : baseEnd_3038520 < baseStart_3038520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038648 : List Nat := [2, 1, 2, 1, 2, 2, 6, 2, 1, 3]
def baseStart_3038648 : Nat := 118140960795 + 3038648 * 2 ^ 59
def prefixEnd_3038648 : Nat := 4983230072969 + 3 ^ 40 * 3038648 * 2
def baseEnd_3038648 : Nat := 1040191309215555006283679

theorem tailTrace_3038648 : CollatzResearch.WordTrace tailWord_3038648 prefixEnd_3038648 1040191309215555006283679 := by
  unfold tailWord_3038648
  simp only [CollatzResearch.WordTrace]
  refine ⟨55414298747752365303506299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73885731663669820404675065 55414298747752365303506299)
  ·
    refine ⟨83121448121628547955259449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55414298747752365303506299 83121448121628547955259449)
    ·
      refine ⟨62341086091221410966444587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83121448121628547955259449 62341086091221410966444587)
      ·
        refine ⟨93511629136832116449666881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62341086091221410966444587 93511629136832116449666881)
        ·
          refine ⟨70133721852624087337250161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93511629136832116449666881 70133721852624087337250161)
          ·
            refine ⟨52600291389468065502937621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70133721852624087337250161 52600291389468065502937621)
            ·
              refine ⟨2465638658881315570450201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52600291389468065502937621 2465638658881315570450201)
              ·
                refine ⟨1849228994160986677837651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2465638658881315570450201 1849228994160986677837651)
                ·
                  refine ⟨2773843491241480016756477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849228994160986677837651 2773843491241480016756477)
                  ·
                    refine ⟨1040191309215555006283679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2773843491241480016756477 1040191309215555006283679)
                    ·
                      rfl

theorem cell22_3038648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_3038648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3038648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3038648 prefixEnd_3038648 := by exact prefixLift 3038648
  have htrace : WordTrace (prefixWord ++ tailWord_3038648) baseStart_3038648 baseEnd_3038648 := by
    simpa [prefixWord, tailWord_3038648, baseEnd_3038648] using wordTrace_append hprefix tailTrace_3038648
  have hstable : (prefixWord ++ tailWord_3038648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038648).length < 2 ^ (prefixWord ++ tailWord_3038648).sum := by decide
  have hdescent : baseEnd_3038648 < baseStart_3038648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038672 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 6]
def baseStart_3038672 : Nat := 118140960795 + 3038672 * 2 ^ 59
def prefixEnd_3038672 : Nat := 4983230072969 + 3 ^ 40 * 3038672 * 2
def baseEnd_3038672 : Nat := 346733174968675647894535

theorem tailTrace_3038672 : CollatzResearch.WordTrace tailWord_3038672 prefixEnd_3038672 346733174968675647894535 := by
  unfold tailWord_3038672
  simp only [CollatzResearch.WordTrace]
  refine ⟨55414736423708891352943135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73886315231611855137257513 55414736423708891352943135)
  ·
    refine ⟨83122104635563337029414703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55414736423708891352943135 83122104635563337029414703)
    ·
      refine ⟨124683156953345005544122055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83122104635563337029414703 124683156953345005544122055)
      ·
        refine ⟨187024735430017508316183083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124683156953345005544122055 187024735430017508316183083)
        ·
          refine ⟨280537103145026262474274625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187024735430017508316183083 280537103145026262474274625)
          ·
            refine ⟨210402827358769696855705969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280537103145026262474274625 210402827358769696855705969)
            ·
              refine ⟨157802120519077272641779477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210402827358769696855705969 157802120519077272641779477)
              ·
                refine ⟨7396974399331747155083413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 157802120519077272641779477 7396974399331747155083413)
                ·
                  refine ⟨346733174968675647894535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7396974399331747155083413 346733174968675647894535)
                  ·
                    rfl

theorem cell22_3038672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 6].length) (baseStart_3038672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3038672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3038672 prefixEnd_3038672 := by exact prefixLift 3038672
  have htrace : WordTrace (prefixWord ++ tailWord_3038672) baseStart_3038672 baseEnd_3038672 := by
    simpa [prefixWord, tailWord_3038672, baseEnd_3038672] using wordTrace_append hprefix tailTrace_3038672
  have hstable : (prefixWord ++ tailWord_3038672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038672).length < 2 ^ (prefixWord ++ tailWord_3038672).sum := by decide
  have hdescent : baseEnd_3038672 < baseStart_3038672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038691 : List Nat := [1, 1, 1, 6, 2, 2, 1, 3, 1, 4]
def baseStart_3038691 : Nat := 118140960795 + 3038691 * 2 ^ 59
def prefixEnd_3038691 : Nat := 4983230072969 + 3 ^ 40 * 3038691 * 2
def baseEnd_3038691 : Nat := 1040206028994317227458547

theorem tailTrace_3038691 : CollatzResearch.WordTrace tailWord_3038691 prefixEnd_3038691 1040206028994317227458547 := by
  unfold tailWord_3038691
  simp only [CollatzResearch.WordTrace]
  refine ⟨110830165834348948950827927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73886777222899299300551951 110830165834348948950827927)
  ·
    refine ⟨166245248751523423426241891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110830165834348948950827927 166245248751523423426241891)
    ·
      refine ⟨249367873127285135139362837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166245248751523423426241891 249367873127285135139362837)
      ·
        refine ⟨11689119052841490709657633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 249367873127285135139362837 11689119052841490709657633)
        ·
          refine ⟨8766839289631118032243225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11689119052841490709657633 8766839289631118032243225)
          ·
            refine ⟨6575129467223338524182419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8766839289631118032243225 6575129467223338524182419)
            ·
              refine ⟨9862694200835007786273629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6575129467223338524182419 9862694200835007786273629)
              ·
                refine ⟨3698510325313127919852611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9862694200835007786273629 3698510325313127919852611)
                ·
                  refine ⟨5547765487969691879778917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3698510325313127919852611 5547765487969691879778917)
                  ·
                    refine ⟨1040206028994317227458547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5547765487969691879778917 1040206028994317227458547)
                    ·
                      rfl

theorem cell22_3038691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 4].length) (baseStart_3038691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3038691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3038691 prefixEnd_3038691 := by exact prefixLift 3038691
  have htrace : WordTrace (prefixWord ++ tailWord_3038691) baseStart_3038691 baseEnd_3038691 := by
    simpa [prefixWord, tailWord_3038691, baseEnd_3038691] using wordTrace_append hprefix tailTrace_3038691
  have hstable : (prefixWord ++ tailWord_3038691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038691).length < 2 ^ (prefixWord ++ tailWord_3038691).sum := by decide
  have hdescent : baseEnd_3038691 < baseStart_3038691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038706 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 6]
def baseStart_3038706 : Nat := 118140960795 + 3038706 * 2 ^ 59
def prefixEnd_3038706 : Nat := 4983230072969 + 3 ^ 40 * 3038706 * 2
def baseEnd_3038706 : Nat := 346737054600287396111167

theorem tailTrace_3038706 : CollatzResearch.WordTrace tailWord_3038706 prefixEnd_3038706 346737054600287396111167 := by
  unfold tailWord_3038706
  simp only [CollatzResearch.WordTrace]
  refine ⟨27707678232323651628155993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73887141952863071008415981 27707678232323651628155993)
  ·
    refine ⟨20780758674242738721116995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27707678232323651628155993 20780758674242738721116995)
    ·
      refine ⟨31171138011364108081675493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20780758674242738721116995 31171138011364108081675493)
      ·
        refine ⟨5844588377130770265314155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31171138011364108081675493 5844588377130770265314155)
        ·
          refine ⟨8766882565696155397971233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5844588377130770265314155 8766882565696155397971233)
          ·
            refine ⟨6575161924272116548478425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8766882565696155397971233 6575161924272116548478425)
            ·
              refine ⟨4931371443204087411358819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6575161924272116548478425 4931371443204087411358819)
              ·
                refine ⟨7397057164806131117038229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4931371443204087411358819 7397057164806131117038229)
                ·
                  refine ⟨346737054600287396111167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7397057164806131117038229 346737054600287396111167)
                  ·
                    rfl

theorem cell22_3038706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_3038706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3038706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3038706 prefixEnd_3038706 := by exact prefixLift 3038706
  have htrace : WordTrace (prefixWord ++ tailWord_3038706) baseStart_3038706 baseEnd_3038706 := by
    simpa [prefixWord, tailWord_3038706, baseEnd_3038706] using wordTrace_append hprefix tailTrace_3038706
  have hstable : (prefixWord ++ tailWord_3038706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038706).length < 2 ^ (prefixWord ++ tailWord_3038706).sum := by decide
  have hdescent : baseEnd_3038706 < baseStart_3038706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038826 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 3, 4]
def baseStart_3038826 : Nat := 118140960795 + 3038826 * 2 ^ 59
def prefixEnd_3038826 : Nat := 4983230072969 + 3 ^ 40 * 3038826 * 2
def baseEnd_3038826 : Nat := 1040252242253221875333133

theorem tailTrace_3038826 : CollatzResearch.WordTrace tailWord_3038826 prefixEnd_3038826 1040252242253221875333133 := by
  unfold tailWord_3038826
  simp only [CollatzResearch.WordTrace]
  refine ⟨27708772422214966751748083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73890059792573244671328221 27708772422214966751748083)
  ·
    refine ⟨41563158633322450127622125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27708772422214966751748083 41563158633322450127622125)
    ·
      refine ⟨15586184487495918797858297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41563158633322450127622125 15586184487495918797858297)
      ·
        refine ⟨11689638365621939098393723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15586184487495918797858297 11689638365621939098393723)
        ·
          refine ⟨17534457548432908647590585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11689638365621939098393723 17534457548432908647590585)
          ·
            refine ⟨13150843161324681485692939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17534457548432908647590585 13150843161324681485692939)
            ·
              refine ⟨19726264741987022228539409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13150843161324681485692939 19726264741987022228539409)
              ·
                refine ⟨14794698556490266671404557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19726264741987022228539409 14794698556490266671404557)
                ·
                  refine ⟨5548011958683850001776709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14794698556490266671404557 5548011958683850001776709)
                  ·
                    refine ⟨1040252242253221875333133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5548011958683850001776709 1040252242253221875333133)
                    ·
                      rfl

theorem cell22_3038826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_3038826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3038826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3038826 prefixEnd_3038826 := by exact prefixLift 3038826
  have htrace : WordTrace (prefixWord ++ tailWord_3038826) baseStart_3038826 baseEnd_3038826 := by
    simpa [prefixWord, tailWord_3038826, baseEnd_3038826] using wordTrace_append hprefix tailTrace_3038826
  have hstable : (prefixWord ++ tailWord_3038826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038826).length < 2 ^ (prefixWord ++ tailWord_3038826).sum := by decide
  have hdescent : baseEnd_3038826 < baseStart_3038826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038858 : List Nat := [3, 1, 2, 3, 2, 1, 1, 5, 4]
def baseStart_3038858 : Nat := 118140960795 + 3038858 * 2 ^ 59
def prefixEnd_3038858 : Nat := 4983230072969 + 3 ^ 40 * 3038858 * 2
def baseEnd_3038858 : Nat := 346754398835728152844345

theorem tailTrace_3038858 : CollatzResearch.WordTrace tailWord_3038858 prefixEnd_3038858 346754398835728152844345 := by
  unfold tailWord_3038858
  simp only [CollatzResearch.WordTrace]
  refine ⟨27709064206185984118039307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73890837883162624314771485 27709064206185984118039307)
  ·
    refine ⟨41563596309278976177058961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27709064206185984118039307 41563596309278976177058961)
    ·
      refine ⟨31172697231959232132794221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41563596309278976177058961 31172697231959232132794221)
      ·
        refine ⟨11689761461984712049797833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31172697231959232132794221 11689761461984712049797833)
        ·
          refine ⟨8767321096488534037348375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11689761461984712049797833 8767321096488534037348375)
          ·
            refine ⟨13150981644732801056022563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8767321096488534037348375 13150981644732801056022563)
            ·
              refine ⟨19726472467099201584033845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13150981644732801056022563 19726472467099201584033845)
              ·
                refine ⟨1849356793790550148503173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19726472467099201584033845 1849356793790550148503173)
                ·
                  refine ⟨346754398835728152844345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1849356793790550148503173 346754398835728152844345)
                  ·
                    rfl

theorem cell22_3038858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_3038858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3038858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3038858 prefixEnd_3038858 := by exact prefixLift 3038858
  have htrace : WordTrace (prefixWord ++ tailWord_3038858) baseStart_3038858 baseEnd_3038858 := by
    simpa [prefixWord, tailWord_3038858, baseEnd_3038858] using wordTrace_append hprefix tailTrace_3038858
  have hstable : (prefixWord ++ tailWord_3038858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038858).length < 2 ^ (prefixWord ++ tailWord_3038858).sum := by decide
  have hdescent : baseEnd_3038858 < baseStart_3038858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038903 : List Nat := [1, 1, 3, 1, 5, 3, 2, 6]
def baseStart_3038903 : Nat := 118140960795 + 3038903 * 2 ^ 59
def prefixEnd_3038903 : Nat := 4983230072969 + 3 ^ 40 * 3038903 * 2
def baseEnd_3038903 : Nat := 115586511214091037906433

theorem tailTrace_3038903 : CollatzResearch.WordTrace tailWord_3038903 prefixEnd_3038903 115586511214091037906433 := by
  unfold tailWord_3038903
  simp only [CollatzResearch.WordTrace]
  refine ⟨110837898109580909157545363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73891932073053939438363575 110837898109580909157545363)
  ·
    refine ⟨166256847164371363736318045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110837898109580909157545363 166256847164371363736318045)
    ·
      refine ⟨62346317686639261401119267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166256847164371363736318045 62346317686639261401119267)
      ·
        refine ⟨93519476529958892101678901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62346317686639261401119267 93519476529958892101678901)
        ·
          refine ⟨8767450924683646134532397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93519476529958892101678901 8767450924683646134532397)
          ·
            refine ⟨3287794096756367300449649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8767450924683646134532397 3287794096756367300449649)
            ·
              refine ⟨2465845572567275475337237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3287794096756367300449649 2465845572567275475337237)
              ·
                refine ⟨115586511214091037906433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2465845572567275475337237 115586511214091037906433)
                ·
                  rfl

theorem cell22_3038903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 6].length) (baseStart_3038903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3038903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3038903 prefixEnd_3038903 := by exact prefixLift 3038903
  have htrace : WordTrace (prefixWord ++ tailWord_3038903) baseStart_3038903 baseEnd_3038903 := by
    simpa [prefixWord, tailWord_3038903, baseEnd_3038903] using wordTrace_append hprefix tailTrace_3038903
  have hstable : (prefixWord ++ tailWord_3038903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038903).length < 2 ^ (prefixWord ++ tailWord_3038903).sum := by decide
  have hdescent : baseEnd_3038903 < baseStart_3038903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038941 : List Nat := [1, 4, 3, 3, 2, 1, 2, 1, 2, 3]
def baseStart_3038941 : Nat := 118140960795 + 3038941 * 2 ^ 59
def prefixEnd_3038941 : Nat := 4983230072969 + 3 ^ 40 * 3038941 * 2
def baseEnd_3038941 : Nat := 1040291609103399908707781

theorem tailTrace_3038941 : CollatzResearch.WordTrace tailWord_3038941 prefixEnd_3038941 1040291609103399908707781 := by
  unfold tailWord_3038941
  simp only [CollatzResearch.WordTrace]
  refine ⟨110839284083443241647428677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73892856055628827764952451 110839284083443241647428677)
  ·
    refine ⟨20782365765645607808892877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110839284083443241647428677 20782365765645607808892877)
    ·
      refine ⟨7793387162117102928334829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20782365765645607808892877 7793387162117102928334829)
      ·
        refine ⟨2922520185793913598125561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7793387162117102928334829 2922520185793913598125561)
        ·
          refine ⟨2191890139345435198594171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2922520185793913598125561 2191890139345435198594171)
          ·
            refine ⟨3287835209018152797891257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191890139345435198594171 3287835209018152797891257)
            ·
              refine ⟨2465876406763614598418443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3287835209018152797891257 2465876406763614598418443)
              ·
                refine ⟨3698814610145421897627665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2465876406763614598418443 3698814610145421897627665)
                ·
                  refine ⟨2774110957609066423220749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3698814610145421897627665 2774110957609066423220749)
                  ·
                    refine ⟨1040291609103399908707781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2774110957609066423220749 1040291609103399908707781)
                    ·
                      rfl

theorem cell22_3038941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_3038941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3038941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3038941 prefixEnd_3038941 := by exact prefixLift 3038941
  have htrace : WordTrace (prefixWord ++ tailWord_3038941) baseStart_3038941 baseEnd_3038941 := by
    simpa [prefixWord, tailWord_3038941, baseEnd_3038941] using wordTrace_append hprefix tailTrace_3038941
  have hstable : (prefixWord ++ tailWord_3038941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038941).length < 2 ^ (prefixWord ++ tailWord_3038941).sum := by decide
  have hdescent : baseEnd_3038941 < baseStart_3038941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039008 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 1, 5]
def baseStart_3039008 : Nat := 118140960795 + 3039008 * 2 ^ 59
def prefixEnd_3039008 : Nat := 4983230072969 + 3 ^ 40 * 3039008 * 2
def baseEnd_3039008 : Nat := 1040314544572634067282575

theorem tailTrace_3039008 : CollatzResearch.WordTrace tailWord_3039008 prefixEnd_3039008 1040314544572634067282575 := by
  unfold tailWord_3039008
  simp only [CollatzResearch.WordTrace]
  refine ⟨55420863887100256045058839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73894485182800341393411785 55420863887100256045058839)
  ·
    refine ⟨83131295830650384067588259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55420863887100256045058839 83131295830650384067588259)
    ·
      refine ⟨124696943745975576101382389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83131295830650384067588259 124696943745975576101382389)
      ·
        refine ⟨11690338476185210259504599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124696943745975576101382389 11690338476185210259504599)
        ·
          refine ⟨17535507714277815389256899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11690338476185210259504599 17535507714277815389256899)
          ·
            refine ⟨26303261571416723083885349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17535507714277815389256899 26303261571416723083885349)
            ·
              refine ⟨4931861544640635578228503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26303261571416723083885349 4931861544640635578228503)
              ·
                refine ⟨7397792316960953367342755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4931861544640635578228503 7397792316960953367342755)
                ·
                  refine ⟨11096688475441430051014133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7397792316960953367342755 11096688475441430051014133)
                  ·
                    refine ⟨1040314544572634067282575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11096688475441430051014133 1040314544572634067282575)
                    ·
                      rfl

theorem cell22_3039008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_3039008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039008 prefixEnd_3039008 := by exact prefixLift 3039008
  have htrace : WordTrace (prefixWord ++ tailWord_3039008) baseStart_3039008 baseEnd_3039008 := by
    simpa [prefixWord, tailWord_3039008, baseEnd_3039008] using wordTrace_append hprefix tailTrace_3039008
  have hstable : (prefixWord ++ tailWord_3039008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039008).length < 2 ^ (prefixWord ++ tailWord_3039008).sum := by decide
  have hdescent : baseEnd_3039008 < baseStart_3039008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039029 : List Nat := [1, 3, 3, 1, 5, 1, 2, 1, 1, 4]
def baseStart_3039029 : Nat := 118140960795 + 3039029 * 2 ^ 59
def prefixEnd_3039029 : Nat := 4983230072969 + 3 ^ 40 * 3039029 * 2
def baseEnd_3039029 : Nat := 1040321733301797012507511

theorem tailTrace_3039029 : CollatzResearch.WordTrace tailWord_3039029 prefixEnd_3039029 1040321733301797012507511 := by
  unfold tailWord_3039029
  simp only [CollatzResearch.WordTrace]
  refine ⟨110842493707124432676632141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73894995804749621784421427 110842493707124432676632141)
  ·
    refine ⟨41565935140171662253737053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110842493707124432676632141 41565935140171662253737053)
    ·
      refine ⟨15587225677564373345151395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41565935140171662253737053 15587225677564373345151395)
      ·
        refine ⟨23380838516346560017727093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15587225677564373345151395 23380838516346560017727093)
        ·
          refine ⟨2191953610907490001661915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23380838516346560017727093 2191953610907490001661915)
          ·
            refine ⟨3287930416361235002492873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191953610907490001661915 3287930416361235002492873)
            ·
              refine ⟨2465947812270926251869655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3287930416361235002492873 2465947812270926251869655)
              ·
                refine ⟨3698921718406389377804483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2465947812270926251869655 3698921718406389377804483)
                ·
                  refine ⟨5548382577609584066706725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3698921718406389377804483 5548382577609584066706725)
                  ·
                    refine ⟨1040321733301797012507511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5548382577609584066706725 1040321733301797012507511)
                    ·
                      rfl

theorem cell22_3039029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_3039029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039029 prefixEnd_3039029 := by exact prefixLift 3039029
  have htrace : WordTrace (prefixWord ++ tailWord_3039029) baseStart_3039029 baseEnd_3039029 := by
    simpa [prefixWord, tailWord_3039029, baseEnd_3039029] using wordTrace_append hprefix tailTrace_3039029
  have hstable : (prefixWord ++ tailWord_3039029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039029).length < 2 ^ (prefixWord ++ tailWord_3039029).sum := by decide
  have hdescent : baseEnd_3039029 < baseStart_3039029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039038 : List Nat := [4, 2, 1, 2, 2, 2, 9]
def baseStart_3039038 : Nat := 118140960795 + 3039038 * 2 ^ 59
def prefixEnd_3039038 : Nat := 4983230072969 + 3 ^ 40 * 3039038 * 2
def baseEnd_3039038 : Nat := 38530548673545332927129

theorem tailTrace_3039038 : CollatzResearch.WordTrace tailWord_3039038 prefixEnd_3039038 38530548673545332927129 := by
  unfold tailWord_3039038
  simp only [CollatzResearch.WordTrace]
  refine ⟨13855352745511478401713721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73895214642727884809139845 13855352745511478401713721)
  ·
    refine ⟨10391514559133608801285291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13855352745511478401713721 10391514559133608801285291)
    ·
      refine ⟨15587271838700413201927937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10391514559133608801285291 15587271838700413201927937)
      ·
        refine ⟨11690453879025309901445953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15587271838700413201927937 11690453879025309901445953)
        ·
          refine ⟨8767840409268982426084465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11690453879025309901445953 8767840409268982426084465)
          ·
            refine ⟨6575880306951736819563349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8767840409268982426084465 6575880306951736819563349)
            ·
              refine ⟨38530548673545332927129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6575880306951736819563349 38530548673545332927129)
              ·
                rfl

theorem cell22_3039038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 9].length) (baseStart_3039038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039038 prefixEnd_3039038 := by exact prefixLift 3039038
  have htrace : WordTrace (prefixWord ++ tailWord_3039038) baseStart_3039038 baseEnd_3039038 := by
    simpa [prefixWord, tailWord_3039038, baseEnd_3039038] using wordTrace_append hprefix tailTrace_3039038
  have hstable : (prefixWord ++ tailWord_3039038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039038).length < 2 ^ (prefixWord ++ tailWord_3039038).sum := by decide
  have hdescent : baseEnd_3039038 < baseStart_3039038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039081 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 1, 7]
def baseStart_3039081 : Nat := 118140960795 + 3039081 * 2 ^ 59
def prefixEnd_3039081 : Nat := 4983230072969 + 3 ^ 40 * 3039081 * 2
def baseEnd_3039081 : Nat := 1040339533964486210207351

theorem tailTrace_3039081 : CollatzResearch.WordTrace tailWord_3039081 prefixEnd_3039081 1040339533964486210207351 := by
  unfold tailWord_3039081
  simp only [CollatzResearch.WordTrace]
  refine ⟨110844390302936045557525097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73896260201957363705016731 110844390302936045557525097)
  ·
    refine ⟨83133292727202034168143823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110844390302936045557525097 83133292727202034168143823)
    ·
      refine ⟨124699939090803051252215735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83133292727202034168143823 124699939090803051252215735)
      ·
        refine ⟨187049908636204576878323603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124699939090803051252215735 187049908636204576878323603)
        ·
          refine ⟨280574862954306865317485405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187049908636204576878323603 280574862954306865317485405)
          ·
            refine ⟨105215573607865074494057027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280574862954306865317485405 105215573607865074494057027)
            ·
              refine ⟨157823360411797611741085541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105215573607865074494057027 157823360411797611741085541)
              ·
                refine ⟨29591880077212052201453539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157823360411797611741085541 29591880077212052201453539)
                ·
                  refine ⟨44387820115818078302180309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29591880077212052201453539 44387820115818078302180309)
                  ·
                    refine ⟨1040339533964486210207351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44387820115818078302180309 1040339533964486210207351)
                    ·
                      rfl

theorem cell22_3039081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_3039081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039081 prefixEnd_3039081 := by exact prefixLift 3039081
  have htrace : WordTrace (prefixWord ++ tailWord_3039081) baseStart_3039081 baseEnd_3039081 := by
    simpa [prefixWord, tailWord_3039081, baseEnd_3039081] using wordTrace_append hprefix tailTrace_3039081
  have hstable : (prefixWord ++ tailWord_3039081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039081).length < 2 ^ (prefixWord ++ tailWord_3039081).sum := by decide
  have hdescent : baseEnd_3039081 < baseStart_3039081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039096 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 1, 10]
def baseStart_3039096 : Nat := 118140960795 + 3039096 * 2 ^ 59
def prefixEnd_3039096 : Nat := 4983230072969 + 3 ^ 40 * 3039096 * 2
def baseEnd_3039096 : Nat := 1040344668771031171082305

theorem tailTrace_3039096 : CollatzResearch.WordTrace tailWord_3039096 prefixEnd_3039096 1040344668771031171082305 := by
  unfold tailWord_3039096
  simp only [CollatzResearch.WordTrace]
  refine ⟨55422468698940851559660571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73896624931921135412880761 55422468698940851559660571)
  ·
    refine ⟨83133703048411277339490857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55422468698940851559660571 83133703048411277339490857)
    ·
      refine ⟨62350277286308458004618143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83133703048411277339490857 62350277286308458004618143)
      ·
        refine ⟨93525415929462687006927215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62350277286308458004618143 93525415929462687006927215)
        ·
          refine ⟨140288123894194030510390823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93525415929462687006927215 140288123894194030510390823)
          ·
            refine ⟨210432185841291045765586235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140288123894194030510390823 210432185841291045765586235)
            ·
              refine ⟨315648278761936568648379353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210432185841291045765586235 315648278761936568648379353)
              ·
                refine ⟨236736209071452426486284515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315648278761936568648379353 236736209071452426486284515)
                ·
                  refine ⟨355104313607178639729426773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236736209071452426486284515 355104313607178639729426773)
                  ·
                    refine ⟨1040344668771031171082305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 355104313607178639729426773 1040344668771031171082305)
                    ·
                      rfl

theorem cell22_3039096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_3039096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039096 prefixEnd_3039096 := by exact prefixLift 3039096
  have htrace : WordTrace (prefixWord ++ tailWord_3039096) baseStart_3039096 baseEnd_3039096 := by
    simpa [prefixWord, tailWord_3039096, baseEnd_3039096] using wordTrace_append hprefix tailTrace_3039096
  have hstable : (prefixWord ++ tailWord_3039096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039096).length < 2 ^ (prefixWord ++ tailWord_3039096).sum := by decide
  have hdescent : baseEnd_3039096 < baseStart_3039096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039113 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 3, 4]
def baseStart_3039113 : Nat := 118140960795 + 3039113 * 2 ^ 59
def prefixEnd_3039113 : Nat := 4983230072969 + 3 ^ 40 * 3039113 * 2
def baseEnd_3039113 : Nat := 1040350488218448793407253

theorem tailTrace_3039113 : CollatzResearch.WordTrace tailWord_3039113 prefixEnd_3039113 1040350488218448793407253 := by
  unfold tailWord_3039113
  simp only [CollatzResearch.WordTrace]
  refine ⟨110845557438820115022689993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73897038292546743348459995 110845557438820115022689993)
  ·
    refine ⟨83134168079115086267017495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110845557438820115022689993 83134168079115086267017495)
    ·
      refine ⟨124701252118672629400526243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83134168079115086267017495 124701252118672629400526243)
      ·
        refine ⟨187051878178008944100789365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124701252118672629400526243 187051878178008944100789365)
        ·
          refine ⟨17536113579188338509449003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187051878178008944100789365 17536113579188338509449003)
          ·
            refine ⟨26304170368782507764173505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17536113579188338509449003 26304170368782507764173505)
            ·
              refine ⟨19728127776586880823130129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26304170368782507764173505 19728127776586880823130129)
              ·
                refine ⟨14796095832440160617347597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19728127776586880823130129 14796095832440160617347597)
                ·
                  refine ⟨5548535937165060231505349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14796095832440160617347597 5548535937165060231505349)
                  ·
                    refine ⟨1040350488218448793407253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5548535937165060231505349 1040350488218448793407253)
                    ·
                      rfl

theorem cell22_3039113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_3039113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039113 prefixEnd_3039113 := by exact prefixLift 3039113
  have htrace : WordTrace (prefixWord ++ tailWord_3039113) baseStart_3039113 baseEnd_3039113 := by
    simpa [prefixWord, tailWord_3039113, baseEnd_3039113] using wordTrace_append hprefix tailTrace_3039113
  have hstable : (prefixWord ++ tailWord_3039113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039113).length < 2 ^ (prefixWord ++ tailWord_3039113).sum := by decide
  have hdescent : baseEnd_3039113 < baseStart_3039113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039130 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 3, 4]
def baseStart_3039130 : Nat := 118140960795 + 3039130 * 2 ^ 59
def prefixEnd_3039130 : Nat := 4983230072969 + 3 ^ 40 * 3039130 * 2
def baseEnd_3039130 : Nat := 1040356307665866415732201

theorem tailTrace_3039130 : CollatzResearch.WordTrace tailWord_3039130 prefixEnd_3039130 1040356307665866415732201 := by
  unfold tailWord_3039130
  simp only [CollatzResearch.WordTrace]
  refine ⟨27711544369939631731514711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73897451653172351284039229 27711544369939631731514711)
  ·
    refine ⟨41567316554909447597272067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27711544369939631731514711 41567316554909447597272067)
    ·
      refine ⟨62350974832364171395908101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41567316554909447597272067 62350974832364171395908101)
      ·
        refine ⟨11690807781068282136732769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62350974832364171395908101 11690807781068282136732769)
        ·
          refine ⟨8768105835801211602549577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11690807781068282136732769 8768105835801211602549577)
          ·
            refine ⟨6576079376850908701912183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8768105835801211602549577 6576079376850908701912183)
            ·
              refine ⟨9864119065276363052868275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6576079376850908701912183 9864119065276363052868275)
              ·
                refine ⟨14796178597914544579302413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9864119065276363052868275 14796178597914544579302413)
                ·
                  refine ⟨5548566974217954217238405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14796178597914544579302413 5548566974217954217238405)
                  ·
                    refine ⟨1040356307665866415732201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5548566974217954217238405 1040356307665866415732201)
                    ·
                      rfl

theorem cell22_3039130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_3039130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039130 prefixEnd_3039130 := by exact prefixLift 3039130
  have htrace : WordTrace (prefixWord ++ tailWord_3039130) baseStart_3039130 baseEnd_3039130 := by
    simpa [prefixWord, tailWord_3039130, baseEnd_3039130] using wordTrace_append hprefix tailTrace_3039130
  have hstable : (prefixWord ++ tailWord_3039130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039130).length < 2 ^ (prefixWord ++ tailWord_3039130).sum := by decide
  have hdescent : baseEnd_3039130 < baseStart_3039130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039280 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 6]
def baseStart_3039280 : Nat := 118140960795 + 3039280 * 2 ^ 59
def prefixEnd_3039280 : Nat := 4983230072969 + 3 ^ 40 * 3039280 * 2
def baseEnd_3039280 : Nat := 346802551910438674827247

theorem tailTrace_3039280 : CollatzResearch.WordTrace tailWord_3039280 prefixEnd_3039280 346802551910438674827247 := by
  unfold tailWord_3039280
  simp only [CollatzResearch.WordTrace]
  refine ⟨55425824214607551272009647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73901098952810068362679529 55425824214607551272009647)
  ·
    refine ⟨83138736321911326908014471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55425824214607551272009647 83138736321911326908014471)
    ·
      refine ⟨124708104482866990362021707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83138736321911326908014471 124708104482866990362021707)
      ·
        refine ⟨187062156724300485543032561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124708104482866990362021707 187062156724300485543032561)
        ·
          refine ⟨140296617543225364157274421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187062156724300485543032561 140296617543225364157274421)
          ·
            refine ⟨13152807894677377889744477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140296617543225364157274421 13152807894677377889744477)
            ·
              refine ⟨4932302960504016708654179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13152807894677377889744477 4932302960504016708654179)
              ·
                refine ⟨7398454440756025062981269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4932302960504016708654179 7398454440756025062981269)
                ·
                  refine ⟨346802551910438674827247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7398454440756025062981269 346802551910438674827247)
                  ·
                    rfl

theorem cell22_3039280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 6].length) (baseStart_3039280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039280 prefixEnd_3039280 := by exact prefixLift 3039280
  have htrace : WordTrace (prefixWord ++ tailWord_3039280) baseStart_3039280 baseEnd_3039280 := by
    simpa [prefixWord, tailWord_3039280, baseEnd_3039280] using wordTrace_append hprefix tailTrace_3039280
  have hstable : (prefixWord ++ tailWord_3039280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039280).length < 2 ^ (prefixWord ++ tailWord_3039280).sum := by decide
  have hdescent : baseEnd_3039280 < baseStart_3039280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039357 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 5, 3]
def baseStart_3039357 : Nat := 118140960795 + 3039357 * 2 ^ 59
def prefixEnd_3039357 : Nat := 4983230072969 + 3 ^ 40 * 3039357 * 2
def baseEnd_3039357 : Nat := 1040434014404913490306505

theorem tailTrace_3039357 : CollatzResearch.WordTrace tailWord_3039357 prefixEnd_3039357 1040434014404913490306505 := by
  unfold tailWord_3039357
  simp only [CollatzResearch.WordTrace]
  refine ⟨110854456849936144694572325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73902971233290763129714883 110854456849936144694572325)
  ·
    refine ⟨20785210659363027130232311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110854456849936144694572325 20785210659363027130232311)
    ·
      refine ⟨31177815989044540695348467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20785210659363027130232311 31177815989044540695348467)
      ·
        refine ⟨46766723983566811043022701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31177815989044540695348467 46766723983566811043022701)
        ·
          refine ⟨17537521493837554141133513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46766723983566811043022701 17537521493837554141133513)
          ·
            refine ⟨13153141120378165605850135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17537521493837554141133513 13153141120378165605850135)
            ·
              refine ⟨19729711680567248408775203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13153141120378165605850135 19729711680567248408775203)
              ·
                refine ⟨29594567520850872613162805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19729711680567248408775203 29594567520850872613162805)
                ·
                  refine ⟨2774490705079769307484013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29594567520850872613162805 2774490705079769307484013)
                  ·
                    refine ⟨1040434014404913490306505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2774490705079769307484013 1040434014404913490306505)
                    ·
                      rfl

theorem cell22_3039357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_3039357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039357 prefixEnd_3039357 := by exact prefixLift 3039357
  have htrace : WordTrace (prefixWord ++ tailWord_3039357) baseStart_3039357 baseEnd_3039357 := by
    simpa [prefixWord, tailWord_3039357, baseEnd_3039357] using wordTrace_append hprefix tailTrace_3039357
  have hstable : (prefixWord ++ tailWord_3039357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039357).length < 2 ^ (prefixWord ++ tailWord_3039357).sum := by decide
  have hdescent : baseEnd_3039357 < baseStart_3039357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039361 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 2, 4]
def baseStart_3039361 : Nat := 118140960795 + 3039361 * 2 ^ 59
def prefixEnd_3039361 : Nat := 4983230072969 + 3 ^ 40 * 3039361 * 2
def baseEnd_3039361 : Nat := 1040435383686658813206493

theorem tailTrace_3039361 : CollatzResearch.WordTrace tailWord_3039361 prefixEnd_3039361 1040435383686658813206493 := by
  unfold tailWord_3039361
  simp only [CollatzResearch.WordTrace]
  refine ⟨110854602741921653377717937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73903068494614435585145291 110854602741921653377717937)
  ·
    refine ⟨83140952056441240033288453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110854602741921653377717937 83140952056441240033288453)
    ·
      refine ⟨15588928510582732506241585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83140952056441240033288453 15588928510582732506241585)
      ·
        refine ⟨11691696382937049379681189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15588928510582732506241585 11691696382937049379681189)
        ·
          refine ⟨2192193071800696758690223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11691696382937049379681189 2192193071800696758690223)
          ·
            refine ⟨3288289607701045138035335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192193071800696758690223 3288289607701045138035335)
            ·
              refine ⟨4932434411551567707053003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288289607701045138035335 4932434411551567707053003)
              ·
                refine ⟨7398651617327351560579505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4932434411551567707053003 7398651617327351560579505)
                ·
                  refine ⟨5548988712995513670434629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7398651617327351560579505 5548988712995513670434629)
                  ·
                    refine ⟨1040435383686658813206493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5548988712995513670434629 1040435383686658813206493)
                    ·
                      rfl

theorem cell22_3039361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_3039361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039361 prefixEnd_3039361 := by exact prefixLift 3039361
  have htrace : WordTrace (prefixWord ++ tailWord_3039361) baseStart_3039361 baseEnd_3039361 := by
    simpa [prefixWord, tailWord_3039361, baseEnd_3039361] using wordTrace_append hprefix tailTrace_3039361
  have hstable : (prefixWord ++ tailWord_3039361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039361).length < 2 ^ (prefixWord ++ tailWord_3039361).sum := by decide
  have hdescent : baseEnd_3039361 < baseStart_3039361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039380 : List Nat := [2, 4, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_3039380 : Nat := 118140960795 + 3039380 * 2 ^ 59
def prefixEnd_3039380 : Nat := 4983230072969 + 3 ^ 40 * 3039380 * 2
def baseEnd_3039380 : Nat := 1040441887774949096981435

theorem tailTrace_3039380 : CollatzResearch.WordTrace tailWord_3039380 prefixEnd_3039380 1040441887774949096981435 := by
  unfold tailWord_3039380
  simp only [CollatzResearch.WordTrace]
  refine ⟨55427647864426409811329797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73903530485901879748439729 55427647864426409811329797)
  ·
    refine ⟨10392683974579951839624337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55427647864426409811329797 10392683974579951839624337)
    ·
      refine ⟨7794512980934963879718253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10392683974579951839624337 7794512980934963879718253)
      ·
        refine ⟨2922942367850611454894345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7794512980934963879718253 2922942367850611454894345)
        ·
          refine ⟨2192206775887958591170759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2922942367850611454894345 2192206775887958591170759)
          ·
            refine ⟨3288310163831937886756139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192206775887958591170759 3288310163831937886756139)
            ·
              refine ⟨4932465245747906830134209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288310163831937886756139 4932465245747906830134209)
              ·
                refine ⟨3699348934310930122600657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4932465245747906830134209 3699348934310930122600657)
                ·
                  refine ⟨2774511700733197591950493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3699348934310930122600657 2774511700733197591950493)
                  ·
                    refine ⟨1040441887774949096981435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2774511700733197591950493 1040441887774949096981435)
                    ·
                      rfl

theorem cell22_3039380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_3039380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039380 prefixEnd_3039380 := by exact prefixLift 3039380
  have htrace : WordTrace (prefixWord ++ tailWord_3039380) baseStart_3039380 baseEnd_3039380 := by
    simpa [prefixWord, tailWord_3039380, baseEnd_3039380] using wordTrace_append hprefix tailTrace_3039380
  have hstable : (prefixWord ++ tailWord_3039380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039380).length < 2 ^ (prefixWord ++ tailWord_3039380).sum := by decide
  have hdescent : baseEnd_3039380 < baseStart_3039380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039391 : List Nat := [1, 1, 2, 6, 1, 1, 2, 4, 1, 3]
def baseStart_3039391 : Nat := 118140960795 + 3039391 * 2 ^ 59
def prefixEnd_3039391 : Nat := 4983230072969 + 3 ^ 40 * 3039391 * 2
def baseEnd_3039391 : Nat := 1040445653299748734956401

theorem tailTrace_3039391 : CollatzResearch.WordTrace tailWord_3039391 prefixEnd_3039391 1040445653299748734956401 := by
  unfold tailWord_3039391
  simp only [CollatzResearch.WordTrace]
  refine ⟨110855696931812968501310027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73903797954541979000873351 110855696931812968501310027)
  ·
    refine ⟨166283545397719452751965041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110855696931812968501310027 166283545397719452751965041)
    ·
      refine ⟨124712659048289589563973781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166283545397719452751965041 124712659048289589563973781)
      ·
        refine ⟨5845905892888574510811271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 124712659048289589563973781 5845905892888574510811271)
        ·
          refine ⟨8768858839332861766216907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5845905892888574510811271 8768858839332861766216907)
          ·
            refine ⟨13153288258999292649325361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8768858839332861766216907 13153288258999292649325361)
            ·
              refine ⟨9864966194249469486994021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13153288258999292649325361 9864966194249469486994021)
              ·
                refine ⟨1849681161421775528811379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9864966194249469486994021 1849681161421775528811379)
                ·
                  refine ⟨2774521742132663293217069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849681161421775528811379 2774521742132663293217069)
                  ·
                    refine ⟨1040445653299748734956401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2774521742132663293217069 1040445653299748734956401)
                    ·
                      rfl

theorem cell22_3039391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 1, 3].length) (baseStart_3039391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039391 prefixEnd_3039391 := by exact prefixLift 3039391
  have htrace : WordTrace (prefixWord ++ tailWord_3039391) baseStart_3039391 baseEnd_3039391 := by
    simpa [prefixWord, tailWord_3039391, baseEnd_3039391] using wordTrace_append hprefix tailTrace_3039391
  have hstable : (prefixWord ++ tailWord_3039391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039391).length < 2 ^ (prefixWord ++ tailWord_3039391).sum := by decide
  have hdescent : baseEnd_3039391 < baseStart_3039391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039425 : List Nat := [1, 2, 6, 1, 2, 2, 1, 3, 1, 3]
def baseStart_3039425 : Nat := 118140960795 + 3039425 * 2 ^ 59
def prefixEnd_3039425 : Nat := 4983230072969 + 3 ^ 40 * 3039425 * 2
def baseEnd_3039425 : Nat := 1040457292194583979606297

theorem tailTrace_3039425 : CollatzResearch.WordTrace tailWord_3039425 prefixEnd_3039425 1040457292194583979606297 := by
  unfold tailWord_3039425
  simp only [CollatzResearch.WordTrace]
  refine ⟨110856937013689792308047729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73904624675793194872031819 110856937013689792308047729)
  ·
    refine ⟨83142702760267344231035797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110856937013689792308047729 83142702760267344231035797)
    ·
      refine ⟨3897314191887531760829803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83142702760267344231035797 3897314191887531760829803)
      ·
        refine ⟨5845971287831297641244705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3897314191887531760829803 5845971287831297641244705)
        ·
          refine ⟨4384478465873473230933529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5845971287831297641244705 4384478465873473230933529)
          ·
            refine ⟨3288358849405104923200147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4384478465873473230933529 3288358849405104923200147)
            ·
              refine ⟨4932538274107657384800221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288358849405104923200147 4932538274107657384800221)
              ·
                refine ⟨1849701852790371519300083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4932538274107657384800221 1849701852790371519300083)
                ·
                  refine ⟨2774552779185557278950125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849701852790371519300083 2774552779185557278950125)
                  ·
                    refine ⟨1040457292194583979606297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2774552779185557278950125 1040457292194583979606297)
                    ·
                      rfl

theorem cell22_3039425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_3039425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039425 prefixEnd_3039425 := by exact prefixLift 3039425
  have htrace : WordTrace (prefixWord ++ tailWord_3039425) baseStart_3039425 baseEnd_3039425 := by
    simpa [prefixWord, tailWord_3039425, baseEnd_3039425] using wordTrace_append hprefix tailTrace_3039425
  have hstable : (prefixWord ++ tailWord_3039425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039425).length < 2 ^ (prefixWord ++ tailWord_3039425).sum := by decide
  have hdescent : baseEnd_3039425 < baseStart_3039425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039552 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 5, 4]
def baseStart_3039552 : Nat := 118140960795 + 3039552 * 2 ^ 59
def prefixEnd_3039552 : Nat := 4983230072969 + 3 ^ 40 * 3039552 * 2
def baseEnd_3039552 : Nat := 1040500766889997981680907

theorem tailTrace_3039552 : CollatzResearch.WordTrace tailWord_3039552 prefixEnd_3039552 1040500766889997981680907 := by
  unfold tailWord_3039552
  simp only [CollatzResearch.WordTrace]
  refine ⟨55430784542114846498960455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73907712722819795331947273 55430784542114846498960455)
  ·
    refine ⟨83146176813172269748440683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55430784542114846498960455 83146176813172269748440683)
    ·
      refine ⟨124719265219758404622661025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83146176813172269748440683 124719265219758404622661025)
      ·
        refine ⟨93539448914818803466995769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124719265219758404622661025 93539448914818803466995769)
        ·
          refine ⟨70154586686114102600246827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93539448914818803466995769 70154586686114102600246827)
          ·
            refine ⟨105231880029171153900370241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70154586686114102600246827 105231880029171153900370241)
            ·
              refine ⟨78923910021878365425277681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105231880029171153900370241 78923910021878365425277681)
              ·
                refine ⟨59192932516408774068958261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78923910021878365425277681 59192932516408774068958261)
                ·
                  refine ⟨5549337423413322568964837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59192932516408774068958261 5549337423413322568964837)
                  ·
                    refine ⟨1040500766889997981680907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5549337423413322568964837 1040500766889997981680907)
                    ·
                      rfl

theorem cell22_3039552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_3039552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039552 prefixEnd_3039552 := by exact prefixLift 3039552
  have htrace : WordTrace (prefixWord ++ tailWord_3039552) baseStart_3039552 baseEnd_3039552 := by
    simpa [prefixWord, tailWord_3039552, baseEnd_3039552] using wordTrace_append hprefix tailTrace_3039552
  have hstable : (prefixWord ++ tailWord_3039552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039552).length < 2 ^ (prefixWord ++ tailWord_3039552).sum := by decide
  have hdescent : baseEnd_3039552 < baseStart_3039552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039556 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 7]
def baseStart_3039556 : Nat := 118140960795 + 3039556 * 2 ^ 59
def prefixEnd_3039556 : Nat := 4983230072969 + 3 ^ 40 * 3039556 * 2
def baseEnd_3039556 : Nat := 346834045390581101526965

theorem tailTrace_3039556 : CollatzResearch.WordTrace tailWord_3039556 prefixEnd_3039556 346834045390581101526965 := by
  unfold tailWord_3039556
  simp only [CollatzResearch.WordTrace]
  refine ⟨55430857488107600840533261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73907809984143467787377681 55430857488107600840533261)
  ·
    refine ⟨20786571558040350315199973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55430857488107600840533261 20786571558040350315199973)
    ·
      refine ⟨3897482167132565684099995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20786571558040350315199973 3897482167132565684099995)
      ·
        refine ⟨5846223250698848526149993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3897482167132565684099995 5846223250698848526149993)
        ·
          refine ⟨4384667438024136394612495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5846223250698848526149993 4384667438024136394612495)
          ·
            refine ⟨6577001157036204591918743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4384667438024136394612495 6577001157036204591918743)
            ·
              refine ⟨9865501735554306887878115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6577001157036204591918743 9865501735554306887878115)
              ·
                refine ⟨14798252603331460331817173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9865501735554306887878115 14798252603331460331817173)
                ·
                  refine ⟨346834045390581101526965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14798252603331460331817173 346834045390581101526965)
                  ·
                    rfl

theorem cell22_3039556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_3039556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039556 prefixEnd_3039556 := by exact prefixLift 3039556
  have htrace : WordTrace (prefixWord ++ tailWord_3039556) baseStart_3039556 baseEnd_3039556 := by
    simpa [prefixWord, tailWord_3039556, baseEnd_3039556] using wordTrace_append hprefix tailTrace_3039556
  have hstable : (prefixWord ++ tailWord_3039556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039556).length < 2 ^ (prefixWord ++ tailWord_3039556).sum := by decide
  have hdescent : baseEnd_3039556 < baseStart_3039556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039586 : List Nat := [3, 3, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3039586 : Nat := 118140960795 + 3039586 * 2 ^ 59
def prefixEnd_3039586 : Nat := 4983230072969 + 3 ^ 40 * 3039586 * 2
def baseEnd_3039586 : Nat := 1040512405784833226330803

theorem tailTrace_3039586 : CollatzResearch.WordTrace tailWord_3039586 prefixEnd_3039586 1040512405784833226330803 := by
  unfold tailWord_3039586
  simp only [CollatzResearch.WordTrace]
  refine ⟨27715702291526629201164653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73908539444071011203105741 27715702291526629201164653)
  ·
    refine ⟨10393388359322485950436745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27715702291526629201164653 10393388359322485950436745)
    ·
      refine ⟨7795041269491864462827559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10393388359322485950436745 7795041269491864462827559)
      ·
        refine ⟨11692561904237796694241339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7795041269491864462827559 11692561904237796694241339)
        ·
          refine ⟨17538842856356695041362009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11692561904237796694241339 17538842856356695041362009)
          ·
            refine ⟨13154132142267521281021507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17538842856356695041362009 13154132142267521281021507)
            ·
              refine ⟨19731198213401281921532261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13154132142267521281021507 19731198213401281921532261)
              ·
                refine ⟨3699599665012740360287299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19731198213401281921532261 3699599665012740360287299)
                ·
                  refine ⟨5549399497519110540430949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3699599665012740360287299 5549399497519110540430949)
                  ·
                    refine ⟨1040512405784833226330803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5549399497519110540430949 1040512405784833226330803)
                    ·
                      rfl

theorem cell22_3039586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3039586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039586 prefixEnd_3039586 := by exact prefixLift 3039586
  have htrace : WordTrace (prefixWord ++ tailWord_3039586) baseStart_3039586 baseEnd_3039586 := by
    simpa [prefixWord, tailWord_3039586, baseEnd_3039586] using wordTrace_append hprefix tailTrace_3039586
  have hstable : (prefixWord ++ tailWord_3039586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039586).length < 2 ^ (prefixWord ++ tailWord_3039586).sum := by decide
  have hdescent : baseEnd_3039586 < baseStart_3039586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039646 : List Nat := [4, 3, 1, 2, 1, 1, 2, 8]
def baseStart_3039646 : Nat := 118140960795 + 3039646 * 2 ^ 59
def prefixEnd_3039646 : Nat := 4983230072969 + 3 ^ 40 * 3039646 * 2
def baseEnd_3039646 : Nat := 115614771667890341092291

theorem tailTrace_3039646 : CollatzResearch.WordTrace tailWord_3039646 prefixEnd_3039646 115614771667890341092291 := by
  unfold tailWord_3039646
  simp only [CollatzResearch.WordTrace]
  refine ⟨13858124693236143381480349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73909998363926098034561861 13858124693236143381480349)
  ·
    refine ⟨5196796759963553768055131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13858124693236143381480349 5196796759963553768055131)
    ·
      refine ⟨7795195139945330652082697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5196796759963553768055131 7795195139945330652082697)
      ·
        refine ⟨5846396354958997989062023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7795195139945330652082697 5846396354958997989062023)
        ·
          refine ⟨8769594532438496983593035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5846396354958997989062023 8769594532438496983593035)
          ·
            refine ⟨13154391798657745475389553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8769594532438496983593035 13154391798657745475389553)
            ·
              refine ⟨9865793848993309106542165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13154391798657745475389553 9865793848993309106542165)
              ·
                refine ⟨115614771667890341092291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9865793848993309106542165 115614771667890341092291)
                ·
                  rfl

theorem cell22_3039646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_3039646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039646 prefixEnd_3039646 := by exact prefixLift 3039646
  have htrace : WordTrace (prefixWord ++ tailWord_3039646) baseStart_3039646 baseEnd_3039646 := by
    simpa [prefixWord, tailWord_3039646, baseEnd_3039646] using wordTrace_append hprefix tailTrace_3039646
  have hstable : (prefixWord ++ tailWord_3039646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039646).length < 2 ^ (prefixWord ++ tailWord_3039646).sum := by decide
  have hdescent : baseEnd_3039646 < baseStart_3039646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039657 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 9]
def baseStart_3039657 : Nat := 118140960795 + 3039657 * 2 ^ 59
def prefixEnd_3039657 : Nat := 4983230072969 + 3 ^ 40 * 3039657 * 2
def baseEnd_3039657 : Nat := 346845570178604235935195

theorem tailTrace_3039657 : CollatzResearch.WordTrace tailWord_3039657 prefixEnd_3039657 346845570178604235935195 := by
  unfold tailWord_3039657
  simp only [CollatzResearch.WordTrace]
  refine ⟨110865398748849295930493225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73910265832566197286995483 110865398748849295930493225)
  ·
    refine ⟨83149049061636971947869919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110865398748849295930493225 83149049061636971947869919)
    ·
      refine ⟨124723573592455457921804879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83149049061636971947869919 124723573592455457921804879)
      ·
        refine ⟨187085360388683186882707319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124723573592455457921804879 187085360388683186882707319)
        ·
          refine ⟨280628040583024780324060979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187085360388683186882707319 280628040583024780324060979)
          ·
            refine ⟨420942060874537170486091469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280628040583024780324060979 420942060874537170486091469)
            ·
              refine ⟨157853272827951438932284301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 420942060874537170486091469 157853272827951438932284301)
              ·
                refine ⟨59194977310481789599606613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157853272827951438932284301 59194977310481789599606613)
                ·
                  refine ⟨346845570178604235935195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59194977310481789599606613 346845570178604235935195)
                  ·
                    rfl

theorem cell22_3039657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 9].length) (baseStart_3039657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039657 prefixEnd_3039657 := by exact prefixLift 3039657
  have htrace : WordTrace (prefixWord ++ tailWord_3039657) baseStart_3039657 baseEnd_3039657 := by
    simpa [prefixWord, tailWord_3039657, baseEnd_3039657] using wordTrace_append hprefix tailTrace_3039657
  have hstable : (prefixWord ++ tailWord_3039657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039657).length < 2 ^ (prefixWord ++ tailWord_3039657).sum := by decide
  have hdescent : baseEnd_3039657 < baseStart_3039657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039719 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 8]
def baseStart_3039719 : Nat := 118140960795 + 3039719 * 2 ^ 59
def prefixEnd_3039719 : Nat := 4983230072969 + 3 ^ 40 * 3039719 * 2
def baseEnd_3039719 : Nat := 346852644800955070918465

theorem tailTrace_3039719 : CollatzResearch.WordTrace tailWord_3039719 prefixEnd_3039719 346852644800955070918465 := by
  unfold tailWord_3039719
  simp only [CollatzResearch.WordTrace]
  refine ⟨110867660074624680519250211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73911773383083120346166807 110867660074624680519250211)
  ·
    refine ⟨166301490111937020778875317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110867660074624680519250211 166301490111937020778875317)
    ·
      refine ⟨15590764697994095698019561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166301490111937020778875317 15590764697994095698019561)
      ·
        refine ⟨11693073523495571773514671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15590764697994095698019561 11693073523495571773514671)
        ·
          refine ⟨17539610285243357660272007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11693073523495571773514671 17539610285243357660272007)
          ·
            refine ⟨26309415427865036490408011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17539610285243357660272007 26309415427865036490408011)
            ·
              refine ⟨39464123141797554735612017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26309415427865036490408011 39464123141797554735612017)
              ·
                refine ⟨29598092356348166051709013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39464123141797554735612017 29598092356348166051709013)
                ·
                  refine ⟨346852644800955070918465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29598092356348166051709013 346852644800955070918465)
                  ·
                    rfl

theorem cell22_3039719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 8].length) (baseStart_3039719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039719 prefixEnd_3039719 := by exact prefixLift 3039719
  have htrace : WordTrace (prefixWord ++ tailWord_3039719) baseStart_3039719 baseEnd_3039719 := by
    simpa [prefixWord, tailWord_3039719, baseEnd_3039719] using wordTrace_append hprefix tailTrace_3039719
  have hstable : (prefixWord ++ tailWord_3039719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039719).length < 2 ^ (prefixWord ++ tailWord_3039719).sum := by decide
  have hdescent : baseEnd_3039719 < baseStart_3039719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039736 : List Nat := [2, 1, 2, 1, 1, 4, 1, 6, 4]
def baseStart_3039736 : Nat := 118140960795 + 3039736 * 2 ^ 59
def prefixEnd_3039736 : Nat := 4983230072969 + 3 ^ 40 * 3039736 * 2
def baseEnd_3039736 : Nat := 346854584616760945026781

theorem tailTrace_3039736 : CollatzResearch.WordTrace tailWord_3039736 prefixEnd_3039736 346854584616760945026781 := by
  unfold tailWord_3039736
  simp only [CollatzResearch.WordTrace]
  refine ⟨55434140057781546211309531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73912186743708728281746041 55434140057781546211309531)
  ·
    refine ⟨83151210086672319316964297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55434140057781546211309531 83151210086672319316964297)
    ·
      refine ⟨62363407565004239487723223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83151210086672319316964297 62363407565004239487723223)
      ·
        refine ⟨93545111347506359231584835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62363407565004239487723223 93545111347506359231584835)
        ·
          refine ⟨140317667021259538847377253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93545111347506359231584835 140317667021259538847377253)
          ·
            refine ⟨26309562566486163533883235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140317667021259538847377253 26309562566486163533883235)
            ·
              refine ⟨39464343849729245300824853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26309562566486163533883235 39464343849729245300824853)
              ·
                refine ⟨1849891117956058373476165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39464343849729245300824853 1849891117956058373476165)
                ·
                  refine ⟨346854584616760945026781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1849891117956058373476165 346854584616760945026781)
                  ·
                    rfl

theorem cell22_3039736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 4].length) (baseStart_3039736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039736 prefixEnd_3039736 := by exact prefixLift 3039736
  have htrace : WordTrace (prefixWord ++ tailWord_3039736) baseStart_3039736 baseEnd_3039736 := by
    simpa [prefixWord, tailWord_3039736, baseEnd_3039736] using wordTrace_append hprefix tailTrace_3039736
  have hstable : (prefixWord ++ tailWord_3039736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039736).length < 2 ^ (prefixWord ++ tailWord_3039736).sum := by decide
  have hdescent : baseEnd_3039736 < baseStart_3039736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039749 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 1, 6]
def baseStart_3039749 : Nat := 118140960795 + 3039749 * 2 ^ 59
def prefixEnd_3039749 : Nat := 4983230072969 + 3 ^ 40 * 3039749 * 2
def baseEnd_3039749 : Nat := 1040568204015955134505303

theorem tailTrace_3039749 : CollatzResearch.WordTrace tailWord_3039749 prefixEnd_3039749 1040568204015955134505303 := by
  unfold tailWord_3039749
  simp only [CollatzResearch.WordTrace]
  refine ⟨110868754264515995642842301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73912502843010663761894867 110868754264515995642842301)
  ·
    refine ⟨41575782849193498366065863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110868754264515995642842301 41575782849193498366065863)
    ·
      refine ⟨62363674273790247549098795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41575782849193498366065863 62363674273790247549098795)
      ·
        refine ⟨93545511410685371323648193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62363674273790247549098795 93545511410685371323648193)
        ·
          refine ⟨70159133558014028492736145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93545511410685371323648193 70159133558014028492736145)
          ·
            refine ⟨52619350168510521369552109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70159133558014028492736145 52619350168510521369552109)
            ·
              refine ⟨19732256313191445513582041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52619350168510521369552109 19732256313191445513582041)
              ·
                refine ⟨14799192234893584135186531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19732256313191445513582041 14799192234893584135186531)
                ·
                  refine ⟨22198788352340376202779797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14799192234893584135186531 22198788352340376202779797)
                  ·
                    refine ⟨1040568204015955134505303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22198788352340376202779797 1040568204015955134505303)
                    ·
                      rfl

theorem cell22_3039749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_3039749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039749 prefixEnd_3039749 := by exact prefixLift 3039749
  have htrace : WordTrace (prefixWord ++ tailWord_3039749) baseStart_3039749 baseEnd_3039749 := by
    simpa [prefixWord, tailWord_3039749, baseEnd_3039749] using wordTrace_append hprefix tailTrace_3039749
  have hstable : (prefixWord ++ tailWord_3039749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039749).length < 2 ^ (prefixWord ++ tailWord_3039749).sum := by decide
  have hdescent : baseEnd_3039749 < baseStart_3039749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039798 : List Nat := [5, 1, 2, 1, 2, 2, 2, 7]
def baseStart_3039798 : Nat := 118140960795 + 3039798 * 2 ^ 59
def prefixEnd_3039798 : Nat := 4983230072969 + 3 ^ 40 * 3039798 * 2
def baseEnd_3039798 : Nat := 115620553079703926670017

theorem tailTrace_3039798 : CollatzResearch.WordTrace tailWord_3039798 prefixEnd_3039798 115620553079703926670017 := by
  unfold tailWord_3039798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6929408840083654813211003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73913694294225651340917365 6929408840083654813211003)
  ·
    refine ⟨10394113260125482219816505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6929408840083654813211003 10394113260125482219816505)
    ·
      refine ⟨7795584945094111664862379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10394113260125482219816505 7795584945094111664862379)
      ·
        refine ⟨11693377417641167497293569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7795584945094111664862379 11693377417641167497293569)
        ·
          refine ⟨8770033063230875622970177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11693377417641167497293569 8770033063230875622970177)
          ·
            refine ⟨6577524797423156717227633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8770033063230875622970177 6577524797423156717227633)
            ·
              refine ⟨4933143598067367537920725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6577524797423156717227633 4933143598067367537920725)
              ·
                refine ⟨115620553079703926670017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4933143598067367537920725 115620553079703926670017)
                ·
                  rfl

theorem cell22_3039798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_3039798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039798 prefixEnd_3039798 := by exact prefixLift 3039798
  have htrace : WordTrace (prefixWord ++ tailWord_3039798) baseStart_3039798 baseEnd_3039798 := by
    simpa [prefixWord, tailWord_3039798, baseEnd_3039798] using wordTrace_append hprefix tailTrace_3039798
  have hstable : (prefixWord ++ tailWord_3039798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039798).length < 2 ^ (prefixWord ++ tailWord_3039798).sum := by decide
  have hdescent : baseEnd_3039798 < baseStart_3039798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039824 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 3, 7]
def baseStart_3039824 : Nat := 118140960795 + 3039824 * 2 ^ 59
def prefixEnd_3039824 : Nat := 4983230072969 + 3 ^ 40 * 3039824 * 2
def baseEnd_3039824 : Nat := 1040593878048679938880073

theorem tailTrace_3039824 : CollatzResearch.WordTrace tailWord_3039824 prefixEnd_3039824 1040593878048679938880073 := by
  unfold tailWord_3039824
  simp only [CollatzResearch.WordTrace]
  refine ⟨55435744869622141725911263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73914326492829522301215017 55435744869622141725911263)
  ·
    refine ⟨83153617304433212588866895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55435744869622141725911263 83153617304433212588866895)
    ·
      refine ⟨124730425956649818883300343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83153617304433212588866895 124730425956649818883300343)
      ·
        refine ⟨187095638934974728324950515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124730425956649818883300343 187095638934974728324950515)
        ·
          refine ⟨280643458402462092487425773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187095638934974728324950515 280643458402462092487425773)
          ·
            refine ⟨105241296900923284682784665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280643458402462092487425773 105241296900923284682784665)
            ·
              refine ⟨78930972675692463512088499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105241296900923284682784665 78930972675692463512088499)
              ·
                refine ⟨118396459013538695268132749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78930972675692463512088499 118396459013538695268132749)
                ·
                  refine ⟨44398672130077010725549781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118396459013538695268132749 44398672130077010725549781)
                  ·
                    refine ⟨1040593878048679938880073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44398672130077010725549781 1040593878048679938880073)
                    ·
                      rfl

theorem cell22_3039824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_3039824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039824 prefixEnd_3039824 := by exact prefixLift 3039824
  have htrace : WordTrace (prefixWord ++ tailWord_3039824) baseStart_3039824 baseEnd_3039824 := by
    simpa [prefixWord, tailWord_3039824, baseEnd_3039824] using wordTrace_append hprefix tailTrace_3039824
  have hstable : (prefixWord ++ tailWord_3039824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039824).length < 2 ^ (prefixWord ++ tailWord_3039824).sum := by decide
  have hdescent : baseEnd_3039824 < baseStart_3039824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039838 : List Nat := [4, 4, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3039838 : Nat := 118140960795 + 3039838 * 2 ^ 59
def prefixEnd_3039838 : Nat := 4983230072969 + 3 ^ 40 * 3039838 * 2
def baseEnd_3039838 : Nat := 346866223511596189676677

theorem tailTrace_3039838 : CollatzResearch.WordTrace tailWord_3039838 prefixEnd_3039838 346866223511596189676677 := by
  unfold tailWord_3039838
  simp only [CollatzResearch.WordTrace]
  refine ⟨13859000045149195480354021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73914666907462375895221445 13859000045149195480354021)
  ·
    refine ⟨2598562508465474152566379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13859000045149195480354021 2598562508465474152566379)
    ·
      refine ⟨3897843762698211228849569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2598562508465474152566379 3897843762698211228849569)
      ·
        refine ⟨2923382822023658421637177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3897843762698211228849569 2923382822023658421637177)
        ·
          refine ⟨2192537116517743816227883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2923382822023658421637177 2192537116517743816227883)
          ·
            refine ⟨3288805674776615724341825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192537116517743816227883 3288805674776615724341825)
            ·
              refine ⟨2466604256082461793256369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3288805674776615724341825 2466604256082461793256369)
              ·
                refine ⟨1849953192061846344942277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2466604256082461793256369 1849953192061846344942277)
                ·
                  refine ⟨346866223511596189676677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1849953192061846344942277 346866223511596189676677)
                  ·
                    rfl

theorem cell22_3039838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3039838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039838 prefixEnd_3039838 := by exact prefixLift 3039838
  have htrace : WordTrace (prefixWord ++ tailWord_3039838) baseStart_3039838 baseEnd_3039838 := by
    simpa [prefixWord, tailWord_3039838, baseEnd_3039838] using wordTrace_append hprefix tailTrace_3039838
  have hstable : (prefixWord ++ tailWord_3039838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039838).length < 2 ^ (prefixWord ++ tailWord_3039838).sum := by decide
  have hdescent : baseEnd_3039838 < baseStart_3039838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039858 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_3039858 : Nat := 118140960795 + 3039858 * 2 ^ 59
def prefixEnd_3039858 : Nat := 4983230072969 + 3 ^ 40 * 3039858 * 2
def baseEnd_3039858 : Nat := 1040605516943515183529969

theorem tailTrace_3039858 : CollatzResearch.WordTrace tailWord_3039858 prefixEnd_3039858 1040605516943515183529969 := by
  unfold tailWord_3039858
  simp only [CollatzResearch.WordTrace]
  refine ⟨27718182455280276814640057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73915153214080738172373485 27718182455280276814640057)
  ·
    refine ⟨20788636841460207610980043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27718182455280276814640057 20788636841460207610980043)
    ·
      refine ⟨31182955262190311416470065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20788636841460207610980043 31182955262190311416470065)
      ·
        refine ⟨23387216446642733562352549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31182955262190311416470065 23387216446642733562352549)
        ·
          refine ⟨4385103083745512542941103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23387216446642733562352549 4385103083745512542941103)
          ·
            refine ⟨6577654625618268814411655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4385103083745512542941103 6577654625618268814411655)
            ·
              refine ⟨9866481938427403221617483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6577654625618268814411655 9866481938427403221617483)
              ·
                refine ⟨14799722907641104832426225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9866481938427403221617483 14799722907641104832426225)
                ·
                  refine ⟨11099792180730828624319669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14799722907641104832426225 11099792180730828624319669)
                  ·
                    refine ⟨1040605516943515183529969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11099792180730828624319669 1040605516943515183529969)
                    ·
                      rfl

theorem cell22_3039858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_3039858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039858 prefixEnd_3039858 := by exact prefixLift 3039858
  have htrace : WordTrace (prefixWord ++ tailWord_3039858) baseStart_3039858 baseEnd_3039858 := by
    simpa [prefixWord, tailWord_3039858, baseEnd_3039858] using wordTrace_append hprefix tailTrace_3039858
  have hstable : (prefixWord ++ tailWord_3039858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039858).length < 2 ^ (prefixWord ++ tailWord_3039858).sum := by decide
  have hdescent : baseEnd_3039858 < baseStart_3039858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039873 : List Nat := [1, 2, 4, 2, 1, 1, 2, 4, 1, 4]
def baseStart_3039873 : Nat := 118140960795 + 3039873 * 2 ^ 59
def prefixEnd_3039873 : Nat := 4983230072969 + 3 ^ 40 * 3039873 * 2
def baseEnd_3039873 : Nat := 1040610651750060144404923

theorem tailTrace_3039873 : CollatzResearch.WordTrace tailWord_3039873 prefixEnd_3039873 1040610651750060144404923 := by
  unfold tailWord_3039873
  simp only [CollatzResearch.WordTrace]
  refine ⟨110873276916066764820356273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73915517944044509880237515 110873276916066764820356273)
  ·
    refine ⟨83154957687050073615267205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110873276916066764820356273 83154957687050073615267205)
    ·
      refine ⟨15591554566321888802862601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83154957687050073615267205 15591554566321888802862601)
      ·
        refine ⟨11693665924741416602146951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15591554566321888802862601 11693665924741416602146951)
        ·
          refine ⟨17540498887112124903220427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11693665924741416602146951 17540498887112124903220427)
          ·
            refine ⟨26310748330668187354830641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17540498887112124903220427 26310748330668187354830641)
            ·
              refine ⟨19733061248001140516122981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26310748330668187354830641 19733061248001140516122981)
              ·
                refine ⟨3699948984000213846773059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19733061248001140516122981 3699948984000213846773059)
                ·
                  refine ⟨5549923476000320770159589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3699948984000213846773059 5549923476000320770159589)
                  ·
                    refine ⟨1040610651750060144404923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5549923476000320770159589 1040610651750060144404923)
                    ·
                      rfl

theorem cell22_3039873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_3039873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039873 prefixEnd_3039873 := by exact prefixLift 3039873
  have htrace : WordTrace (prefixWord ++ tailWord_3039873) baseStart_3039873 baseEnd_3039873 := by
    simpa [prefixWord, tailWord_3039873, baseEnd_3039873] using wordTrace_append hprefix tailTrace_3039873
  have hstable : (prefixWord ++ tailWord_3039873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039873).length < 2 ^ (prefixWord ++ tailWord_3039873).sum := by decide
  have hdescent : baseEnd_3039873 < baseStart_3039873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039890 : List Nat := [3, 2, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3039890 : Nat := 118140960795 + 3039890 * 2 ^ 59
def prefixEnd_3039890 : Nat := 4983230072969 + 3 ^ 40 * 3039890 * 2
def baseEnd_3039890 : Nat := 1040616471197477766729871

theorem tailTrace_3039890 : CollatzResearch.WordTrace tailWord_3039890 prefixEnd_3039890 1040616471197477766729871 := by
  unfold tailWord_3039890
  simp only [CollatzResearch.WordTrace]
  refine ⟨27718474239251294180931281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73915931304670117815816749 27718474239251294180931281)
  ·
    refine ⟨20788855679438470635698461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27718474239251294180931281 20788855679438470635698461)
    ·
      refine ⟨7795820879789426488386923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20788855679438470635698461 7795820879789426488386923)
      ·
        refine ⟨11693731319684139732580385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7795820879789426488386923 11693731319684139732580385)
        ·
          refine ⟨8770298489763104799435289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11693731319684139732580385 8770298489763104799435289)
          ·
            refine ⟨6577723867322328599576467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8770298489763104799435289 6577723867322328599576467)
            ·
              refine ⟨9866585800983492899364701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6577723867322328599576467 9866585800983492899364701)
              ·
                refine ⟨3699969675368809837261763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9866585800983492899364701 3699969675368809837261763)
                ·
                  refine ⟨5549954513053214755892645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3699969675368809837261763 5549954513053214755892645)
                  ·
                    refine ⟨1040616471197477766729871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5549954513053214755892645 1040616471197477766729871)
                    ·
                      rfl

theorem cell22_3039890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3039890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039890 prefixEnd_3039890 := by exact prefixLift 3039890
  have htrace : WordTrace (prefixWord ++ tailWord_3039890) baseStart_3039890 baseEnd_3039890 := by
    simpa [prefixWord, tailWord_3039890, baseEnd_3039890] using wordTrace_append hprefix tailTrace_3039890
  have hstable : (prefixWord ++ tailWord_3039890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039890).length < 2 ^ (prefixWord ++ tailWord_3039890).sum := by decide
  have hdescent : baseEnd_3039890 < baseStart_3039890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039933 : List Nat := [1, 4, 1, 2, 1, 3, 4, 6]
def baseStart_3039933 : Nat := 118140960795 + 3039933 * 2 ^ 59
def prefixEnd_3039933 : Nat := 4983230072969 + 3 ^ 40 * 3039933 * 2
def baseEnd_3039933 : Nat := 115625687886248887544971

theorem tailTrace_3039933 : CollatzResearch.WordTrace tailWord_3039933 prefixEnd_3039933 115625687886248887544971 := by
  unfold tailWord_3039933
  simp only [CollatzResearch.WordTrace]
  refine ⟨110875465295849395067540453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73916976863899596711693635 110875465295849395067540453)
  ·
    refine ⟨20789149742971761575163835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110875465295849395067540453 20789149742971761575163835)
    ·
      refine ⟨31183724614457642362745753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20789149742971761575163835 31183724614457642362745753)
      ·
        refine ⟨23387793460843231772059315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31183724614457642362745753 23387793460843231772059315)
        ·
          refine ⟨35081690191264847658088973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23387793460843231772059315 35081690191264847658088973)
          ·
            refine ⟨13155633821724317871783365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35081690191264847658088973 13155633821724317871783365)
            ·
              refine ⟨2466681341573309600959381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13155633821724317871783365 2466681341573309600959381)
              ·
                refine ⟨115625687886248887544971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2466681341573309600959381 115625687886248887544971)
                ·
                  rfl

theorem cell22_3039933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 6].length) (baseStart_3039933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039933 prefixEnd_3039933 := by exact prefixLift 3039933
  have htrace : WordTrace (prefixWord ++ tailWord_3039933) baseStart_3039933 baseEnd_3039933 := by
    simpa [prefixWord, tailWord_3039933, baseEnd_3039933] using wordTrace_append hprefix tailTrace_3039933
  have hstable : (prefixWord ++ tailWord_3039933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039933).length < 2 ^ (prefixWord ++ tailWord_3039933).sum := by decide
  have hdescent : baseEnd_3039933 < baseStart_3039933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039961 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 7]
def baseStart_3039961 : Nat := 118140960795 + 3039961 * 2 ^ 59
def prefixEnd_3039961 : Nat := 4983230072969 + 3 ^ 40 * 3039961 * 2
def baseEnd_3039961 : Nat := 346880258649485749401551

theorem tailTrace_3039961 : CollatzResearch.WordTrace tailWord_3039961 prefixEnd_3039961 346880258649485749401551 := by
  unfold tailWord_3039961
  simp only [CollatzResearch.WordTrace]
  refine ⟨110876486539747955849559737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73917657693165303899706491 110876486539747955849559737)
  ·
    refine ⟨83157364904810966887169803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110876486539747955849559737 83157364904810966887169803)
    ·
      refine ⟨124736047357216450330754705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83157364904810966887169803 124736047357216450330754705)
      ·
        refine ⟨93552035517912337748066029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124736047357216450330754705 93552035517912337748066029)
        ·
          refine ⟨35082013319217126655524761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93552035517912337748066029 35082013319217126655524761)
          ·
            refine ⟨26311509989412844991643571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35082013319217126655524761 26311509989412844991643571)
            ·
              refine ⟨39467264984119267487465357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26311509989412844991643571 39467264984119267487465357)
              ·
                refine ⟨14800224369044725307799509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39467264984119267487465357 14800224369044725307799509)
                ·
                  refine ⟨346880258649485749401551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14800224369044725307799509 346880258649485749401551)
                  ·
                    rfl

theorem cell22_3039961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 7].length) (baseStart_3039961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3039961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3039961 prefixEnd_3039961 := by exact prefixLift 3039961
  have htrace : WordTrace (prefixWord ++ tailWord_3039961) baseStart_3039961 baseEnd_3039961 := by
    simpa [prefixWord, tailWord_3039961, baseEnd_3039961] using wordTrace_append hprefix tailTrace_3039961
  have hstable : (prefixWord ++ tailWord_3039961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039961).length < 2 ^ (prefixWord ++ tailWord_3039961).sum := by decide
  have hdescent : baseEnd_3039961 < baseStart_3039961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040113 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 7]
def baseStart_3040113 : Nat := 118140960795 + 3040113 * 2 ^ 59
def prefixEnd_3040113 : Nat := 4983230072969 + 3 ^ 40 * 3040113 * 2
def baseEnd_3040113 : Nat := 346897602884926506134729

theorem tailTrace_3040113 : CollatzResearch.WordTrace tailWord_3040113 prefixEnd_3040113 346897602884926506134729 := by
  unfold tailWord_3040113
  simp only [CollatzResearch.WordTrace]
  refine ⟨110882030435197285809092993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73921353623464857206061995 110882030435197285809092993)
  ·
    refine ⟨83161522826397964356819745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110882030435197285809092993 83161522826397964356819745)
    ·
      refine ⟨62371142119798473267614809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83161522826397964356819745 62371142119798473267614809)
      ·
        refine ⟨46778356589848854950711107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62371142119798473267614809 46778356589848854950711107)
        ·
          refine ⟨70167534884773282426066661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46778356589848854950711107 70167534884773282426066661)
          ·
            refine ⟨13156412790894990454887499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70167534884773282426066661 13156412790894990454887499)
            ·
              refine ⟨19734619186342485682331249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13156412790894990454887499 19734619186342485682331249)
              ·
                refine ⟨14800964389756864261748437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19734619186342485682331249 14800964389756864261748437)
                ·
                  refine ⟨346897602884926506134729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14800964389756864261748437 346897602884926506134729)
                  ·
                    rfl

theorem cell22_3040113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 7].length) (baseStart_3040113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040113 prefixEnd_3040113 := by exact prefixLift 3040113
  have htrace : WordTrace (prefixWord ++ tailWord_3040113) baseStart_3040113 baseEnd_3040113 := by
    simpa [prefixWord, tailWord_3040113, baseEnd_3040113] using wordTrace_append hprefix tailTrace_3040113
  have hstable : (prefixWord ++ tailWord_3040113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040113).length < 2 ^ (prefixWord ++ tailWord_3040113).sum := by decide
  have hdescent : baseEnd_3040113 < baseStart_3040113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040128 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 2, 5]
def baseStart_3040128 : Nat := 118140960795 + 3040128 * 2 ^ 59
def prefixEnd_3040128 : Nat := 4983230072969 + 3 ^ 40 * 3040128 * 2
def baseEnd_3040128 : Nat := 1040697943461324479279141

theorem tailTrace_3040128 : CollatzResearch.WordTrace tailWord_3040128 prefixEnd_3040128 1040697943461324479279141 := by
  unfold tailWord_3040128
  simp only [CollatzResearch.WordTrace]
  refine ⟨55441288765071471685444519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73921718353428628913926025 55441288765071471685444519)
  ·
    refine ⟨83161933147607207528166779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55441288765071471685444519 83161933147607207528166779)
    ·
      refine ⟨124742899721410811292250169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83161933147607207528166779 124742899721410811292250169)
      ·
        refine ⟨93557174791058108469187627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124742899721410811292250169 93557174791058108469187627)
        ·
          refine ⟨140335762186587162703781441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93557174791058108469187627 140335762186587162703781441)
          ·
            refine ⟨105251821639940372027836081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140335762186587162703781441 105251821639940372027836081)
            ·
              refine ⟨78938866229955279020877061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105251821639940372027836081 78938866229955279020877061)
              ·
                refine ⟨14801037418116614816414449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78938866229955279020877061 14801037418116614816414449)
                ·
                  refine ⟨11100778063587461112310837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14801037418116614816414449 11100778063587461112310837)
                  ·
                    refine ⟨1040697943461324479279141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11100778063587461112310837 1040697943461324479279141)
                    ·
                      rfl

theorem cell22_3040128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_3040128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040128 prefixEnd_3040128 := by exact prefixLift 3040128
  have htrace : WordTrace (prefixWord ++ tailWord_3040128) baseStart_3040128 baseEnd_3040128 := by
    simpa [prefixWord, tailWord_3040128, baseEnd_3040128] using wordTrace_append hprefix tailTrace_3040128
  have hstable : (prefixWord ++ tailWord_3040128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040128).length < 2 ^ (prefixWord ++ tailWord_3040128).sum := by decide
  have hdescent : baseEnd_3040128 < baseStart_3040128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040190 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_3040190 : Nat := 118140960795 + 3040190 * 2 ^ 59
def prefixEnd_3040190 : Nat := 4983230072969 + 3 ^ 40 * 3040190 * 2
def baseEnd_3040190 : Nat := 1040719167328376984228951

theorem tailTrace_3040190 : CollatzResearch.WordTrace tailWord_3040190 prefixEnd_3040190 1040719167328376984228951 := by
  unfold tailWord_3040190
  simp only [CollatzResearch.WordTrace]
  refine ⟨13860604856989790994955753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73923225903945551973097349 13860604856989790994955753)
  ·
    refine ⟨10395453642742343246216815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13860604856989790994955753 10395453642742343246216815)
    ·
      refine ⟨15593180464113514869325223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10395453642742343246216815 15593180464113514869325223)
      ·
        refine ⟨23389770696170272303987835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15593180464113514869325223 23389770696170272303987835)
        ·
          refine ⟨35084656044255408455981753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23389770696170272303987835 35084656044255408455981753)
          ·
            refine ⟨26313492033191556341986315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35084656044255408455981753 26313492033191556341986315)
            ·
              refine ⟨39470238049787334512979473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26313492033191556341986315 39470238049787334512979473)
              ·
                refine ⟨29602678537340500884734605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39470238049787334512979473 29602678537340500884734605)
                ·
                  refine ⟨11101004451502687831775477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29602678537340500884734605 11101004451502687831775477)
                  ·
                    refine ⟨1040719167328376984228951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11101004451502687831775477 1040719167328376984228951)
                    ·
                      rfl

theorem cell22_3040190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_3040190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040190 prefixEnd_3040190 := by exact prefixLift 3040190
  have htrace : WordTrace (prefixWord ++ tailWord_3040190) baseStart_3040190 baseEnd_3040190 := by
    simpa [prefixWord, tailWord_3040190, baseEnd_3040190] using wordTrace_append hprefix tailTrace_3040190
  have hstable : (prefixWord ++ tailWord_3040190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040190).length < 2 ^ (prefixWord ++ tailWord_3040190).sum := by decide
  have hdescent : baseEnd_3040190 < baseStart_3040190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040192 : List Nat := [2, 1, 1, 2, 3, 4, 1, 4, 4]
def baseStart_3040192 : Nat := 118140960795 + 3040192 * 2 ^ 59
def prefixEnd_3040192 : Nat := 4983230072969 + 3 ^ 40 * 3040192 * 2
def baseEnd_3040192 : Nat := 346906617323083215226315

theorem tailTrace_3040192 : CollatzResearch.WordTrace tailWord_3040192 prefixEnd_3040192 346906617323083215226315 := by
  unfold tailWord_3040192
  simp only [CollatzResearch.WordTrace]
  refine ⟨55442455900955541150609415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73923274534607388200812553 55442455900955541150609415)
  ·
    refine ⟨83163683851433311725914123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55442455900955541150609415 83163683851433311725914123)
    ·
      refine ⟨124745525777149967588871185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83163683851433311725914123 124745525777149967588871185)
      ·
        refine ⟨93559144332862475691653389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124745525777149967588871185 93559144332862475691653389)
        ·
          refine ⟨35084679124823428384370021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93559144332862475691653389 35084679124823428384370021)
          ·
            refine ⟨6578377335904392822069379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35084679124823428384370021 6578377335904392822069379)
            ·
              refine ⟨9867566003856589233104069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6578377335904392822069379 9867566003856589233104069)
              ·
                refine ⟨1850168625723110481207013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9867566003856589233104069 1850168625723110481207013)
                ·
                  refine ⟨346906617323083215226315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1850168625723110481207013 346906617323083215226315)
                  ·
                    rfl

theorem cell22_3040192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 4].length) (baseStart_3040192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040192 prefixEnd_3040192 := by exact prefixLift 3040192
  have htrace : WordTrace (prefixWord ++ tailWord_3040192) baseStart_3040192 baseEnd_3040192 := by
    simpa [prefixWord, tailWord_3040192, baseEnd_3040192] using wordTrace_append hprefix tailTrace_3040192
  have hstable : (prefixWord ++ tailWord_3040192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040192).length < 2 ^ (prefixWord ++ tailWord_3040192).sum := by decide
  have hdescent : baseEnd_3040192 < baseStart_3040192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040207 : List Nat := [1, 1, 2, 1, 1, 6, 2, 3, 2, 3]
def baseStart_3040207 : Nat := 118140960795 + 3040207 * 2 ^ 59
def prefixEnd_3040207 : Nat := 4983230072969 + 3 ^ 40 * 3040207 * 2
def baseEnd_3040207 : Nat := 1040724986775794606553899

theorem tailTrace_3040207 : CollatzResearch.WordTrace tailWord_3040207 prefixEnd_3040207 1040724986775794606553899 := by
  unfold tailWord_3040207
  simp only [CollatzResearch.WordTrace]
  refine ⟨110885458896856739863014875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73923639264571159908676583 110885458896856739863014875)
  ·
    refine ⟨166328188345285109794522313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110885458896856739863014875 166328188345285109794522313)
    ·
      refine ⟨124746141258963832345891735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166328188345285109794522313 124746141258963832345891735)
      ·
        refine ⟨187119211888445748518837603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124746141258963832345891735 187119211888445748518837603)
        ·
          refine ⟨280678817832668622778256405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187119211888445748518837603 280678817832668622778256405)
          ·
            refine ⟨13156819585906341692730769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 280678817832668622778256405 13156819585906341692730769)
            ·
              refine ⟨9867614689429756269548077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13156819585906341692730769 9867614689429756269548077)
              ·
                refine ⟨3700355508536158601080529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9867614689429756269548077 3700355508536158601080529)
                ·
                  refine ⟨2775266631402118950810397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3700355508536158601080529 2775266631402118950810397)
                  ·
                    refine ⟨1040724986775794606553899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2775266631402118950810397 1040724986775794606553899)
                    ·
                      rfl

theorem cell22_3040207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 3].length) (baseStart_3040207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040207 prefixEnd_3040207 := by exact prefixLift 3040207
  have htrace : WordTrace (prefixWord ++ tailWord_3040207) baseStart_3040207 baseEnd_3040207 := by
    simpa [prefixWord, tailWord_3040207, baseEnd_3040207] using wordTrace_append hprefix tailTrace_3040207
  have hstable : (prefixWord ++ tailWord_3040207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040207).length < 2 ^ (prefixWord ++ tailWord_3040207).sum := by decide
  have hdescent : baseEnd_3040207 < baseStart_3040207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040226 : List Nat := [3, 3, 3, 1, 1, 2, 2, 3, 4]
def baseStart_3040226 : Nat := 118140960795 + 3040226 * 2 ^ 59
def prefixEnd_3040226 : Nat := 4983230072969 + 3 ^ 40 * 3040226 * 2
def baseEnd_3040226 : Nat := 346910496954694963442947

theorem tailTrace_3040226 : CollatzResearch.WordTrace tailWord_3040226 prefixEnd_3040226 346910496954694963442947 := by
  unfold tailWord_3040226
  simp only [CollatzResearch.WordTrace]
  refine ⟨27721537970946976526989133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73924101255858604071971021 27721537970946976526989133)
  ·
    refine ⟨10395576739105116197620925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27721537970946976526989133 10395576739105116197620925)
    ·
      refine ⟨3898341277164418574107847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10395576739105116197620925 3898341277164418574107847)
      ·
        refine ⟨5847511915746627861161771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3898341277164418574107847 5847511915746627861161771)
        ·
          refine ⟨8771267873619941791742657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5847511915746627861161771 8771267873619941791742657)
          ·
            refine ⟨6578450905214956343806993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8771267873619941791742657 6578450905214956343806993)
            ·
              refine ⟨4933838178911217257855245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6578450905214956343806993 4933838178911217257855245)
              ·
                refine ⟨1850189317091706471695717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4933838178911217257855245 1850189317091706471695717)
                ·
                  refine ⟨346910496954694963442947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1850189317091706471695717 346910496954694963442947)
                  ·
                    rfl

theorem cell22_3040226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_3040226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040226 prefixEnd_3040226 := by exact prefixLift 3040226
  have htrace : WordTrace (prefixWord ++ tailWord_3040226) baseStart_3040226 baseEnd_3040226 := by
    simpa [prefixWord, tailWord_3040226, baseEnd_3040226] using wordTrace_append hprefix tailTrace_3040226
  have hstable : (prefixWord ++ tailWord_3040226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040226).length < 2 ^ (prefixWord ++ tailWord_3040226).sum := by decide
  have hdescent : baseEnd_3040226 < baseStart_3040226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040252 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 3, 3]
def baseStart_3040252 : Nat := 118140960795 + 3040252 * 2 ^ 59
def prefixEnd_3040252 : Nat := 4983230072969 + 3 ^ 40 * 3040252 * 2
def baseEnd_3040252 : Nat := 1040740391195429489178761

theorem tailTrace_3040252 : CollatzResearch.WordTrace tailWord_3040252 prefixEnd_3040252 1040740391195429489178761 := by
  unfold tailWord_3040252
  simp only [CollatzResearch.WordTrace]
  refine ⟨55443550090846856274201505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73924733454462475032268673 55443550090846856274201505)
  ·
    refine ⟨41582662568135142205651129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55443550090846856274201505 41582662568135142205651129)
    ·
      refine ⟨31186996926101356654238347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41582662568135142205651129 31186996926101356654238347)
      ·
        refine ⟨46780495389152034981357521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31186996926101356654238347 46780495389152034981357521)
        ·
          refine ⟨35085371541864026236018141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46780495389152034981357521 35085371541864026236018141)
          ·
            refine ⟨13157014328199009838506803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35085371541864026236018141 13157014328199009838506803)
            ·
              refine ⟨19735521492298514757760205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13157014328199009838506803 19735521492298514757760205)
              ·
                refine ⟨7400820559611943034160077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19735521492298514757760205 7400820559611943034160077)
                ·
                  refine ⟨2775307709854478637810029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7400820559611943034160077 2775307709854478637810029)
                  ·
                    refine ⟨1040740391195429489178761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2775307709854478637810029 1040740391195429489178761)
                    ·
                      rfl

theorem cell22_3040252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_3040252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040252 prefixEnd_3040252 := by exact prefixLift 3040252
  have htrace : WordTrace (prefixWord ++ tailWord_3040252) baseStart_3040252 baseEnd_3040252 := by
    simpa [prefixWord, tailWord_3040252, baseEnd_3040252] using wordTrace_append hprefix tailTrace_3040252
  have hstable : (prefixWord ++ tailWord_3040252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040252).length < 2 ^ (prefixWord ++ tailWord_3040252).sum := by decide
  have hdescent : baseEnd_3040252 < baseStart_3040252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040258 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_3040258 : Nat := 118140960795 + 3040258 * 2 ^ 59
def prefixEnd_3040258 : Nat := 4983230072969 + 3 ^ 40 * 3040258 * 2
def baseEnd_3040258 : Nat := 1040742445118047473528743

theorem tailTrace_3040258 : CollatzResearch.WordTrace tailWord_3040258 prefixEnd_3040258 1040742445118047473528743 := by
  unfold tailWord_3040258
  simp only [CollatzResearch.WordTrace]
  refine ⟨27721829754917993893280357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73924879346447983715414285 27721829754917993893280357)
  ·
    refine ⟨5197843079047123854990067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27721829754917993893280357 5197843079047123854990067)
    ·
      refine ⟨7796764618570685782485101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5197843079047123854990067 7796764618570685782485101)
      ·
        refine ⟨2923786731964007168431913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7796764618570685782485101 2923786731964007168431913)
        ·
          refine ⟨2192840048973005376323935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2923786731964007168431913 2192840048973005376323935)
          ·
            refine ⟨3289260073459508064485903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192840048973005376323935 3289260073459508064485903)
            ·
              refine ⟨4933890110189262096728855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3289260073459508064485903 4933890110189262096728855)
              ·
                refine ⟨7400835165283893145093283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4933890110189262096728855 7400835165283893145093283)
                ·
                  refine ⟨11101252747925839717639925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7400835165283893145093283 11101252747925839717639925)
                  ·
                    refine ⟨1040742445118047473528743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11101252747925839717639925 1040742445118047473528743)
                    ·
                      rfl

theorem cell22_3040258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_3040258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040258 prefixEnd_3040258 := by exact prefixLift 3040258
  have htrace : WordTrace (prefixWord ++ tailWord_3040258) baseStart_3040258 baseEnd_3040258 := by
    simpa [prefixWord, tailWord_3040258, baseEnd_3040258] using wordTrace_append hprefix tailTrace_3040258
  have hstable : (prefixWord ++ tailWord_3040258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040258).length < 2 ^ (prefixWord ++ tailWord_3040258).sum := by decide
  have hdescent : baseEnd_3040258 < baseStart_3040258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040265 : List Nat := [1, 2, 1, 1, 3, 1, 1, 7, 5]
def baseStart_3040265 : Nat := 118140960795 + 3040265 * 2 ^ 59
def prefixEnd_3040265 : Nat := 4983230072969 + 3 ^ 40 * 3040265 * 2
def baseEnd_3040265 : Nat := 346914947120367262867907

theorem tailTrace_3040265 : CollatzResearch.WordTrace tailWord_3040265 prefixEnd_3040265 346914947120367262867907 := by
  unfold tailWord_3040265
  simp only [CollatzResearch.WordTrace]
  refine ⟨110887574330646615768626249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73925049553764410512417499 110887574330646615768626249)
  ·
    refine ⟨83165680747984961826469687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110887574330646615768626249 83165680747984961826469687)
    ·
      refine ⟨124748521121977442739704531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83165680747984961826469687 124748521121977442739704531)
      ·
        refine ⟨187122781682966164109556797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124748521121977442739704531 187122781682966164109556797)
        ·
          refine ⟨70171043131112311541083799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187122781682966164109556797 70171043131112311541083799)
          ·
            refine ⟨105256564696668467311625699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70171043131112311541083799 105256564696668467311625699)
            ·
              refine ⟨157884847045002700967438549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105256564696668467311625699 157884847045002700967438549)
              ·
                refine ⟨3700426102617250803924341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 157884847045002700967438549 3700426102617250803924341)
                ·
                  refine ⟨346914947120367262867907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3700426102617250803924341 346914947120367262867907)
                  ·
                    rfl

theorem cell22_3040265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 5].length) (baseStart_3040265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040265 prefixEnd_3040265 := by exact prefixLift 3040265
  have htrace : WordTrace (prefixWord ++ tailWord_3040265) baseStart_3040265 baseEnd_3040265 := by
    simpa [prefixWord, tailWord_3040265, baseEnd_3040265] using wordTrace_append hprefix tailTrace_3040265
  have hstable : (prefixWord ++ tailWord_3040265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040265).length < 2 ^ (prefixWord ++ tailWord_3040265).sum := by decide
  have hdescent : baseEnd_3040265 < baseStart_3040265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040357 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 2, 4]
def baseStart_3040357 : Nat := 118140960795 + 3040357 * 2 ^ 59
def prefixEnd_3040357 : Nat := 4983230072969 + 3 ^ 40 * 3040357 * 2
def baseEnd_3040357 : Nat := 1040776334841244215303439

theorem tailTrace_3040357 : CollatzResearch.WordTrace tailWord_3040357 prefixEnd_3040357 1040776334841244215303439 := by
  unfold tailWord_3040357
  simp only [CollatzResearch.WordTrace]
  refine ⟨110890929846313315480975325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73927286564208876987316883 110890929846313315480975325)
  ·
    refine ⟨41584098692367493305365747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110890929846313315480975325 41584098692367493305365747)
    ·
      refine ⟨62376148038551239958048621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41584098692367493305365747 62376148038551239958048621)
      ·
        refine ⟨23391055514456714984268233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62376148038551239958048621 23391055514456714984268233)
        ·
          refine ⟨17543291635842536238201175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23391055514456714984268233 17543291635842536238201175)
          ·
            refine ⟨26314937453763804357301763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17543291635842536238201175 26314937453763804357301763)
            ·
              refine ⟨39472406180645706535952645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26314937453763804357301763 39472406180645706535952645)
              ·
                refine ⟨7401076158871069975491121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39472406180645706535952645 7401076158871069975491121)
                ·
                  refine ⟨5550807119153302481618341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7401076158871069975491121 5550807119153302481618341)
                  ·
                    refine ⟨1040776334841244215303439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5550807119153302481618341 1040776334841244215303439)
                    ·
                      rfl

theorem cell22_3040357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_3040357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040357 prefixEnd_3040357 := by exact prefixLift 3040357
  have htrace : WordTrace (prefixWord ++ tailWord_3040357) baseStart_3040357 baseEnd_3040357 := by
    simpa [prefixWord, tailWord_3040357, baseEnd_3040357] using wordTrace_append hprefix tailTrace_3040357
  have hstable : (prefixWord ++ tailWord_3040357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040357).length < 2 ^ (prefixWord ++ tailWord_3040357).sum := by decide
  have hdescent : baseEnd_3040357 < baseStart_3040357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040359 : List Nat := [1, 1, 5, 1, 1, 3, 1, 4, 2, 3]
def baseStart_3040359 : Nat := 118140960795 + 3040359 * 2 ^ 59
def prefixEnd_3040359 : Nat := 4983230072969 + 3 ^ 40 * 3040359 * 2
def baseEnd_3040359 : Nat := 1040777019482116876753433

theorem tailTrace_3040359 : CollatzResearch.WordTrace tailWord_3040359 prefixEnd_3040359 1040777019482116876753433 := by
  unfold tailWord_3040359
  simp only [CollatzResearch.WordTrace]
  refine ⟨110891002792306069822548131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73927335194870713215032087 110891002792306069822548131)
  ·
    refine ⟨166336504188459104733822197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110891002792306069822548131 166336504188459104733822197)
    ·
      refine ⟨15594047267668041068795831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166336504188459104733822197 15594047267668041068795831)
      ·
        refine ⟨23391070901502061603193747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15594047267668041068795831 23391070901502061603193747)
        ·
          refine ⟨35086606352253092404790621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23391070901502061603193747 35086606352253092404790621)
          ·
            refine ⟨13157477382094909651796483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35086606352253092404790621 13157477382094909651796483)
            ·
              refine ⟨19736216073142364477694725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13157477382094909651796483 19736216073142364477694725)
              ·
                refine ⟨3700540513714193339567761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19736216073142364477694725 3700540513714193339567761)
                ·
                  refine ⟨2775405385285645004675821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3700540513714193339567761 2775405385285645004675821)
                  ·
                    refine ⟨1040777019482116876753433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2775405385285645004675821 1040777019482116876753433)
                    ·
                      rfl

theorem cell22_3040359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_3040359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040359 prefixEnd_3040359 := by exact prefixLift 3040359
  have htrace : WordTrace (prefixWord ++ tailWord_3040359) baseStart_3040359 baseEnd_3040359 := by
    simpa [prefixWord, tailWord_3040359, baseEnd_3040359] using wordTrace_append hprefix tailTrace_3040359
  have hstable : (prefixWord ++ tailWord_3040359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040359).length < 2 ^ (prefixWord ++ tailWord_3040359).sum := by decide
  have hdescent : baseEnd_3040359 < baseStart_3040359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040361 : List Nat := [1, 2, 1, 1, 1, 8, 2, 2, 4]
def baseStart_3040361 : Nat := 118140960795 + 3040361 * 2 ^ 59
def prefixEnd_3040361 : Nat := 4983230072969 + 3 ^ 40 * 3040361 * 2
def baseEnd_3040361 : Nat := 346925901374329846067809

theorem tailTrace_3040361 : CollatzResearch.WordTrace tailWord_3040361 prefixEnd_3040361 346925901374329846067809 := by
  unfold tailWord_3040361
  simp only [CollatzResearch.WordTrace]
  refine ⟨110891075738298824164120937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73927383825532549442747291 110891075738298824164120937)
  ·
    refine ⟨83168306803724118123090703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110891075738298824164120937 83168306803724118123090703)
    ·
      refine ⟨124752460205586177184636055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83168306803724118123090703 124752460205586177184636055)
      ·
        refine ⟨187128690308379265776954083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124752460205586177184636055 187128690308379265776954083)
        ·
          refine ⟨280693035462568898665431125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187128690308379265776954083 280693035462568898665431125)
          ·
            refine ⟨3289371509326979281235521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 280693035462568898665431125 3289371509326979281235521)
            ·
              refine ⟨2467028631995234460926641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3289371509326979281235521 2467028631995234460926641)
              ·
                refine ⟨1850271473996425845694981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2467028631995234460926641 1850271473996425845694981)
                ·
                  refine ⟨346925901374329846067809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1850271473996425845694981 346925901374329846067809)
                  ·
                    rfl

theorem cell22_3040361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 4].length) (baseStart_3040361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040361 prefixEnd_3040361 := by exact prefixLift 3040361
  have htrace : WordTrace (prefixWord ++ tailWord_3040361) baseStart_3040361 baseEnd_3040361 := by
    simpa [prefixWord, tailWord_3040361, baseEnd_3040361] using wordTrace_append hprefix tailTrace_3040361
  have hstable : (prefixWord ++ tailWord_3040361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040361).length < 2 ^ (prefixWord ++ tailWord_3040361).sum := by decide
  have hdescent : baseEnd_3040361 < baseStart_3040361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040389 : List Nat := [1, 3, 1, 1, 6, 1, 3, 6]
def baseStart_3040389 : Nat := 118140960795 + 3040389 * 2 ^ 59
def prefixEnd_3040389 : Nat := 4983230072969 + 3 ^ 40 * 3040389 * 2
def baseEnd_3040389 : Nat := 115643032121689644278149

theorem tailTrace_3040389 : CollatzResearch.WordTrace tailWord_3040389 prefixEnd_3040389 115643032121689644278149 := by
  unfold tailWord_3040389
  simp only [CollatzResearch.WordTrace]
  refine ⟨110892096982197384946140221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73928064654798256630760147 110892096982197384946140221)
  ·
    refine ⟨41584536368324019354802583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110892096982197384946140221 41584536368324019354802583)
    ·
      refine ⟨62376804552486029032203875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41584536368324019354802583 62376804552486029032203875)
      ·
        refine ⟨93565206828729043548305813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62376804552486029032203875 93565206828729043548305813)
        ·
          refine ⟨4385869070096673916326835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 93565206828729043548305813 4385869070096673916326835)
          ·
            refine ⟨6578803605145010874490253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4385869070096673916326835 6578803605145010874490253)
            ·
              refine ⟨2467051351929379077933845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6578803605145010874490253 2467051351929379077933845)
              ·
                refine ⟨115643032121689644278149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2467051351929379077933845 115643032121689644278149)
                ·
                  rfl

theorem cell22_3040389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 6].length) (baseStart_3040389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040389 prefixEnd_3040389 := by exact prefixLift 3040389
  have htrace : WordTrace (prefixWord ++ tailWord_3040389) baseStart_3040389 baseEnd_3040389 := by
    simpa [prefixWord, tailWord_3040389, baseEnd_3040389] using wordTrace_append hprefix tailTrace_3040389
  have hstable : (prefixWord ++ tailWord_3040389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040389).length < 2 ^ (prefixWord ++ tailWord_3040389).sum := by decide
  have hdescent : baseEnd_3040389 < baseStart_3040389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040417 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 7]
def baseStart_3040417 : Nat := 118140960795 + 3040417 * 2 ^ 59
def prefixEnd_3040417 : Nat := 4983230072969 + 3 ^ 40 * 3040417 * 2
def baseEnd_3040417 : Nat := 346932291355808019601085

theorem tailTrace_3040417 : CollatzResearch.WordTrace tailWord_3040417 prefixEnd_3040417 346932291355808019601085 := by
  unfold tailWord_3040417
  simp only [CollatzResearch.WordTrace]
  refine ⟨110893118226095945728159505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73928745484063963818773003 110893118226095945728159505)
  ·
    refine ⟨83169838669571959296119629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110893118226095945728159505 83169838669571959296119629)
    ·
      refine ⟨31188689501089484736044861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83169838669571959296119629 31188689501089484736044861)
      ·
        refine ⟨11695758562908556776016823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31188689501089484736044861 11695758562908556776016823)
        ·
          refine ⟨17543637844362835164025235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11695758562908556776016823 17543637844362835164025235)
          ·
            refine ⟨26315456766544252746037853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17543637844362835164025235 26315456766544252746037853)
            ·
              refine ⟨9868296287454094779764195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26315456766544252746037853 9868296287454094779764195)
              ·
                refine ⟨14802444431181142169646293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9868296287454094779764195 14802444431181142169646293)
                ·
                  refine ⟨346932291355808019601085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14802444431181142169646293 346932291355808019601085)
                  ·
                    rfl

theorem cell22_3040417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 7].length) (baseStart_3040417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040417 prefixEnd_3040417 := by exact prefixLift 3040417
  have htrace : WordTrace (prefixWord ++ tailWord_3040417) baseStart_3040417 baseEnd_3040417 := by
    simpa [prefixWord, tailWord_3040417, baseEnd_3040417] using wordTrace_append hprefix tailTrace_3040417
  have hstable : (prefixWord ++ tailWord_3040417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040417).length < 2 ^ (prefixWord ++ tailWord_3040417).sum := by decide
  have hdescent : baseEnd_3040417 < baseStart_3040417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040421 : List Nat := [1, 3, 1, 2, 1, 4, 2, 4, 1, 3]
def baseStart_3040421 : Nat := 118140960795 + 3040421 * 2 ^ 59
def prefixEnd_3040421 : Nat := 4983230072969 + 3 ^ 40 * 3040421 * 2
def baseEnd_3040421 : Nat := 1040798243349169381703243

theorem tailTrace_3040421 : CollatzResearch.WordTrace tailWord_3040421 prefixEnd_3040421 1040798243349169381703243 := by
  unfold tailWord_3040421
  simp only [CollatzResearch.WordTrace]
  refine ⟨110893264118081454411305117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73928842745387636274203411 110893264118081454411305117)
  ·
    refine ⟨41584974044280545404239419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110893264118081454411305117 41584974044280545404239419)
    ·
      refine ⟨62377461066420818106359129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41584974044280545404239419 62377461066420818106359129)
      ·
        refine ⟨46783095799815613579769347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62377461066420818106359129 46783095799815613579769347)
        ·
          refine ⟨70174643699723420369654021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46783095799815613579769347 70174643699723420369654021)
          ·
            refine ⟨13157745693698141319310129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70174643699723420369654021 13157745693698141319310129)
            ·
              refine ⟨9868309270273605989482597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13157745693698141319310129 9868309270273605989482597)
              ·
                refine ⟨1850307988176301123027987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9868309270273605989482597 1850307988176301123027987)
                ·
                  refine ⟨2775461982264451684541981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1850307988176301123027987 2775461982264451684541981)
                  ·
                    refine ⟨1040798243349169381703243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2775461982264451684541981 1040798243349169381703243)
                    ·
                      rfl

theorem cell22_3040421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_3040421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040421 prefixEnd_3040421 := by exact prefixLift 3040421
  have htrace : WordTrace (prefixWord ++ tailWord_3040421) baseStart_3040421 baseEnd_3040421 := by
    simpa [prefixWord, tailWord_3040421, baseEnd_3040421] using wordTrace_append hprefix tailTrace_3040421
  have hstable : (prefixWord ++ tailWord_3040421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040421).length < 2 ^ (prefixWord ++ tailWord_3040421).sum := by decide
  have hdescent : baseEnd_3040421 < baseStart_3040421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040447 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 3, 4]
def baseStart_3040447 : Nat := 118140960795 + 3040447 * 2 ^ 59
def prefixEnd_3040447 : Nat := 4983230072969 + 3 ^ 40 * 3040447 * 2
def baseEnd_3040447 : Nat := 1040807143680513980553163

theorem tailTrace_3040447 : CollatzResearch.WordTrace tailWord_3040447 prefixEnd_3040447 1040807143680513980553163 := by
  unfold tailWord_3040447
  simp only [CollatzResearch.WordTrace]
  refine ⟨110894212415987260851751595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73929474943991507234501063 110894212415987260851751595)
  ·
    refine ⟨166341318623980891277627393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110894212415987260851751595 166341318623980891277627393)
    ·
      refine ⟨124755988967985668458220545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166341318623980891277627393 124755988967985668458220545)
      ·
        refine ⟨93566991725989251343665409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124755988967985668458220545 93566991725989251343665409)
        ·
          refine ⟨70175243794491938507749057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93566991725989251343665409 70175243794491938507749057)
          ·
            refine ⟨52631432845868953880811793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70175243794491938507749057 52631432845868953880811793)
            ·
              refine ⟨39473574634401715410608845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52631432845868953880811793 39473574634401715410608845)
              ·
                refine ⟨14802590487900643278978317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39473574634401715410608845 14802590487900643278978317)
                ·
                  refine ⟨5550971432962741229616869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14802590487900643278978317 5550971432962741229616869)
                  ·
                    refine ⟨1040807143680513980553163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5550971432962741229616869 1040807143680513980553163)
                    ·
                      rfl

theorem cell22_3040447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_3040447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040447 prefixEnd_3040447 := by exact prefixLift 3040447
  have htrace : WordTrace (prefixWord ++ tailWord_3040447) baseStart_3040447 baseEnd_3040447 := by
    simpa [prefixWord, tailWord_3040447, baseEnd_3040447] using wordTrace_append hprefix tailTrace_3040447
  have hstable : (prefixWord ++ tailWord_3040447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040447).length < 2 ^ (prefixWord ++ tailWord_3040447).sum := by decide
  have hdescent : baseEnd_3040447 < baseStart_3040447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040479 : List Nat := [1, 1, 2, 3, 2, 1, 2, 6, 4]
def baseStart_3040479 : Nat := 118140960795 + 3040479 * 2 ^ 59
def prefixEnd_3040479 : Nat := 4983230072969 + 3 ^ 40 * 3040479 * 2
def baseEnd_3040479 : Nat := 346939365978158854584355

theorem tailTrace_3040479 : CollatzResearch.WordTrace tailWord_3040479 prefixEnd_3040479 346939365978158854584355 := by
  unfold tailWord_3040479
  simp only [CollatzResearch.WordTrace]
  refine ⟨110895379551871330316916491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73930253034580886877944327 110895379551871330316916491)
  ·
    refine ⟨166343069327806995475374737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110895379551871330316916491 166343069327806995475374737)
    ·
      refine ⟨124757301995855246606531053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166343069327806995475374737 124757301995855246606531053)
      ·
        refine ⟨46783988248445717477449145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124757301995855246606531053 46783988248445717477449145)
        ·
          refine ⟨35087991186334288108086859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46783988248445717477449145 35087991186334288108086859)
          ·
            refine ⟨52631986779501432162130289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35087991186334288108086859 52631986779501432162130289)
            ·
              refine ⟨39473990084626074121597717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52631986779501432162130289 39473990084626074121597717)
              ·
                refine ⟨1850343285216847224449893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39473990084626074121597717 1850343285216847224449893)
                ·
                  refine ⟨346939365978158854584355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1850343285216847224449893 346939365978158854584355)
                  ·
                    rfl

theorem cell22_3040479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 4].length) (baseStart_3040479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040479 prefixEnd_3040479 := by exact prefixLift 3040479
  have htrace : WordTrace (prefixWord ++ tailWord_3040479) baseStart_3040479 baseEnd_3040479 := by
    simpa [prefixWord, tailWord_3040479, baseEnd_3040479] using wordTrace_append hprefix tailTrace_3040479
  have hstable : (prefixWord ++ tailWord_3040479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040479).length < 2 ^ (prefixWord ++ tailWord_3040479).sum := by decide
  have hdescent : baseEnd_3040479 < baseStart_3040479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040498 : List Nat := [3, 2, 1, 3, 3, 2, 1, 2, 1, 4]
def baseStart_3040498 : Nat := 118140960795 + 3040498 * 2 ^ 59
def prefixEnd_3040498 : Nat := 4983230072969 + 3 ^ 40 * 3040498 * 2
def baseEnd_3040498 : Nat := 1040824602022766847528007

theorem tailTrace_3040498 : CollatzResearch.WordTrace tailWord_3040498 prefixEnd_3040498 1040824602022766847528007 := by
  unfold tailWord_3040498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27724018134700624140464537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73930715025868331041238765 27724018134700624140464537)
  ·
    refine ⟨20793013601025468105348403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27724018134700624140464537 20793013601025468105348403)
    ·
      refine ⟨31189520401538202158022605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20793013601025468105348403 31189520401538202158022605)
      ·
        refine ⟨11696070150576825809258477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31189520401538202158022605 11696070150576825809258477)
        ·
          refine ⟨4386026306466309678471929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11696070150576825809258477 4386026306466309678471929)
          ·
            refine ⟨3289519729849732258853947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4386026306466309678471929 3289519729849732258853947)
            ·
              refine ⟨4934279594774598388280921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3289519729849732258853947 4934279594774598388280921)
              ·
                refine ⟨3700709696080948791210691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4934279594774598388280921 3700709696080948791210691)
                ·
                  refine ⟨5551064544121423186816037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3700709696080948791210691 5551064544121423186816037)
                  ·
                    refine ⟨1040824602022766847528007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5551064544121423186816037 1040824602022766847528007)
                    ·
                      rfl

theorem cell22_3040498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_3040498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040498 prefixEnd_3040498 := by exact prefixLift 3040498
  have htrace : WordTrace (prefixWord ++ tailWord_3040498) baseStart_3040498 baseEnd_3040498 := by
    simpa [prefixWord, tailWord_3040498, baseEnd_3040498] using wordTrace_append hprefix tailTrace_3040498
  have hstable : (prefixWord ++ tailWord_3040498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040498).length < 2 ^ (prefixWord ++ tailWord_3040498).sum := by decide
  have hdescent : baseEnd_3040498 < baseStart_3040498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040530 : List Nat := [3, 2, 4, 2, 1, 1, 1, 4, 4]
def baseStart_3040530 : Nat := 118140960795 + 3040530 * 2 ^ 59
def prefixEnd_3040530 : Nat := 4983230072969 + 3 ^ 40 * 3040530 * 2
def baseEnd_3040530 : Nat := 346945185425576476909303

theorem tailTrace_3040530 : CollatzResearch.WordTrace tailWord_3040530 prefixEnd_3040530 346945185425576476909303 := by
  unfold tailWord_3040530
  simp only [CollatzResearch.WordTrace]
  refine ⟨27724309918671641506755761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73931493116457710684682029 27724309918671641506755761)
  ·
    refine ⟨20793232439003731130066821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27724309918671641506755761 20793232439003731130066821)
    ·
      refine ⟨3898731082313199586887529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20793232439003731130066821 3898731082313199586887529)
      ·
        refine ⟨2924048311734899690165647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3898731082313199586887529 2924048311734899690165647)
        ·
          refine ⟨4386072467602349535248471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2924048311734899690165647 4386072467602349535248471)
          ·
            refine ⟨6579108701403524302872707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4386072467602349535248471 6579108701403524302872707)
            ·
              refine ⟨9868663052105286454309061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6579108701403524302872707 9868663052105286454309061)
              ·
                refine ⟨1850374322269741210182949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9868663052105286454309061 1850374322269741210182949)
                ·
                  refine ⟨346945185425576476909303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1850374322269741210182949 346945185425576476909303)
                  ·
                    rfl

theorem cell22_3040530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_3040530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040530 prefixEnd_3040530 := by exact prefixLift 3040530
  have htrace : WordTrace (prefixWord ++ tailWord_3040530) baseStart_3040530 baseEnd_3040530 := by
    simpa [prefixWord, tailWord_3040530, baseEnd_3040530] using wordTrace_append hprefix tailTrace_3040530
  have hstable : (prefixWord ++ tailWord_3040530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040530).length < 2 ^ (prefixWord ++ tailWord_3040530).sum := by decide
  have hdescent : baseEnd_3040530 < baseStart_3040530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040539 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 3, 3]
def baseStart_3040539 : Nat := 118140960795 + 3040539 * 2 ^ 59
def prefixEnd_3040539 : Nat := 4983230072969 + 3 ^ 40 * 3040539 * 2
def baseEnd_3040539 : Nat := 1040838637160656407252881

theorem tailTrace_3040539 : CollatzResearch.WordTrace tailWord_3040539 prefixEnd_3040539 1040838637160656407252881 := by
  unfold tailWord_3040539
  simp only [CollatzResearch.WordTrace]
  refine ⟨110897567931653960564100671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73931711954435973709400447 110897567931653960564100671)
  ·
    refine ⟨166346351897480940846151007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110897567931653960564100671 166346351897480940846151007)
    ·
      refine ⟨249519527846221411269226511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166346351897480940846151007 249519527846221411269226511)
      ·
        refine ⟨374279291769332116903839767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249519527846221411269226511 374279291769332116903839767)
        ·
          refine ⟨561418937653998175355759651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374279291769332116903839767 561418937653998175355759651)
          ·
            refine ⟨842128406480997263033639477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561418937653998175355759651 842128406480997263033639477)
            ·
              refine ⟨78949538107593493409403701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 842128406480997263033639477 78949538107593493409403701)
              ·
                refine ⟨7401519197586890007131597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78949538107593493409403701 7401519197586890007131597)
                ·
                  refine ⟨2775569699095083752674349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7401519197586890007131597 2775569699095083752674349)
                  ·
                    refine ⟨1040838637160656407252881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2775569699095083752674349 1040838637160656407252881)
                    ·
                      rfl

theorem cell22_3040539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 3].length) (baseStart_3040539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040539 prefixEnd_3040539 := by exact prefixLift 3040539
  have htrace : WordTrace (prefixWord ++ tailWord_3040539) baseStart_3040539 baseEnd_3040539 := by
    simpa [prefixWord, tailWord_3040539, baseEnd_3040539] using wordTrace_append hprefix tailTrace_3040539
  have hstable : (prefixWord ++ tailWord_3040539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040539).length < 2 ^ (prefixWord ++ tailWord_3040539).sum := by decide
  have hdescent : baseEnd_3040539 < baseStart_3040539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040541 : List Nat := [1, 4, 2, 3, 1, 3, 1, 7]
def baseStart_3040541 : Nat := 118140960795 + 3040541 * 2 ^ 59
def prefixEnd_3040541 : Nat := 4983230072969 + 3 ^ 40 * 3040541 * 2
def baseEnd_3040541 : Nat := 115648813533503229855875

theorem tailTrace_3040541 : CollatzResearch.WordTrace tailWord_3040541 prefixEnd_3040541 115648813533503229855875 := by
  unfold tailWord_3040541
  simp only [CollatzResearch.WordTrace]
  refine ⟨110897640877646714905673477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73931760585097809937115651 110897640877646714905673477)
  ·
    refine ⟨20793307664558759044813777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110897640877646714905673477 20793307664558759044813777)
    ·
      refine ⟨15594980748419069283610333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20793307664558759044813777 15594980748419069283610333)
      ·
        refine ⟨5848117780657150981353875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15594980748419069283610333 5848117780657150981353875)
        ·
          refine ⟨8772176670985726472030813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5848117780657150981353875 8772176670985726472030813)
          ·
            refine ⟨3289566251619647427011555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8772176670985726472030813 3289566251619647427011555)
            ·
              refine ⟨4934349377429471140517333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3289566251619647427011555 4934349377429471140517333)
              ·
                refine ⟨115648813533503229855875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4934349377429471140517333 115648813533503229855875)
                ·
                  rfl

theorem cell22_3040541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 7].length) (baseStart_3040541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040541 prefixEnd_3040541 := by exact prefixLift 3040541
  have htrace : WordTrace (prefixWord ++ tailWord_3040541) baseStart_3040541 baseEnd_3040541 := by
    simpa [prefixWord, tailWord_3040541, baseEnd_3040541] using wordTrace_append hprefix tailTrace_3040541
  have hstable : (prefixWord ++ tailWord_3040541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040541).length < 2 ^ (prefixWord ++ tailWord_3040541).sum := by decide
  have hdescent : baseEnd_3040541 < baseStart_3040541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040704 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 7]
def baseStart_3040704 : Nat := 118140960795 + 3040704 * 2 ^ 59
def prefixEnd_3040704 : Nat := 4983230072969 + 3 ^ 40 * 3040704 * 2
def baseEnd_3040704 : Nat := 346965040010883658959125

theorem tailTrace_3040704 : CollatzResearch.WordTrace tailWord_3040704 prefixEnd_3040704 346965040010883658959125 := by
  unfold tailWord_3040704
  simp only [CollatzResearch.WordTrace]
  refine ⟨55451792988028096871928583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73935723984037462495904777 55451792988028096871928583)
  ·
    refine ⟨83177689482042145307892875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55451792988028096871928583 83177689482042145307892875)
    ·
      refine ⟨124766534223063217961839313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83177689482042145307892875 124766534223063217961839313)
      ·
        refine ⟨93574900667297413471379485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124766534223063217961839313 93574900667297413471379485)
        ·
          refine ⟨35090587750236530051767307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93574900667297413471379485 35090587750236530051767307)
          ·
            refine ⟨52635881625354795077650961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35090587750236530051767307 52635881625354795077650961)
            ·
              refine ⟨39476911219016096308238221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52635881625354795077650961 39476911219016096308238221)
              ·
                refine ⟨14803841707131036115589333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39476911219016096308238221 14803841707131036115589333)
                ·
                  refine ⟨346965040010883658959125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14803841707131036115589333 346965040010883658959125)
                  ·
                    rfl

theorem cell22_3040704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 7].length) (baseStart_3040704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040704 prefixEnd_3040704 := by exact prefixLift 3040704
  have htrace : WordTrace (prefixWord ++ tailWord_3040704) baseStart_3040704 baseEnd_3040704 := by
    simpa [prefixWord, tailWord_3040704, baseEnd_3040704] using wordTrace_append hprefix tailTrace_3040704
  have hstable : (prefixWord ++ tailWord_3040704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040704).length < 2 ^ (prefixWord ++ tailWord_3040704).sum := by decide
  have hdescent : baseEnd_3040704 < baseStart_3040704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040719 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 1, 7]
def baseStart_3040719 : Nat := 118140960795 + 3040719 * 2 ^ 59
def prefixEnd_3040719 : Nat := 4983230072969 + 3 ^ 40 * 3040719 * 2
def baseEnd_3040719 : Nat := 1040900254839195937752329

theorem tailTrace_3040719 : CollatzResearch.WordTrace tailWord_3040719 prefixEnd_3040719 1040900254839195937752329 := by
  unfold tailWord_3040719
  simp only [CollatzResearch.WordTrace]
  refine ⟨110904133071001851305653211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73936088714001234203768807 110904133071001851305653211)
  ·
    refine ⟨166356199606502776958479817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110904133071001851305653211 166356199606502776958479817)
    ·
      refine ⟨124767149704877082718859863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166356199606502776958479817 124767149704877082718859863)
      ·
        refine ⟨187150724557315624078289795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124767149704877082718859863 187150724557315624078289795)
        ·
          refine ⟨280726086835973436117434693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187150724557315624078289795 280726086835973436117434693)
          ·
            refine ⟨52636141281745019272019005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280726086835973436117434693 52636141281745019272019005)
            ·
              refine ⟨19738552980654382227007127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52636141281745019272019005 19738552980654382227007127)
              ·
                refine ⟨29607829470981573340510691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19738552980654382227007127 29607829470981573340510691)
                ·
                  refine ⟨44411744206472360010766037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29607829470981573340510691 44411744206472360010766037)
                  ·
                    refine ⟨1040900254839195937752329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44411744206472360010766037 1040900254839195937752329)
                    ·
                      rfl

theorem cell22_3040719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_3040719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040719 prefixEnd_3040719 := by exact prefixLift 3040719
  have htrace : WordTrace (prefixWord ++ tailWord_3040719) baseStart_3040719 baseEnd_3040719 := by
    simpa [prefixWord, tailWord_3040719, baseEnd_3040719] using wordTrace_append hprefix tailTrace_3040719
  have hstable : (prefixWord ++ tailWord_3040719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040719).length < 2 ^ (prefixWord ++ tailWord_3040719).sum := by decide
  have hdescent : baseEnd_3040719 < baseStart_3040719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040796 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 1, 6]
def baseStart_3040796 : Nat := 118140960795 + 3040796 * 2 ^ 59
def prefixEnd_3040796 : Nat := 4983230072969 + 3 ^ 40 * 3040796 * 2
def baseEnd_3040796 : Nat := 1040926613512793403577093

theorem tailTrace_3040796 : CollatzResearch.WordTrace tailWord_3040796 prefixEnd_3040796 1040926613512793403577093 := by
  unfold tailWord_3040796
  simp only [CollatzResearch.WordTrace]
  refine ⟨55453470745861446728103121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73937960994481928970804161 55453470745861446728103121)
  ·
    refine ⟨41590103059396085046077341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55453470745861446728103121 41590103059396085046077341)
    ·
      refine ⟨15596288647273531892279003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41590103059396085046077341 15596288647273531892279003)
      ·
        refine ⟨23394432970910297838418505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15596288647273531892279003 23394432970910297838418505)
        ·
          refine ⟨17545824728182723378813879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23394432970910297838418505 17545824728182723378813879)
          ·
            refine ⟨26318737092274085068220819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17545824728182723378813879 26318737092274085068220819)
            ·
              refine ⟨39478105638411127602331229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26318737092274085068220819 39478105638411127602331229)
              ·
                refine ⟨14804289614404172850874211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39478105638411127602331229 14804289614404172850874211)
                ·
                  refine ⟨22206434421606259276311317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14804289614404172850874211 22206434421606259276311317)
                  ·
                    refine ⟨1040926613512793403577093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22206434421606259276311317 1040926613512793403577093)
                    ·
                      rfl

theorem cell22_3040796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_3040796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040796 prefixEnd_3040796 := by exact prefixLift 3040796
  have htrace : WordTrace (prefixWord ++ tailWord_3040796) baseStart_3040796 baseEnd_3040796 := by
    simpa [prefixWord, tailWord_3040796, baseEnd_3040796] using wordTrace_append hprefix tailTrace_3040796
  have hstable : (prefixWord ++ tailWord_3040796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040796).length < 2 ^ (prefixWord ++ tailWord_3040796).sum := by decide
  have hdescent : baseEnd_3040796 < baseStart_3040796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040800 : List Nat := [2, 1, 1, 6, 1, 1, 3, 3, 4]
def baseStart_3040800 : Nat := 118140960795 + 3040800 * 2 ^ 59
def prefixEnd_3040800 : Nat := 4983230072969 + 3 ^ 40 * 3040800 * 2
def baseEnd_3040800 : Nat := 346975994264846242159027

theorem tailTrace_3040800 : CollatzResearch.WordTrace tailWord_3040800 prefixEnd_3040800 346975994264846242159027 := by
  unfold tailWord_3040800
  simp only [CollatzResearch.WordTrace]
  refine ⟨55453543691854201069675927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73938058255805601426234569 55453543691854201069675927)
  ·
    refine ⟨83180315537781301604513891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55453543691854201069675927 83180315537781301604513891)
    ·
      refine ⟨124770473306671952406770837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83180315537781301604513891 124770473306671952406770837)
      ·
        refine ⟨5848615936250247769067383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 124770473306671952406770837 5848615936250247769067383)
        ·
          refine ⟨8772923904375371653601075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5848615936250247769067383 8772923904375371653601075)
          ·
            refine ⟨13159385856563057480401613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8772923904375371653601075 13159385856563057480401613)
            ·
              refine ⟨4934769696211146555150605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13159385856563057480401613 4934769696211146555150605)
              ·
                refine ⟨1850538636079179958181477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4934769696211146555150605 1850538636079179958181477)
                ·
                  refine ⟨346975994264846242159027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1850538636079179958181477 346975994264846242159027)
                  ·
                    rfl

theorem cell22_3040800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 4].length) (baseStart_3040800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040800 prefixEnd_3040800 := by exact prefixLift 3040800
  have htrace : WordTrace (prefixWord ++ tailWord_3040800) baseStart_3040800 baseEnd_3040800 := by
    simpa [prefixWord, tailWord_3040800, baseEnd_3040800] using wordTrace_append hprefix tailTrace_3040800
  have hstable : (prefixWord ++ tailWord_3040800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040800).length < 2 ^ (prefixWord ++ tailWord_3040800).sum := by decide
  have hdescent : baseEnd_3040800 < baseStart_3040800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040828 : List Nat := [2, 2, 2, 2, 4, 1, 2, 7]
def baseStart_3040828 : Nat := 118140960795 + 3040828 * 2 ^ 59
def prefixEnd_3040828 : Nat := 4983230072969 + 3 ^ 40 * 3040828 * 2
def baseEnd_3040828 : Nat := 115659729751861776308555

theorem tailTrace_3040828 : CollatzResearch.WordTrace tailWord_3040828 prefixEnd_3040828 115659729751861776308555 := by
  unfold tailWord_3040828
  simp only [CollatzResearch.WordTrace]
  refine ⟨55454054313803481460685569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73938739085071308614247425 55454054313803481460685569)
  ·
    refine ⟨41590540735352611095514177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55454054313803481460685569 41590540735352611095514177)
    ·
      refine ⟨31192905551514458321635633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41590540735352611095514177 31192905551514458321635633)
      ·
        refine ⟨23394679163635843741226725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31192905551514458321635633 23394679163635843741226725)
        ·
          refine ⟨4386502343181720701480011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23394679163635843741226725 4386502343181720701480011)
          ·
            refine ⟨6579753514772581052220017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4386502343181720701480011 6579753514772581052220017)
            ·
              refine ⟨4934815136079435789165013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6579753514772581052220017 4934815136079435789165013)
              ·
                refine ⟨115659729751861776308555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4934815136079435789165013 115659729751861776308555)
                ·
                  rfl

theorem cell22_3040828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 7].length) (baseStart_3040828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040828 prefixEnd_3040828 := by exact prefixLift 3040828
  have htrace : WordTrace (prefixWord ++ tailWord_3040828) baseStart_3040828 baseEnd_3040828 := by
    simpa [prefixWord, tailWord_3040828, baseEnd_3040828] using wordTrace_append hprefix tailTrace_3040828
  have hstable : (prefixWord ++ tailWord_3040828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040828).length < 2 ^ (prefixWord ++ tailWord_3040828).sum := by decide
  have hdescent : baseEnd_3040828 < baseStart_3040828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040903 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 3, 4]
def baseStart_3040903 : Nat := 118140960795 + 3040903 * 2 ^ 59
def prefixEnd_3040903 : Nat := 4983230072969 + 3 ^ 40 * 3040903 * 2
def baseEnd_3040903 : Nat := 1040963241799480791151765

theorem tailTrace_3040903 : CollatzResearch.WordTrace tailWord_3040903 prefixEnd_3040903 1040963241799480791151765 := by
  unfold tailWord_3040903
  simp only [CollatzResearch.WordTrace]
  refine ⟨110910844102335250730351363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73940562734890167153567575 110910844102335250730351363)
  ·
    refine ⟨166366266153502876095527045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110910844102335250730351363 166366266153502876095527045)
    ·
      refine ⟨31193674903781789267911321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166366266153502876095527045 31193674903781789267911321)
      ·
        refine ⟨23395256177836341950933491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31193674903781789267911321 23395256177836341950933491)
        ·
          refine ⟨35092884266754512926400237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23395256177836341950933491 35092884266754512926400237)
          ·
            refine ⟨13159831600032942347400089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35092884266754512926400237 13159831600032942347400089)
            ·
              refine ⟨9869873700024706760550067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13159831600032942347400089 9869873700024706760550067)
              ·
                refine ⟨14804810550037060140825101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9869873700024706760550067 14804810550037060140825101)
                ·
                  refine ⟨5551803956263897552809413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14804810550037060140825101 5551803956263897552809413)
                  ·
                    refine ⟨1040963241799480791151765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5551803956263897552809413 1040963241799480791151765)
                    ·
                      rfl

theorem cell22_3040903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_3040903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040903 prefixEnd_3040903 := by exact prefixLift 3040903
  have htrace : WordTrace (prefixWord ++ tailWord_3040903) baseStart_3040903 baseEnd_3040903 := by
    simpa [prefixWord, tailWord_3040903, baseEnd_3040903] using wordTrace_append hprefix tailTrace_3040903
  have hstable : (prefixWord ++ tailWord_3040903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040903).length < 2 ^ (prefixWord ++ tailWord_3040903).sum := by decide
  have hdescent : baseEnd_3040903 < baseStart_3040903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040920 : List Nat := [2, 1, 2, 4, 1, 3, 1, 3, 1, 4]
def baseStart_3040920 : Nat := 118140960795 + 3040920 * 2 ^ 59
def prefixEnd_3040920 : Nat := 4983230072969 + 3 ^ 40 * 3040920 * 2
def baseEnd_3040920 : Nat := 1040969061246898413476713

theorem tailTrace_3040920 : CollatzResearch.WordTrace tailWord_3040920 prefixEnd_3040920 1040969061246898413476713 := by
  unfold tailWord_3040920
  simp only [CollatzResearch.WordTrace]
  refine ⟨55455732071636831316860107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73940976095515775089146809 55455732071636831316860107)
  ·
    refine ⟨83183598107455246975290161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55455732071636831316860107 83183598107455246975290161)
    ·
      refine ⟨62387698580591435231467621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83183598107455246975290161 62387698580591435231467621)
      ·
        refine ⟨11697693483860894105900179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62387698580591435231467621 11697693483860894105900179)
        ·
          refine ⟨17546540225791341158850269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11697693483860894105900179 17546540225791341158850269)
          ·
            refine ⟨6579952584671752934568851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17546540225791341158850269 6579952584671752934568851)
            ·
              refine ⟨9869928877007629401853277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6579952584671752934568851 9869928877007629401853277)
              ·
                refine ⟨3701223328877861025694979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9869928877007629401853277 3701223328877861025694979)
                ·
                  refine ⟨5551834993316791538542469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3701223328877861025694979 5551834993316791538542469)
                  ·
                    refine ⟨1040969061246898413476713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5551834993316791538542469 1040969061246898413476713)
                    ·
                      rfl

theorem cell22_3040920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_3040920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040920 prefixEnd_3040920 := by exact prefixLift 3040920
  have htrace : WordTrace (prefixWord ++ tailWord_3040920) baseStart_3040920 baseEnd_3040920 := by
    simpa [prefixWord, tailWord_3040920, baseEnd_3040920] using wordTrace_append hprefix tailTrace_3040920
  have hstable : (prefixWord ++ tailWord_3040920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040920).length < 2 ^ (prefixWord ++ tailWord_3040920).sum := by decide
  have hdescent : baseEnd_3040920 < baseStart_3040920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3040980 : List Nat := [2, 4, 1, 3, 1, 3, 8]
def baseStart_3040980 : Nat := 118140960795 + 3040980 * 2 ^ 59
def prefixEnd_3040980 : Nat := 4983230072969 + 3 ^ 40 * 3040980 * 2
def baseEnd_3040980 : Nat := 38555170387891787295427

theorem tailTrace_3040980 : CollatzResearch.WordTrace tailWord_3040980 prefixEnd_3040980 38555170387891787295427 := by
  unfold tailWord_3040980
  simp only [CollatzResearch.WordTrace]
  refine ⟨55456826261528146440452197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73942435015370861920602929 55456826261528146440452197)
  ·
    refine ⟨10398154924036527457584787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55456826261528146440452197 10398154924036527457584787)
    ·
      refine ⟨15597232386054791186377181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10398154924036527457584787 15597232386054791186377181)
      ·
        refine ⟨5848962144770546694891443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15597232386054791186377181 5848962144770546694891443)
        ·
          refine ⟨8773443217155820042337165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5848962144770546694891443 8773443217155820042337165)
          ·
            refine ⟨3290041206433432515876437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8773443217155820042337165 3290041206433432515876437)
            ·
              refine ⟨38555170387891787295427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3290041206433432515876437 38555170387891787295427)
              ·
                rfl

theorem cell22_3040980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 8].length) (baseStart_3040980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3040980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3040980 prefixEnd_3040980 := by exact prefixLift 3040980
  have htrace : WordTrace (prefixWord ++ tailWord_3040980) baseStart_3040980 baseEnd_3040980 := by
    simpa [prefixWord, tailWord_3040980, baseEnd_3040980] using wordTrace_append hprefix tailTrace_3040980
  have hstable : (prefixWord ++ tailWord_3040980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3040980).length < 2 ^ (prefixWord ++ tailWord_3040980).sum := by decide
  have hdescent : baseEnd_3040980 < baseStart_3040980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3040980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041037 : List Nat := [1, 7, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3041037 : Nat := 118140960795 + 3041037 * 2 ^ 59
def prefixEnd_3041037 : Nat := 4983230072969 + 3 ^ 40 * 3041037 * 2
def baseEnd_3041037 : Nat := 347003037579316369433785

theorem tailTrace_3041037 : CollatzResearch.WordTrace tailWord_3041037 prefixEnd_3041037 347003037579316369433785 := by
  unfold tailWord_3041037
  simp only [CollatzResearch.WordTrace]
  refine ⟨110915731483849791615729365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73943820989233194410486243 110915731483849791615729365)
  ·
    refine ⟨2599587456652729490993657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 110915731483849791615729365 2599587456652729490993657)
    ·
      refine ⟨1949690592489547118245243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2599587456652729490993657 1949690592489547118245243)
      ·
        refine ⟨2924535888734320677367865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1949690592489547118245243 2924535888734320677367865)
        ·
          refine ⟨2193401916550740508025899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2924535888734320677367865 2193401916550740508025899)
          ·
            refine ⟨3290102874826110762038849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2193401916550740508025899 3290102874826110762038849)
            ·
              refine ⟨2467577156119583071529137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3290102874826110762038849 2467577156119583071529137)
              ·
                refine ⟨1850682867089687303646853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2467577156119583071529137 1850682867089687303646853)
                ·
                  refine ⟨347003037579316369433785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1850682867089687303646853 347003037579316369433785)
                  ·
                    rfl

theorem cell22_3041037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3041037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041037 prefixEnd_3041037 := by exact prefixLift 3041037
  have htrace : WordTrace (prefixWord ++ tailWord_3041037) baseStart_3041037 baseEnd_3041037 := by
    simpa [prefixWord, tailWord_3041037, baseEnd_3041037] using wordTrace_append hprefix tailTrace_3041037
  have hstable : (prefixWord ++ tailWord_3041037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041037).length < 2 ^ (prefixWord ++ tailWord_3041037).sum := by decide
  have hdescent : baseEnd_3041037 < baseStart_3041037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041042 : List Nat := [3, 2, 4, 1, 1, 1, 1, 4, 5]
def baseStart_3041042 : Nat := 118140960795 + 3041042 * 2 ^ 59
def prefixEnd_3041042 : Nat := 4983230072969 + 3 ^ 40 * 3041042 * 2
def baseEnd_3041042 : Nat := 347003608113376920642113

theorem tailTrace_3041042 : CollatzResearch.WordTrace tailWord_3041042 prefixEnd_3041042 347003608113376920642113 := by
  unfold tailWord_3041042
  simp only [CollatzResearch.WordTrace]
  refine ⟨27728978462207919367415345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73943942565887784979774253 27728978462207919367415345)
  ·
    refine ⟨20796733846655939525561509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27728978462207919367415345 20796733846655939525561509)
    ·
      refine ⟨3899387596247988661042783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20796733846655939525561509 3899387596247988661042783)
      ·
        refine ⟨5849081394371982991564175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3899387596247988661042783 5849081394371982991564175)
        ·
          refine ⟨8773622091557974487346263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5849081394371982991564175 8773622091557974487346263)
          ·
            refine ⟨13160433137336961731019395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8773622091557974487346263 13160433137336961731019395)
            ·
              refine ⟨19740649706005442596529093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13160433137336961731019395 19740649706005442596529093)
              ·
                refine ⟨3701371819876020486849205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19740649706005442596529093 3701371819876020486849205)
                ·
                  refine ⟨347003608113376920642113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3701371819876020486849205 347003608113376920642113)
                  ·
                    rfl

theorem cell22_3041042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_3041042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041042 prefixEnd_3041042 := by exact prefixLift 3041042
  have htrace : WordTrace (prefixWord ++ tailWord_3041042) baseStart_3041042 baseEnd_3041042 := by
    simpa [prefixWord, tailWord_3041042, baseEnd_3041042] using wordTrace_append hprefix tailTrace_3041042
  have hstable : (prefixWord ++ tailWord_3041042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041042).length < 2 ^ (prefixWord ++ tailWord_3041042).sum := by decide
  have hdescent : baseEnd_3041042 < baseStart_3041042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041098 : List Nat := [3, 1, 2, 1, 1, 1, 13]
def baseStart_3041098 : Nat := 118140960795 + 3041098 * 2 ^ 59
def prefixEnd_3041098 : Nat := 4983230072969 + 3 ^ 40 * 3041098 * 2
def baseEnd_3041098 : Nat := 38556666454983899352821

theorem tailTrace_3041098 : CollatzResearch.WordTrace tailWord_3041098 prefixEnd_3041098 38556666454983899352821 := by
  unfold tailWord_3041098
  simp only [CollatzResearch.WordTrace]
  refine ⟨27729489084157199758424987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73945304224419199355799965 27729489084157199758424987)
  ·
    refine ⟨41594233626235799637637481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27729489084157199758424987 41594233626235799637637481)
    ·
      refine ⟨31195675219676849728228111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41594233626235799637637481 31195675219676849728228111)
      ·
        refine ⟨46793512829515274592342167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31195675219676849728228111 46793512829515274592342167)
        ·
          refine ⟨70190269244272911888513251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46793512829515274592342167 70190269244272911888513251)
          ·
            refine ⟨105285403866409367832769877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70190269244272911888513251 105285403866409367832769877)
            ·
              refine ⟨38556666454983899352821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 105285403866409367832769877 38556666454983899352821)
              ·
                rfl

theorem cell22_3041098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 13].length) (baseStart_3041098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041098 prefixEnd_3041098 := by exact prefixLift 3041098
  have htrace : WordTrace (prefixWord ++ tailWord_3041098) baseStart_3041098 baseEnd_3041098 := by
    simpa [prefixWord, tailWord_3041098, baseEnd_3041098] using wordTrace_append hprefix tailTrace_3041098
  have hstable : (prefixWord ++ tailWord_3041098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041098).length < 2 ^ (prefixWord ++ tailWord_3041098).sum := by decide
  have hdescent : baseEnd_3041098 < baseStart_3041098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041119 : List Nat := [1, 1, 2, 3, 1, 5, 3, 1, 2, 3]
def baseStart_3041119 : Nat := 118140960795 + 3041119 * 2 ^ 59
def prefixEnd_3041119 : Nat := 4983230072969 + 3 ^ 40 * 3041119 * 2
def baseEnd_3041119 : Nat := 1041037183013728227751103

theorem tailTrace_3041119 : CollatzResearch.WordTrace tailWord_3041119 prefixEnd_3041119 1041037183013728227751103 := by
  unfold tailWord_3041119
  simp only [CollatzResearch.WordTrace]
  refine ⟨110918722269552719620214411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73945814846368479746809607 110918722269552719620214411)
  ·
    refine ⟨166378083404329079430321617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110918722269552719620214411 166378083404329079430321617)
    ·
      refine ⟨124783562553246809572741213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166378083404329079430321617 124783562553246809572741213)
      ·
        refine ⟨46793835957467553589777955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124783562553246809572741213 46793835957467553589777955)
        ·
          refine ⟨70190753936201330384666933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46793835957467553589777955 70190753936201330384666933)
          ·
            refine ⟨6580383181518874723562525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70190753936201330384666933 6580383181518874723562525)
            ·
              refine ⟨2467643693069578021335947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6580383181518874723562525 2467643693069578021335947)
              ·
                refine ⟨3701465539604367032003921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2467643693069578021335947 3701465539604367032003921)
                ·
                  refine ⟨2776099154703275274002941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3701465539604367032003921 2776099154703275274002941)
                  ·
                    refine ⟨1041037183013728227751103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2776099154703275274002941 1041037183013728227751103)
                    ·
                      rfl

theorem cell22_3041119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 2, 3].length) (baseStart_3041119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041119 prefixEnd_3041119 := by exact prefixLift 3041119
  have htrace : WordTrace (prefixWord ++ tailWord_3041119) baseStart_3041119 baseEnd_3041119 := by
    simpa [prefixWord, tailWord_3041119, baseEnd_3041119] using wordTrace_append hprefix tailTrace_3041119
  have hstable : (prefixWord ++ tailWord_3041119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041119).length < 2 ^ (prefixWord ++ tailWord_3041119).sum := by decide
  have hdescent : baseEnd_3041119 < baseStart_3041119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041132 : List Nat := [2, 2, 1, 1, 4, 4, 2, 6]
def baseStart_3041132 : Nat := 118140960795 + 3041132 * 2 ^ 59
def prefixEnd_3041132 : Nat := 4983230072969 + 3 ^ 40 * 3041132 * 2
def baseEnd_3041132 : Nat := 115671292575488947464007

theorem tailTrace_3041132 : CollatzResearch.WordTrace tailWord_3041132 prefixEnd_3041132 115671292575488947464007 := by
  unfold tailWord_3041132
  simp only [CollatzResearch.WordTrace]
  refine ⟨55459598209252811420218825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73946130945670415226958433 55459598209252811420218825)
  ·
    refine ⟨41594698656939608565164119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55459598209252811420218825 41594698656939608565164119)
    ·
      refine ⟨62392047985409412847746179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41594698656939608565164119 62392047985409412847746179)
      ·
        refine ⟨93588071978114119271619269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62392047985409412847746179 93588071978114119271619269)
        ·
          refine ⟨17547763495896397363428613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93588071978114119271619269 17547763495896397363428613)
          ·
            refine ⟨3290205655480574505642865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17547763495896397363428613 3290205655480574505642865)
            ·
              refine ⟨2467654241610430879232149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3290205655480574505642865 2467654241610430879232149)
              ·
                refine ⟨115671292575488947464007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2467654241610430879232149 115671292575488947464007)
                ·
                  rfl

theorem cell22_3041132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 6].length) (baseStart_3041132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041132 prefixEnd_3041132 := by exact prefixLift 3041132
  have htrace : WordTrace (prefixWord ++ tailWord_3041132) baseStart_3041132 baseEnd_3041132 := by
    simpa [prefixWord, tailWord_3041132, baseEnd_3041132] using wordTrace_append hprefix tailTrace_3041132
  have hstable : (prefixWord ++ tailWord_3041132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041132).length < 2 ^ (prefixWord ++ tailWord_3041132).sum := by decide
  have hdescent : baseEnd_3041132 < baseStart_3041132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041177 : List Nat := [1, 2, 1, 2, 1, 3, 6, 1, 5]
def baseStart_3041177 : Nat := 118140960795 + 3041177 * 2 ^ 59
def prefixEnd_3041177 : Nat := 4983230072969 + 3 ^ 40 * 3041177 * 2
def baseEnd_3041177 : Nat := 347019012533011803266975

theorem tailTrace_3041177 : CollatzResearch.WordTrace tailWord_3041177 prefixEnd_3041177 347019012533011803266975 := by
  unfold tailWord_3041177
  simp only [CollatzResearch.WordTrace]
  refine ⟨110920837703342595525825785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73947225135561730350550523 110920837703342595525825785)
  ·
    refine ⟨83190628277506946644369339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110920837703342595525825785 83190628277506946644369339)
    ·
      refine ⟨124785942416260419966554009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83190628277506946644369339 124785942416260419966554009)
      ·
        refine ⟨93589456812195314974915507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124785942416260419966554009 93589456812195314974915507)
        ·
          refine ⟨140384185218292972462373261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93589456812195314974915507 140384185218292972462373261)
          ·
            refine ⟨52644069456859864673389973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140384185218292972462373261 52644069456859864673389973)
            ·
              refine ⟨2467690755790306156565155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52644069456859864673389973 2467690755790306156565155)
              ·
                refine ⟨3701536133685459234847733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2467690755790306156565155 3701536133685459234847733)
                ·
                  refine ⟨347019012533011803266975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3701536133685459234847733 347019012533011803266975)
                  ·
                    rfl

theorem cell22_3041177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 5].length) (baseStart_3041177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041177 prefixEnd_3041177 := by exact prefixLift 3041177
  have htrace : WordTrace (prefixWord ++ tailWord_3041177) baseStart_3041177 baseEnd_3041177 := by
    simpa [prefixWord, tailWord_3041177, baseEnd_3041177] using wordTrace_append hprefix tailTrace_3041177
  have hstable : (prefixWord ++ tailWord_3041177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041177).length < 2 ^ (prefixWord ++ tailWord_3041177).sum := by decide
  have hdescent : baseEnd_3041177 < baseStart_3041177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041237 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 1, 5]
def baseStart_3041237 : Nat := 118140960795 + 3041237 * 2 ^ 59
def prefixEnd_3041237 : Nat := 4983230072969 + 3 ^ 40 * 3041237 * 2
def baseEnd_3041237 : Nat := 1041077576825215253300741

theorem tailTrace_3041237 : CollatzResearch.WordTrace tailWord_3041237 prefixEnd_3041237 1041077576825215253300741 := by
  unfold tailWord_3041237
  simp only [CollatzResearch.WordTrace]
  refine ⟨110923026083125225773009965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73948684055416817182006643 110923026083125225773009965)
  ·
    refine ⟨41596134781171959664878737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110923026083125225773009965 41596134781171959664878737)
    ·
      refine ⟨31197101085878969748659053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41596134781171959664878737 31197101085878969748659053)
      ·
        refine ⟨11698912907204613655747145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31197101085878969748659053 11698912907204613655747145)
        ·
          refine ⟨8774184680403460241810359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11698912907204613655747145 8774184680403460241810359)
          ·
            refine ⟨13161277020605190362715539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8774184680403460241810359 13161277020605190362715539)
            ·
              refine ⟨19741915530907785544073309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13161277020605190362715539 19741915530907785544073309)
              ·
                refine ⟨7403218324090419579027491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19741915530907785544073309 7403218324090419579027491)
                ·
                  refine ⟨11104827486135629368541237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7403218324090419579027491 11104827486135629368541237)
                  ·
                    refine ⟨1041077576825215253300741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11104827486135629368541237 1041077576825215253300741)
                    ·
                      rfl

theorem cell22_3041237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_3041237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041237 prefixEnd_3041237 := by exact prefixLift 3041237
  have htrace : WordTrace (prefixWord ++ tailWord_3041237) baseStart_3041237 baseEnd_3041237 := by
    simpa [prefixWord, tailWord_3041237, baseEnd_3041237] using wordTrace_append hprefix tailTrace_3041237
  have hstable : (prefixWord ++ tailWord_3041237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041237).length < 2 ^ (prefixWord ++ tailWord_3041237).sum := by decide
  have hdescent : baseEnd_3041237 < baseStart_3041237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041280 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 2, 6]
def baseStart_3041280 : Nat := 118140960795 + 3041280 * 2 ^ 59
def prefixEnd_3041280 : Nat := 4983230072969 + 3 ^ 40 * 3041280 * 2
def baseEnd_3041280 : Nat := 1041092296603977474475609

theorem tailTrace_3041280 : CollatzResearch.WordTrace tailWord_3041280 prefixEnd_3041280 1041092296603977474475609 := by
  unfold tailWord_3041280
  simp only [CollatzResearch.WordTrace]
  refine ⟨55462297210984722058412647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73949729614646296077883529 55462297210984722058412647)
  ·
    refine ⟨83193445816477083087618971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55462297210984722058412647 83193445816477083087618971)
    ·
      refine ⟨124790168724715624631428457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83193445816477083087618971 124790168724715624631428457)
      ·
        refine ⟨93592626543536718473571343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124790168724715624631428457 93592626543536718473571343)
        ·
          refine ⟨140388939815305077710357015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93592626543536718473571343 140388939815305077710357015)
          ·
            refine ⟨210583409722957616565535523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140388939815305077710357015 210583409722957616565535523)
            ·
              refine ⟨315875114584436424848303285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210583409722957616565535523 315875114584436424848303285)
              ·
                refine ⟨29613291992290914829528433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 315875114584436424848303285 29613291992290914829528433)
                ·
                  refine ⟨22209968994218186122146325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29613291992290914829528433 22209968994218186122146325)
                  ·
                    refine ⟨1041092296603977474475609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22209968994218186122146325 1041092296603977474475609)
                    ·
                      rfl

theorem cell22_3041280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_3041280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041280 prefixEnd_3041280 := by exact prefixLift 3041280
  have htrace : WordTrace (prefixWord ++ tailWord_3041280) baseStart_3041280 baseEnd_3041280 := by
    simpa [prefixWord, tailWord_3041280, baseEnd_3041280] using wordTrace_append hprefix tailTrace_3041280
  have hstable : (prefixWord ++ tailWord_3041280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041280).length < 2 ^ (prefixWord ++ tailWord_3041280).sum := by decide
  have hdescent : baseEnd_3041280 < baseStart_3041280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041301 : List Nat := [1, 3, 2, 1, 6, 1, 2, 6]
def baseStart_3041301 : Nat := 118140960795 + 3041301 * 2 ^ 59
def prefixEnd_3041301 : Nat := 4983230072969 + 3 ^ 40 * 3041301 * 2
def baseEnd_3041301 : Nat := 115677720592571157744505

theorem tailTrace_3041301 : CollatzResearch.WordTrace tailWord_3041301 prefixEnd_3041301 115677720592571157744505 := by
  unfold tailWord_3041301
  simp only [CollatzResearch.WordTrace]
  refine ⟨110925360354893364703339757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73950240236595576468893171 110925360354893364703339757)
  ·
    refine ⟨41597010133085011763752409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110925360354893364703339757 41597010133085011763752409)
    ·
      refine ⟨31197757599813758822814307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41597010133085011763752409 31197757599813758822814307)
      ·
        refine ⟨46796636399720638234221461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31197757599813758822814307 46796636399720638234221461)
        ·
          refine ⟨2193592331236904917229131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46796636399720638234221461 2193592331236904917229131)
          ·
            refine ⟨3290388496855357375843697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2193592331236904917229131 3290388496855357375843697)
            ·
              refine ⟨2467791372641518031882773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3290388496855357375843697 2467791372641518031882773)
              ·
                refine ⟨115677720592571157744505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2467791372641518031882773 115677720592571157744505)
                ·
                  rfl

theorem cell22_3041301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 6].length) (baseStart_3041301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041301 prefixEnd_3041301 := by exact prefixLift 3041301
  have htrace : WordTrace (prefixWord ++ tailWord_3041301) baseStart_3041301 baseEnd_3041301 := by
    simpa [prefixWord, tailWord_3041301, baseEnd_3041301] using wordTrace_append hprefix tailTrace_3041301
  have hstable : (prefixWord ++ tailWord_3041301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041301).length < 2 ^ (prefixWord ++ tailWord_3041301).sum := by decide
  have hdescent : baseEnd_3041301 < baseStart_3041301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041376 : List Nat := [2, 1, 1, 3, 2, 4, 3, 1, 1, 4]
def baseStart_3041376 : Nat := 118140960795 + 3041376 * 2 ^ 59
def prefixEnd_3041376 : Nat := 4983230072969 + 3 ^ 40 * 3041376 * 2
def baseEnd_3041376 : Nat := 1041125159365865224075315

theorem tailTrace_3041376 : CollatzResearch.WordTrace tailWord_3041376 prefixEnd_3041376 1041125159365865224075315 := by
  unfold tailWord_3041376
  simp only [CollatzResearch.WordTrace]
  refine ⟨55464047914810826256159991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73952063886414435008213321 55464047914810826256159991)
  ·
    refine ⟨83196071872216239384239987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55464047914810826256159991 83196071872216239384239987)
    ·
      refine ⟨124794107808324359076359981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83196071872216239384239987 124794107808324359076359981)
      ·
        refine ⟨46797790428121634653634993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124794107808324359076359981 46797790428121634653634993)
        ·
          refine ⟨35098342821091225990226245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46797790428121634653634993 35098342821091225990226245)
          ·
            refine ⟨6580939278954604873167421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35098342821091225990226245 6580939278954604873167421)
            ·
              refine ⟨2467852229607976827437783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6580939278954604873167421 2467852229607976827437783)
              ·
                refine ⟨3701778344411965241156675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2467852229607976827437783 3701778344411965241156675)
                ·
                  refine ⟨5552667516617947861735013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3701778344411965241156675 5552667516617947861735013)
                  ·
                    refine ⟨1041125159365865224075315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5552667516617947861735013 1041125159365865224075315)
                    ·
                      rfl

theorem cell22_3041376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 1, 4].length) (baseStart_3041376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041376 prefixEnd_3041376 := by exact prefixLift 3041376
  have htrace : WordTrace (prefixWord ++ tailWord_3041376) baseStart_3041376 baseEnd_3041376 := by
    simpa [prefixWord, tailWord_3041376, baseEnd_3041376] using wordTrace_append hprefix tailTrace_3041376
  have hstable : (prefixWord ++ tailWord_3041376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041376).length < 2 ^ (prefixWord ++ tailWord_3041376).sum := by decide
  have hdescent : baseEnd_3041376 < baseStart_3041376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041391 : List Nat := [1, 1, 2, 1, 3, 4, 4, 2, 4]
def baseStart_3041391 : Nat := 118140960795 + 3041391 * 2 ^ 59
def prefixEnd_3041391 : Nat := 4983230072969 + 3 ^ 40 * 3041391 * 2
def baseEnd_3041391 : Nat := 347043431390803394983423

theorem tailTrace_3041391 : CollatzResearch.WordTrace tailWord_3041391 prefixEnd_3041391 347043431390803394983423 := by
  unfold tailWord_3041391
  simp only [CollatzResearch.WordTrace]
  refine ⟨110928642924567310074116027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73952428616378206716077351 110928642924567310074116027)
  ·
    refine ⟨166392964386850965111174041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110928642924567310074116027 166392964386850965111174041)
    ·
      refine ⟨124794723290138223833380531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166392964386850965111174041 124794723290138223833380531)
      ·
        refine ⟨187192084935207335750070797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124794723290138223833380531 187192084935207335750070797)
        ·
          refine ⟨70197031850702750906276549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187192084935207335750070797 70197031850702750906276549)
          ·
            refine ⟨13161943472006765794926853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70197031850702750906276549 13161943472006765794926853)
            ·
              refine ⟨2467864401001268586548785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13161943472006765794926853 2467864401001268586548785)
              ·
                refine ⟨1850898300750951439911589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2467864401001268586548785 1850898300750951439911589)
                ·
                  refine ⟨347043431390803394983423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1850898300750951439911589 347043431390803394983423)
                  ·
                    rfl

theorem cell22_3041391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 4].length) (baseStart_3041391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041391 prefixEnd_3041391 := by exact prefixLift 3041391
  have htrace : WordTrace (prefixWord ++ tailWord_3041391) baseStart_3041391 baseEnd_3041391 := by
    simpa [prefixWord, tailWord_3041391, baseEnd_3041391] using wordTrace_append hprefix tailTrace_3041391
  have hstable : (prefixWord ++ tailWord_3041391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041391).length < 2 ^ (prefixWord ++ tailWord_3041391).sum := by decide
  have hdescent : baseEnd_3041391 < baseStart_3041391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041554 : List Nat := [3, 2, 4, 13]
def baseStart_3041554 : Nat := 118140960795 + 3041554 * 2 ^ 59
def prefixEnd_3041554 : Nat := 4983230072969 + 3 ^ 40 * 3041554 * 2
def baseEnd_3041554 : Nat := 1428238809881388330761

theorem tailTrace_3041554 : CollatzResearch.WordTrace tailWord_3041554 prefixEnd_3041554 1428238809881388330761 := by
  unfold tailWord_3041554
  simp only [CollatzResearch.WordTrace]
  refine ⟨27733647005744197228074929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73956392015317859274866477 27733647005744197228074929)
  ·
    refine ⟨20800235254308147921056197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27733647005744197228074929 20800235254308147921056197)
    ·
      refine ⟨3900044110182777735198037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20800235254308147921056197 3900044110182777735198037)
      ·
        refine ⟨1428238809881388330761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3900044110182777735198037 1428238809881388330761)
        ·
          rfl

theorem cell22_3041554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 13].length) (baseStart_3041554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041554 prefixEnd_3041554 := by exact prefixLift 3041554
  have htrace : WordTrace (prefixWord ++ tailWord_3041554) baseStart_3041554 baseEnd_3041554 := by
    simpa [prefixWord, tailWord_3041554, baseEnd_3041554] using wordTrace_append hprefix tailTrace_3041554
  have hstable : (prefixWord ++ tailWord_3041554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041554).length < 2 ^ (prefixWord ++ tailWord_3041554).sum := by decide
  have hdescent : baseEnd_3041554 < baseStart_3041554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041588 : List Nat := [2, 5, 1, 1, 1, 3, 3, 6]
def baseStart_3041588 : Nat := 118140960795 + 3041588 * 2 ^ 59
def prefixEnd_3041588 : Nat := 4983230072969 + 3 ^ 40 * 3041588 * 2
def baseEnd_3041588 : Nat := 115688636810929704197185

theorem tailTrace_3041588 : CollatzResearch.WordTrace tailWord_3041588 prefixEnd_3041588 115688636810929704197185 := by
  unfold tailWord_3041588
  simp only [CollatzResearch.WordTrace]
  refine ⟨55467914052426806359518709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73957218736569075146024945 55467914052426806359518709)
  ·
    refine ⟨5200116942415013096204879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55467914052426806359518709 5200116942415013096204879)
    ·
      refine ⟨7800175413622519644307319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5200116942415013096204879 7800175413622519644307319)
      ·
        refine ⟨11700263120433779466460979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7800175413622519644307319 11700263120433779466460979)
        ·
          refine ⟨17550394680650669199691469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11700263120433779466460979 17550394680650669199691469)
          ·
            refine ⟨6581398005244000949884301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17550394680650669199691469 6581398005244000949884301)
            ·
              refine ⟨2468024251966500356206613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6581398005244000949884301 2468024251966500356206613)
              ·
                refine ⟨115688636810929704197185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2468024251966500356206613 115688636810929704197185)
                ·
                  rfl

theorem cell22_3041588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 6].length) (baseStart_3041588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041588 prefixEnd_3041588 := by exact prefixLift 3041588
  have htrace : WordTrace (prefixWord ++ tailWord_3041588) baseStart_3041588 baseEnd_3041588 := by
    simpa [prefixWord, tailWord_3041588, baseEnd_3041588] using wordTrace_append hprefix tailTrace_3041588
  have hstable : (prefixWord ++ tailWord_3041588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041588).length < 2 ^ (prefixWord ++ tailWord_3041588).sum := by decide
  have hdescent : baseEnd_3041588 < baseStart_3041588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041599 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 7]
def baseStart_3041599 : Nat := 118140960795 + 3041599 * 2 ^ 59
def prefixEnd_3041599 : Nat := 4983230072969 + 3 ^ 40 * 3041599 * 2
def baseEnd_3041599 : Nat := 347067165607722325249877

theorem tailTrace_3041599 : CollatzResearch.WordTrace tailWord_3041599 prefixEnd_3041599 347067165607722325249877 := by
  unfold tailWord_3041599
  simp only [CollatzResearch.WordTrace]
  refine ⟨110936229307813761597687851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73957486205209174398458567 110936229307813761597687851)
  ·
    refine ⟨166404343961720642396531777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110936229307813761597687851 166404343961720642396531777)
    ·
      refine ⟨124803257971290481797398833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166404343961720642396531777 124803257971290481797398833)
      ·
        refine ⟨93602443478467861348049125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124803257971290481797398833 93602443478467861348049125)
        ·
          refine ⟨17550458152212724002759211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93602443478467861348049125 17550458152212724002759211)
          ·
            refine ⟨26325687228319086004138817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17550458152212724002759211 26325687228319086004138817)
            ·
              refine ⟨19744265421239314503104113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26325687228319086004138817 19744265421239314503104113)
              ·
                refine ⟨14808199065929485877328085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19744265421239314503104113 14808199065929485877328085)
                ·
                  refine ⟨347067165607722325249877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14808199065929485877328085 347067165607722325249877)
                  ·
                    rfl

theorem cell22_3041599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 7].length) (baseStart_3041599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041599 prefixEnd_3041599 := by exact prefixLift 3041599
  have htrace : WordTrace (prefixWord ++ tailWord_3041599) baseStart_3041599 baseEnd_3041599 := by
    simpa [prefixWord, tailWord_3041599, baseEnd_3041599] using wordTrace_append hprefix tailTrace_3041599
  have hstable : (prefixWord ++ tailWord_3041599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041599).length < 2 ^ (prefixWord ++ tailWord_3041599).sum := by decide
  have hdescent : baseEnd_3041599 < baseStart_3041599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041603 : List Nat := [1, 1, 1, 3, 1, 3, 3, 5, 1, 3]
def baseStart_3041603 : Nat := 118140960795 + 3041603 * 2 ^ 59
def prefixEnd_3041603 : Nat := 4983230072969 + 3 ^ 40 * 3041603 * 2
def baseEnd_3041603 : Nat := 1041202866104912298649619

theorem tailTrace_3041603 : CollatzResearch.WordTrace tailWord_3041603 prefixEnd_3041603 1041202866104912298649619 := by
  unfold tailWord_3041603
  simp only [CollatzResearch.WordTrace]
  refine ⟨110936375199799270280833463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73957583466532846853888975 110936375199799270280833463)
  ·
    refine ⟨166404562799698905421250195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110936375199799270280833463 166404562799698905421250195)
    ·
      refine ⟨249606844199548358131875293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166404562799698905421250195 249606844199548358131875293)
      ·
        refine ⟨93602566574830634299453235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249606844199548358131875293 93602566574830634299453235)
        ·
          refine ⟨140403849862245951449179853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93602566574830634299453235 140403849862245951449179853)
          ·
            refine ⟨52651443698342231793442445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140403849862245951449179853 52651443698342231793442445)
            ·
              refine ⟨19744291386878336922540917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52651443698342231793442445 19744291386878336922540917)
              ·
                refine ⟨1851027317519844086488211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19744291386878336922540917 1851027317519844086488211)
                ·
                  refine ⟨2776540976279766129732317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851027317519844086488211 2776540976279766129732317)
                  ·
                    refine ⟨1041202866104912298649619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2776540976279766129732317 1041202866104912298649619)
                    ·
                      rfl

theorem cell22_3041603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 1, 3].length) (baseStart_3041603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041603 prefixEnd_3041603 := by exact prefixLift 3041603
  have htrace : WordTrace (prefixWord ++ tailWord_3041603) baseStart_3041603 baseEnd_3041603 := by
    simpa [prefixWord, tailWord_3041603, baseEnd_3041603] using wordTrace_append hprefix tailTrace_3041603
  have hstable : (prefixWord ++ tailWord_3041603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041603).length < 2 ^ (prefixWord ++ tailWord_3041603).sum := by decide
  have hdescent : baseEnd_3041603 < baseStart_3041603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041616 : List Nat := [2, 1, 1, 1, 1, 6, 3, 2, 5]
def baseStart_3041616 : Nat := 118140960795 + 3041616 * 2 ^ 59
def prefixEnd_3041616 : Nat := 4983230072969 + 3 ^ 40 * 3041616 * 2
def baseEnd_3041616 : Nat := 347069105423528199358193

theorem tailTrace_3041616 : CollatzResearch.WordTrace tailWord_3041616 prefixEnd_3041616 347069105423528199358193 := by
  unfold tailWord_3041616
  simp only [CollatzResearch.WordTrace]
  refine ⟨55468424674376086750528351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73957899565834782334037801 55468424674376086750528351)
  ·
    refine ⟨83202637011564130125792527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55468424674376086750528351 83202637011564130125792527)
    ·
      refine ⟨124803955517346195188688791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83202637011564130125792527 124803955517346195188688791)
      ·
        refine ⟨187205933276019292783033187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124803955517346195188688791 187205933276019292783033187)
        ·
          refine ⟨280808899914028939174549781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187205933276019292783033187 280808899914028939174549781)
          ·
            refine ⟨13162917183470106523807021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 280808899914028939174549781 13162917183470106523807021)
            ·
              refine ⟨4936093943801289946427633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13162917183470106523807021 4936093943801289946427633)
              ·
                refine ⟨3702070457850967459820725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4936093943801289946427633 3702070457850967459820725)
                ·
                  refine ⟨347069105423528199358193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3702070457850967459820725 347069105423528199358193)
                  ·
                    rfl

theorem cell22_3041616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 5].length) (baseStart_3041616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041616 prefixEnd_3041616 := by exact prefixLift 3041616
  have htrace : WordTrace (prefixWord ++ tailWord_3041616) baseStart_3041616 baseEnd_3041616 := by
    simpa [prefixWord, tailWord_3041616, baseEnd_3041616] using wordTrace_append hprefix tailTrace_3041616
  have hstable : (prefixWord ++ tailWord_3041616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041616).length < 2 ^ (prefixWord ++ tailWord_3041616).sum := by decide
  have hdescent : baseEnd_3041616 < baseStart_3041616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041620 : List Nat := [2, 4, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_3041620 : Nat := 118140960795 + 3041620 * 2 ^ 59
def prefixEnd_3041620 : Nat := 4983230072969 + 3 ^ 40 * 3041620 * 2
def baseEnd_3041620 : Nat := 1041208685552329920974567

theorem tailTrace_3041620 : CollatzResearch.WordTrace tailWord_3041620 prefixEnd_3041620 1041208685552329920974567 := by
  unfold tailWord_3041620
  simp only [CollatzResearch.WordTrace]
  refine ⟨55468497620368841092101157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73957996827158454789468209 55468497620368841092101157)
  ·
    refine ⟨10400343303819157704768967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55468497620368841092101157 10400343303819157704768967)
    ·
      refine ⟨15600514955728736557153451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10400343303819157704768967 15600514955728736557153451)
      ·
        refine ⟨23400772433593104835730177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15600514955728736557153451 23400772433593104835730177)
        ·
          refine ⟨17550579325194828626797633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23400772433593104835730177 17550579325194828626797633)
          ·
            refine ⟨13162934493896121470098225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17550579325194828626797633 13162934493896121470098225)
            ·
              refine ⟨9872200870422091102573669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13162934493896121470098225 9872200870422091102573669)
              ·
                refine ⟨1851037663204142081732563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9872200870422091102573669 1851037663204142081732563)
                ·
                  refine ⟨2776556494806213122598845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851037663204142081732563 2776556494806213122598845)
                  ·
                    refine ⟨1041208685552329920974567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2776556494806213122598845 1041208685552329920974567)
                    ·
                      rfl

theorem cell22_3041620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_3041620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041620 prefixEnd_3041620 := by exact prefixLift 3041620
  have htrace : WordTrace (prefixWord ++ tailWord_3041620) baseStart_3041620 baseEnd_3041620 := by
    simpa [prefixWord, tailWord_3041620, baseEnd_3041620] using wordTrace_append hprefix tailTrace_3041620
  have hstable : (prefixWord ++ tailWord_3041620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041620).length < 2 ^ (prefixWord ++ tailWord_3041620).sum := by decide
  have hdescent : baseEnd_3041620 < baseStart_3041620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041678 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 6]
def baseStart_3041678 : Nat := 118140960795 + 3041678 * 2 ^ 59
def prefixEnd_3041678 : Nat := 4983230072969 + 3 ^ 40 * 3041678 * 2
def baseEnd_3041678 : Nat := 347076180045879034341463

theorem tailTrace_3041678 : CollatzResearch.WordTrace tailWord_3041678 prefixEnd_3041678 347076180045879034341463 := by
  unfold tailWord_3041678
  simp only [CollatzResearch.WordTrace]
  refine ⟨13867388834315944761226711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73959407116351705393209125 13867388834315944761226711)
  ·
    refine ⟨20801083251473917141840067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13867388834315944761226711 20801083251473917141840067)
    ·
      refine ⟨31201624877210875712760101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20801083251473917141840067 31201624877210875712760101)
      ·
        refine ⟨5850304664477039196142519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31201624877210875712760101 5850304664477039196142519)
        ·
          refine ⟨8775456996715558794213779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850304664477039196142519 8775456996715558794213779)
          ·
            refine ⟨13163185495073338191320669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8775456996715558794213779 13163185495073338191320669)
            ·
              refine ⟨4936194560652501821745251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13163185495073338191320669 4936194560652501821745251)
              ·
                refine ⟨7404291840978752732617877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4936194560652501821745251 7404291840978752732617877)
                ·
                  refine ⟨347076180045879034341463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7404291840978752732617877 347076180045879034341463)
                  ·
                    rfl

theorem cell22_3041678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_3041678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041678 prefixEnd_3041678 := by exact prefixLift 3041678
  have htrace : WordTrace (prefixWord ++ tailWord_3041678) baseStart_3041678 baseEnd_3041678 := by
    simpa [prefixWord, tailWord_3041678, baseEnd_3041678] using wordTrace_append hprefix tailTrace_3041678
  have hstable : (prefixWord ++ tailWord_3041678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041678).length < 2 ^ (prefixWord ++ tailWord_3041678).sum := by decide
  have hdescent : baseEnd_3041678 < baseStart_3041678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041697 : List Nat := [1, 2, 3, 5, 1, 2, 1, 2, 1, 4]
def baseStart_3041697 : Nat := 118140960795 + 3041697 * 2 ^ 59
def prefixEnd_3041697 : Nat := 4983230072969 + 3 ^ 40 * 3041697 * 2
def baseEnd_3041697 : Nat := 1041235044225927386799331

theorem tailTrace_3041697 : CollatzResearch.WordTrace tailWord_3041697 prefixEnd_3041697 1041235044225927386799331 := by
  unfold tailWord_3041697
  simp only [CollatzResearch.WordTrace]
  refine ⟨110939803661458724334755345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73959869107639149556503563 110939803661458724334755345)
  ·
    refine ⟨83204852746094043251066509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110939803661458724334755345 83204852746094043251066509)
    ·
      refine ⟨31201819779785266219149941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83204852746094043251066509 31201819779785266219149941)
      ·
        refine ⟨2925170604354868708045307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31201819779785266219149941 2925170604354868708045307)
        ·
          refine ⟨4387755906532303062067961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2925170604354868708045307 4387755906532303062067961)
          ·
            refine ⟨3290816929899227296550971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4387755906532303062067961 3290816929899227296550971)
            ·
              refine ⟨4936225394848840944826457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3290816929899227296550971 4936225394848840944826457)
              ·
                refine ⟨3702169046136630708619843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4936225394848840944826457 3702169046136630708619843)
                ·
                  refine ⟨5553253569204946062929765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702169046136630708619843 5553253569204946062929765)
                  ·
                    refine ⟨1041235044225927386799331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5553253569204946062929765 1041235044225927386799331)
                    ·
                      rfl

theorem cell22_3041697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_3041697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041697 prefixEnd_3041697 := by exact prefixLift 3041697
  have htrace : WordTrace (prefixWord ++ tailWord_3041697) baseStart_3041697 baseEnd_3041697 := by
    simpa [prefixWord, tailWord_3041697, baseEnd_3041697] using wordTrace_append hprefix tailTrace_3041697
  have hstable : (prefixWord ++ tailWord_3041697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041697).length < 2 ^ (prefixWord ++ tailWord_3041697).sum := by decide
  have hdescent : baseEnd_3041697 < baseStart_3041697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041729 : List Nat := [1, 2, 7, 1, 1, 1, 1, 4, 4]
def baseStart_3041729 : Nat := 118140960795 + 3041729 * 2 ^ 59
def prefixEnd_3041729 : Nat := 4983230072969 + 3 ^ 40 * 3041729 * 2
def baseEnd_3041729 : Nat := 347081999493296656666411

theorem tailTrace_3041729 : CollatzResearch.WordTrace tailWord_3041729 prefixEnd_3041729 347081999493296656666411 := by
  unfold tailWord_3041729
  simp only [CollatzResearch.WordTrace]
  refine ⟨110940970797342793799920241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73960647198228529199946827 110940970797342793799920241)
  ·
    refine ⟨83205728098007095349940181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110940970797342793799920241 83205728098007095349940181)
    ·
      refine ⟨1950134252297041297264223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 83205728098007095349940181 1950134252297041297264223)
      ·
        refine ⟨2925201378445561945896335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1950134252297041297264223 2925201378445561945896335)
        ·
          refine ⟨4387802067668342918844503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2925201378445561945896335 4387802067668342918844503)
          ·
            refine ⟨6581703101502514378266755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4387802067668342918844503 6581703101502514378266755)
            ·
              refine ⟨9872554652253771567400133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6581703101502514378266755 9872554652253771567400133)
              ·
                refine ⟨1851103997297582168887525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9872554652253771567400133 1851103997297582168887525)
                ·
                  refine ⟨347081999493296656666411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1851103997297582168887525 347081999493296656666411)
                  ·
                    rfl

theorem cell22_3041729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 4].length) (baseStart_3041729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041729 prefixEnd_3041729 := by exact prefixLift 3041729
  have htrace : WordTrace (prefixWord ++ tailWord_3041729) baseStart_3041729 baseEnd_3041729 := by
    simpa [prefixWord, tailWord_3041729, baseEnd_3041729] using wordTrace_append hprefix tailTrace_3041729
  have hstable : (prefixWord ++ tailWord_3041729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041729).length < 2 ^ (prefixWord ++ tailWord_3041729).sum := by decide
  have hdescent : baseEnd_3041729 < baseStart_3041729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041736 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 2, 6]
def baseStart_3041736 : Nat := 118140960795 + 3041736 * 2 ^ 59
def prefixEnd_3041736 : Nat := 4983230072969 + 3 ^ 40 * 3041736 * 2
def baseEnd_3041736 : Nat := 1041248394722944285074211

theorem tailTrace_3041736 : CollatzResearch.WordTrace tailWord_3041736 prefixEnd_3041736 1041248394722944285074211 := by
  unfold tailWord_3041736
  simp only [CollatzResearch.WordTrace]
  refine ⟨55470613054158716997712531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73960817405544955996950041 55470613054158716997712531)
  ·
    refine ⟨83205919581238075496568797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55470613054158716997712531 83205919581238075496568797)
    ·
      refine ⟨31202219842964278311213299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83205919581238075496568797 31202219842964278311213299)
      ·
        refine ⟨46803329764446417466819949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31202219842964278311213299 46803329764446417466819949)
        ·
          refine ⟨17551248661667406550057481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46803329764446417466819949 17551248661667406550057481)
          ·
            refine ⟨13163436496250554912543111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17551248661667406550057481 13163436496250554912543111)
            ·
              refine ⟨19745154744375832368814667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13163436496250554912543111 19745154744375832368814667)
              ·
                refine ⟨29617732116563748553222001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19745154744375832368814667 29617732116563748553222001)
                ·
                  refine ⟨22213299087422811414916501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29617732116563748553222001 22213299087422811414916501)
                  ·
                    refine ⟨1041248394722944285074211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22213299087422811414916501 1041248394722944285074211)
                    ·
                      rfl

theorem cell22_3041736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_3041736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041736 prefixEnd_3041736 := by exact prefixLift 3041736
  have htrace : WordTrace (prefixWord ++ tailWord_3041736) baseStart_3041736 baseEnd_3041736 := by
    simpa [prefixWord, tailWord_3041736, baseEnd_3041736] using wordTrace_append hprefix tailTrace_3041736
  have hstable : (prefixWord ++ tailWord_3041736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041736).length < 2 ^ (prefixWord ++ tailWord_3041736).sum := by decide
  have hdescent : baseEnd_3041736 < baseStart_3041736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041738 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 3, 3]
def baseStart_3041738 : Nat := 118140960795 + 3041738 * 2 ^ 59
def prefixEnd_3041738 : Nat := 4983230072969 + 3 ^ 40 * 3041738 * 2
def baseEnd_3041738 : Nat := 1041249079363816946524205

theorem tailTrace_3041738 : CollatzResearch.WordTrace tailWord_3041738 prefixEnd_3041738 1041249079363816946524205 := by
  unfold tailWord_3041738
  simp only [CollatzResearch.WordTrace]
  refine ⟨27735324763577547084249467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73960866036206792224665245 27735324763577547084249467)
  ·
    refine ⟨41602987145366320626374201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27735324763577547084249467 41602987145366320626374201)
    ·
      refine ⟨31202240359024740469780651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41602987145366320626374201 31202240359024740469780651)
      ·
        refine ⟨46803360538537110704670977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31202240359024740469780651 46803360538537110704670977)
        ·
          refine ⟨35102520403902833028503233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46803360538537110704670977 35102520403902833028503233)
          ·
            refine ⟨26326890302927124771377425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35102520403902833028503233 26326890302927124771377425)
            ·
              refine ⟨19745167727195343578533069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26326890302927124771377425 19745167727195343578533069)
              ·
                refine ⟨7404437897698253841949901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19745167727195343578533069 7404437897698253841949901)
                ·
                  refine ⟨2776664211636845190731213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7404437897698253841949901 2776664211636845190731213)
                  ·
                    refine ⟨1041249079363816946524205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2776664211636845190731213 1041249079363816946524205)
                    ·
                      rfl

theorem cell22_3041738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_3041738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041738 prefixEnd_3041738 := by exact prefixLift 3041738
  have htrace : WordTrace (prefixWord ++ tailWord_3041738) baseStart_3041738 baseEnd_3041738 := by
    simpa [prefixWord, tailWord_3041738, baseEnd_3041738] using wordTrace_append hprefix tailTrace_3041738
  have hstable : (prefixWord ++ tailWord_3041738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041738).length < 2 ^ (prefixWord ++ tailWord_3041738).sum := by decide
  have hdescent : baseEnd_3041738 < baseStart_3041738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041740 : List Nat := [2, 2, 1, 4, 4, 1, 1, 7]
def baseStart_3041740 : Nat := 118140960795 + 3041740 * 2 ^ 59
def prefixEnd_3041740 : Nat := 4983230072969 + 3 ^ 40 * 3041740 * 2
def baseEnd_3041740 : Nat := 115694418222743289774911

theorem tailTrace_3041740 : CollatzResearch.WordTrace tailWord_3041740 prefixEnd_3041740 115694418222743289774911 := by
  unfold tailWord_3041740
  simp only [CollatzResearch.WordTrace]
  refine ⟨55470686000151471339285337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73960914666868628452380449 55470686000151471339285337)
  ·
    refine ⟨41603014500113603504464003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55470686000151471339285337 41603014500113603504464003)
    ·
      refine ⟨62404521750170405256696005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41603014500113603504464003 62404521750170405256696005)
      ·
        refine ⟨11700847828156950985630501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62404521750170405256696005 11700847828156950985630501)
        ·
          refine ⟨2193908967779428309805719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11700847828156950985630501 2193908967779428309805719)
          ·
            refine ⟨3290863451669142464708579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2193908967779428309805719 3290863451669142464708579)
            ·
              refine ⟨4936295177503713697062869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3290863451669142464708579 4936295177503713697062869)
              ·
                refine ⟨115694418222743289774911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4936295177503713697062869 115694418222743289774911)
                ·
                  rfl

theorem cell22_3041740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 7].length) (baseStart_3041740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041740 prefixEnd_3041740 := by exact prefixLift 3041740
  have htrace : WordTrace (prefixWord ++ tailWord_3041740) baseStart_3041740 baseEnd_3041740 := by
    simpa [prefixWord, tailWord_3041740, baseEnd_3041740] using wordTrace_append hprefix tailTrace_3041740
  have hstable : (prefixWord ++ tailWord_3041740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041740).length < 2 ^ (prefixWord ++ tailWord_3041740).sum := by decide
  have hdescent : baseEnd_3041740 < baseStart_3041740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041841 : List Nat := [1, 2, 2, 3, 1, 1, 12]
def baseStart_3041841 : Nat := 118140960795 + 3041841 * 2 ^ 59
def prefixEnd_3041841 : Nat := 4983230072969 + 3 ^ 40 * 3041841 * 2
def baseEnd_3041841 : Nat := 38566086606250333748107

theorem tailTrace_3041841 : CollatzResearch.WordTrace tailWord_3041841 prefixEnd_3041841 38566086606250333748107 := by
  unfold tailWord_3041841
  simp only [CollatzResearch.WordTrace]
  refine ⟨110945055772937036927997377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73963370515291357951998251 110945055772937036927997377)
  ·
    refine ⟨83208791829702777695998033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110945055772937036927997377 83208791829702777695998033)
    ·
      refine ⟨62406593872277083271998525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83208791829702777695998033 62406593872277083271998525)
      ·
        refine ⟨23402472702103906226999447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62406593872277083271998525 23402472702103906226999447)
        ·
          refine ⟨35103709053155859340499171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23402472702103906226999447 35103709053155859340499171)
          ·
            refine ⟨52655563579733789010748757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35103709053155859340499171 52655563579733789010748757)
            ·
              refine ⟨38566086606250333748107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 52655563579733789010748757 38566086606250333748107)
              ·
                rfl

theorem cell22_3041841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 12].length) (baseStart_3041841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041841 prefixEnd_3041841 := by exact prefixLift 3041841
  have htrace : WordTrace (prefixWord ++ tailWord_3041841) baseStart_3041841 baseEnd_3041841 := by
    simpa [prefixWord, tailWord_3041841, baseEnd_3041841] using wordTrace_append hprefix tailTrace_3041841
  have hstable : (prefixWord ++ tailWord_3041841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041841).length < 2 ^ (prefixWord ++ tailWord_3041841).sum := by decide
  have hdescent : baseEnd_3041841 < baseStart_3041841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041843 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 2, 4]
def baseStart_3041843 : Nat := 118140960795 + 3041843 * 2 ^ 59
def prefixEnd_3041843 : Nat := 4983230072969 + 3 ^ 40 * 3041843 * 2
def baseEnd_3041843 : Nat := 1041285023009631672648883

theorem tailTrace_3041843 : CollatzResearch.WordTrace tailWord_3041843 prefixEnd_3041843 1041285023009631672648883 := by
  unfold tailWord_3041843
  simp only [CollatzResearch.WordTrace]
  refine ⟨110945128718929791269570183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73963419145953194179713455 110945128718929791269570183)
  ·
    refine ⟨166417693078394686904355275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110945128718929791269570183 166417693078394686904355275)
    ·
      refine ⟨249626539617592030356532913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166417693078394686904355275 249626539617592030356532913)
      ·
        refine ⟨187219904713194022767399685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249626539617592030356532913 187219904713194022767399685)
        ·
          refine ⟨35103732133723879268887441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187219904713194022767399685 35103732133723879268887441)
          ·
            refine ⟨26327799100292909451665581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35103732133723879268887441 26327799100292909451665581)
            ·
              refine ⟨9872924662609841044374593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26327799100292909451665581 9872924662609841044374593)
              ·
                refine ⟨7404693496957380783280945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9872924662609841044374593 7404693496957380783280945)
                ·
                  refine ⟨5553520122718035587460709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7404693496957380783280945 5553520122718035587460709)
                  ·
                    refine ⟨1041285023009631672648883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5553520122718035587460709 1041285023009631672648883)
                    ·
                      rfl

theorem cell22_3041843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 4].length) (baseStart_3041843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041843 prefixEnd_3041843 := by exact prefixLift 3041843
  have htrace : WordTrace (prefixWord ++ tailWord_3041843) baseStart_3041843 baseEnd_3041843 := by
    simpa [prefixWord, tailWord_3041843, baseEnd_3041843] using wordTrace_append hprefix tailTrace_3041843
  have hstable : (prefixWord ++ tailWord_3041843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041843).length < 2 ^ (prefixWord ++ tailWord_3041843).sum := by decide
  have hdescent : baseEnd_3041843 < baseStart_3041843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041845 : List Nat := [1, 3, 3, 1, 1, 2, 2, 4, 2, 3]
def baseStart_3041845 : Nat := 118140960795 + 3041845 * 2 ^ 59
def prefixEnd_3041845 : Nat := 4983230072969 + 3 ^ 40 * 3041845 * 2
def baseEnd_3041845 : Nat := 1041285707650504334098877

theorem tailTrace_3041845 : CollatzResearch.WordTrace tailWord_3041845 prefixEnd_3041845 1041285707650504334098877 := by
  unfold tailWord_3041845
  simp only [CollatzResearch.WordTrace]
  refine ⟨110945201664922545611142989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73963467776615030407428659 110945201664922545611142989)
  ·
    refine ⟨41604450624345954604178621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110945201664922545611142989 41604450624345954604178621)
    ·
      refine ⟨15601668984129732976566983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41604450624345954604178621 15601668984129732976566983)
      ·
        refine ⟨23402503476194599464850475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15601668984129732976566983 23402503476194599464850475)
        ·
          refine ⟨35103755214291899197275713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23402503476194599464850475 35103755214291899197275713)
          ·
            refine ⟨26327816410718924397956785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35103755214291899197275713 26327816410718924397956785)
            ·
              refine ⟨19745862308039193298467589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26327816410718924397956785 19745862308039193298467589)
              ·
                refine ⟨3702349182757348743462673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19745862308039193298467589 3702349182757348743462673)
                ·
                  refine ⟨2776761887068011557597005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3702349182757348743462673 2776761887068011557597005)
                  ·
                    refine ⟨1041285707650504334098877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2776761887068011557597005 1041285707650504334098877)
                    ·
                      rfl

theorem cell22_3041845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_3041845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041845 prefixEnd_3041845 := by exact prefixLift 3041845
  have htrace : WordTrace (prefixWord ++ tailWord_3041845) baseStart_3041845 baseEnd_3041845 := by
    simpa [prefixWord, tailWord_3041845, baseEnd_3041845] using wordTrace_append hprefix tailTrace_3041845
  have hstable : (prefixWord ++ tailWord_3041845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041845).length < 2 ^ (prefixWord ++ tailWord_3041845).sum := by decide
  have hdescent : baseEnd_3041845 < baseStart_3041845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041903 : List Nat := [1, 1, 2, 1, 3, 2, 3, 4, 5]
def baseStart_3041903 : Nat := 118140960795 + 3041903 * 2 ^ 59
def prefixEnd_3041903 : Nat := 4983230072969 + 3 ^ 40 * 3041903 * 2
def baseEnd_3041903 : Nat := 347101854078603838716233

theorem tailTrace_3041903 : CollatzResearch.WordTrace tailWord_3041903 prefixEnd_3041903 347101854078603838716233 := by
  unfold tailWord_3041903
  simp only [CollatzResearch.WordTrace]
  refine ⟨110947317098712421516754363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73964878065808281011169575 110947317098712421516754363)
  ·
    refine ⟨166420975648068632275131545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110947317098712421516754363 166420975648068632275131545)
    ·
      refine ⟨124815731736051474206348659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166420975648068632275131545 124815731736051474206348659)
      ·
        refine ⟨187223597604077211309522989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124815731736051474206348659 187223597604077211309522989)
        ·
          refine ⟨70208849101528954241071121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187223597604077211309522989 70208849101528954241071121)
          ·
            refine ⟨52656636826146715680803341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70208849101528954241071121 52656636826146715680803341)
            ·
              refine ⟨19746238809805018380301253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52656636826146715680803341 19746238809805018380301253)
              ·
                refine ⟨3702419776838440946306485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19746238809805018380301253 3702419776838440946306485)
                ·
                  refine ⟨347101854078603838716233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3702419776838440946306485 347101854078603838716233)
                  ·
                    rfl

theorem cell22_3041903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 5].length) (baseStart_3041903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041903 prefixEnd_3041903 := by exact prefixLift 3041903
  have htrace : WordTrace (prefixWord ++ tailWord_3041903) baseStart_3041903 baseEnd_3041903 := by
    simpa [prefixWord, tailWord_3041903, baseEnd_3041903] using wordTrace_append hprefix tailTrace_3041903
  have hstable : (prefixWord ++ tailWord_3041903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041903).length < 2 ^ (prefixWord ++ tailWord_3041903).sum := by decide
  have hdescent : baseEnd_3041903 < baseStart_3041903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041965 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 6]
def baseStart_3041965 : Nat := 118140960795 + 3041965 * 2 ^ 59
def prefixEnd_3041965 : Nat := 4983230072969 + 3 ^ 40 * 3041965 * 2
def baseEnd_3041965 : Nat := 347108928700954673699503

theorem tailTrace_3041965 : CollatzResearch.WordTrace tailWord_3041965 prefixEnd_3041965 347108928700954673699503 := by
  unfold tailWord_3041965
  simp only [CollatzResearch.WordTrace]
  refine ⟨110949578424487806105511349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73966385616325204070340899 110949578424487806105511349)
  ·
    refine ⟨10401522977295731822391689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110949578424487806105511349 10401522977295731822391689)
    ·
      refine ⟨7801142232971798866793767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10401522977295731822391689 7801142232971798866793767)
      ·
        refine ⟨11701713349457698300190651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7801142232971798866793767 11701713349457698300190651)
        ·
          refine ⟨17552570024186547450285977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11701713349457698300190651 17552570024186547450285977)
          ·
            refine ⟨13164427518139910587714483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17552570024186547450285977 13164427518139910587714483)
            ·
              refine ⟨19746641277209865881571725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13164427518139910587714483 19746641277209865881571725)
              ·
                refine ⟨7404990478953699705589397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19746641277209865881571725 7404990478953699705589397)
                ·
                  refine ⟨347108928700954673699503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7404990478953699705589397 347108928700954673699503)
                  ·
                    rfl

theorem cell22_3041965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_3041965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041965 prefixEnd_3041965 := by exact prefixLift 3041965
  have htrace : WordTrace (prefixWord ++ tailWord_3041965) baseStart_3041965 baseEnd_3041965 := by
    simpa [prefixWord, tailWord_3041965, baseEnd_3041965] using wordTrace_append hprefix tailTrace_3041965
  have hstable : (prefixWord ++ tailWord_3041965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041965).length < 2 ^ (prefixWord ++ tailWord_3041965).sum := by decide
  have hdescent : baseEnd_3041965 < baseStart_3041965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3041978 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 3, 6]
def baseStart_3041978 : Nat := 118140960795 + 3041978 * 2 ^ 59
def prefixEnd_3041978 : Nat := 4983230072969 + 3 ^ 40 * 3041978 * 2
def baseEnd_3041978 : Nat := 1041331236268536320523469

theorem tailTrace_3041978 : CollatzResearch.WordTrace tailWord_3041978 prefixEnd_3041978 1041331236268536320523469 := by
  unfold tailWord_3041978
  simp only [CollatzResearch.WordTrace]
  refine ⟨27737513143360177331433647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73966701715627139550489725 27737513143360177331433647)
  ·
    refine ⟨41606269715040265997150471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27737513143360177331433647 41606269715040265997150471)
    ·
      refine ⟨62409404572560398995725707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41606269715040265997150471 62409404572560398995725707)
      ·
        refine ⟨93614106858840598493588561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62409404572560398995725707 93614106858840598493588561)
        ·
          refine ⟨70210580144130448870191421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93614106858840598493588561 70210580144130448870191421)
          ·
            refine ⟨26328967554048918326321783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70210580144130448870191421 26328967554048918326321783)
            ·
              refine ⟨39493451331073377489482675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26328967554048918326321783 39493451331073377489482675)
              ·
                refine ⟨59240176996610066234224013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39493451331073377489482675 59240176996610066234224013)
                ·
                  refine ⟨22215066373728774837834005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59240176996610066234224013 22215066373728774837834005)
                  ·
                    refine ⟨1041331236268536320523469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22215066373728774837834005 1041331236268536320523469)
                    ·
                      rfl

theorem cell22_3041978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_3041978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3041978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3041978 prefixEnd_3041978 := by exact prefixLift 3041978
  have htrace : WordTrace (prefixWord ++ tailWord_3041978) baseStart_3041978 baseEnd_3041978 := by
    simpa [prefixWord, tailWord_3041978, baseEnd_3041978] using wordTrace_append hprefix tailTrace_3041978
  have hstable : (prefixWord ++ tailWord_3041978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3041978).length < 2 ^ (prefixWord ++ tailWord_3041978).sum := by decide
  have hdescent : baseEnd_3041978 < baseStart_3041978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3041978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
