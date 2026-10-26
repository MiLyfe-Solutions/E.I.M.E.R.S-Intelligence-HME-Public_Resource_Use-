import V185TrunkScan22Chunk284

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2542802 : List Nat := [3, 2, 2, 2, 1, 1, 2, 5, 4]
def baseStart_2542802 : Nat := 118140960795 + 2542802 * 2 ^ 59
def prefixEnd_2542802 : Nat := 4983230072969 + 3 ^ 40 * 2542802 * 2
def baseEnd_2542802 : Nat := 290151030047570113151305

theorem tailTrace_2542802 : CollatzResearch.WordTrace tailWord_2542802 prefixEnd_2542802 290151030047570113151305 := by
  unfold tailWord_2542802
  simp only [CollatzResearch.WordTrace]
  refine ⟨23185902033467526213057665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61829072089246736568153773 23185902033467526213057665)
  ·
    refine ⟨17389426525100644659793249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23185902033467526213057665 17389426525100644659793249)
    ·
      refine ⟨13042069893825483494844937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17389426525100644659793249 13042069893825483494844937)
      ·
        refine ⟨9781552420369112621133703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13042069893825483494844937 9781552420369112621133703)
        ·
          refine ⟨14672328630553668931700555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9781552420369112621133703 14672328630553668931700555)
          ·
            refine ⟨22008492945830503397550833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14672328630553668931700555 22008492945830503397550833)
            ·
              refine ⟨16506369709372877548163125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22008492945830503397550833 16506369709372877548163125)
              ·
                refine ⟨1547472160253707270140293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16506369709372877548163125 1547472160253707270140293)
                ·
                  refine ⟨290151030047570113151305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1547472160253707270140293 290151030047570113151305)
                  ·
                    rfl

theorem cell22_2542802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_2542802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542802 prefixEnd_2542802 := by exact prefixLift 2542802
  have htrace : WordTrace (prefixWord ++ tailWord_2542802) baseStart_2542802 baseEnd_2542802 := by
    simpa [prefixWord, tailWord_2542802, baseEnd_2542802] using wordTrace_append hprefix tailTrace_2542802
  have hstable : (prefixWord ++ tailWord_2542802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542802).length < 2 ^ (prefixWord ++ tailWord_2542802).sum := by decide
  have hdescent : baseEnd_2542802 < baseStart_2542802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542815 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 2, 4]
def baseStart_2542815 : Nat := 118140960795 + 2542815 * 2 ^ 59
def prefixEnd_2542815 : Nat := 4983230072969 + 3 ^ 40 * 2542815 * 2
def baseEnd_2542815 : Nat := 870457540308382638878875

theorem tailTrace_2542815 : CollatzResearch.WordTrace tailWord_2542815 prefixEnd_2542815 870457540308382638878875 := by
  unfold tailWord_2542815
  simp only [CollatzResearch.WordTrace]
  refine ⟨92744082282823008072453899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61829388188548672048302599 92744082282823008072453899)
  ·
    refine ⟨139116123424234512108680849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92744082282823008072453899 139116123424234512108680849)
    ·
      refine ⟨104337092568175884081510637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139116123424234512108680849 104337092568175884081510637)
      ·
        refine ⟨39126409713065956530566489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104337092568175884081510637 39126409713065956530566489)
        ·
          refine ⟨29344807284799467397924867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39126409713065956530566489 29344807284799467397924867)
          ·
            refine ⟨44017210927199201096887301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29344807284799467397924867 44017210927199201096887301)
            ·
              refine ⟨8253227048849850205666369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44017210927199201096887301 8253227048849850205666369)
              ·
                refine ⟨6189920286637387654249777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8253227048849850205666369 6189920286637387654249777)
                ·
                  refine ⟨4642440214978040740687333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6189920286637387654249777 4642440214978040740687333)
                  ·
                    refine ⟨870457540308382638878875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4642440214978040740687333 870457540308382638878875)
                    ·
                      rfl

theorem cell22_2542815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_2542815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542815 prefixEnd_2542815 := by exact prefixLift 2542815
  have htrace : WordTrace (prefixWord ++ tailWord_2542815) baseStart_2542815 baseEnd_2542815 := by
    simpa [prefixWord, tailWord_2542815, baseEnd_2542815] using wordTrace_append hprefix tailTrace_2542815
  have hstable : (prefixWord ++ tailWord_2542815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542815).length < 2 ^ (prefixWord ++ tailWord_2542815).sum := by decide
  have hdescent : baseEnd_2542815 < baseStart_2542815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542817 : List Nat := [1, 2, 3, 1, 3, 2, 1, 4, 2, 3]
def baseStart_2542817 : Nat := 118140960795 + 2542817 * 2 ^ 59
def prefixEnd_2542817 : Nat := 4983230072969 + 3 ^ 40 * 2542817 * 2
def baseEnd_2542817 : Nat := 870458224949255300328869

theorem tailTrace_2542817 : CollatzResearch.WordTrace tailWord_2542817 prefixEnd_2542817 870458224949255300328869 := by
  unfold tailWord_2542817
  simp only [CollatzResearch.WordTrace]
  refine ⟨92744155228815762414026705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61829436819210508276017803 92744155228815762414026705)
  ·
    refine ⟨69558116421611821810520029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92744155228815762414026705 69558116421611821810520029)
    ·
      refine ⟨26084293658104433178945011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69558116421611821810520029 26084293658104433178945011)
      ·
        refine ⟨39126440487156649768417517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26084293658104433178945011 39126440487156649768417517)
        ·
          refine ⟨14672415182683743663156569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39126440487156649768417517 14672415182683743663156569)
          ·
            refine ⟨11004311387012807747367427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14672415182683743663156569 11004311387012807747367427)
            ·
              refine ⟨16506467080519211621051141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11004311387012807747367427 16506467080519211621051141)
              ·
                refine ⟨3094962577597352178947089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16506467080519211621051141 3094962577597352178947089)
                ·
                  refine ⟨2321221933198014134210317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3094962577597352178947089 2321221933198014134210317)
                  ·
                    refine ⟨870458224949255300328869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2321221933198014134210317 870458224949255300328869)
                    ·
                      rfl

theorem cell22_2542817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_2542817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542817 prefixEnd_2542817 := by exact prefixLift 2542817
  have htrace : WordTrace (prefixWord ++ tailWord_2542817) baseStart_2542817 baseEnd_2542817 := by
    simpa [prefixWord, tailWord_2542817, baseEnd_2542817] using wordTrace_append hprefix tailTrace_2542817
  have hstable : (prefixWord ++ tailWord_2542817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542817).length < 2 ^ (prefixWord ++ tailWord_2542817).sum := by decide
  have hdescent : baseEnd_2542817 < baseStart_2542817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542830 : List Nat := [4, 1, 2, 1, 1, 1, 5, 7]
def baseStart_2542830 : Nat := 118140960795 + 2542830 * 2 ^ 59
def prefixEnd_2542830 : Nat := 4983230072969 + 3 ^ 40 * 2542830 * 2
def baseEnd_2542830 : Nat := 96718075012769733305981

theorem tailTrace_2542830 : CollatzResearch.WordTrace tailWord_2542830 prefixEnd_2542830 96718075012769733305981 := by
  unfold tailWord_2542830
  simp only [CollatzResearch.WordTrace]
  refine ⟨11593078672221083204281243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61829752918512443756166629 11593078672221083204281243)
  ·
    refine ⟨17389618008331624806421865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11593078672221083204281243 17389618008331624806421865)
    ·
      refine ⟨13042213506248718604816399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17389618008331624806421865 13042213506248718604816399)
      ·
        refine ⟨19563320259373077907224599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13042213506248718604816399 19563320259373077907224599)
        ·
          refine ⟨29344980389059616860836899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19563320259373077907224599 29344980389059616860836899)
          ·
            refine ⟨44017470583589425291255349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29344980389059616860836899 44017470583589425291255349)
            ·
              refine ⟨4126637867211508621055189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44017470583589425291255349 4126637867211508621055189)
              ·
                refine ⟨96718075012769733305981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4126637867211508621055189 96718075012769733305981)
                ·
                  rfl

theorem cell22_2542830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_2542830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542830 prefixEnd_2542830 := by exact prefixLift 2542830
  have htrace : WordTrace (prefixWord ++ tailWord_2542830) baseStart_2542830 baseEnd_2542830 := by
    simpa [prefixWord, tailWord_2542830, baseEnd_2542830] using wordTrace_append hprefix tailTrace_2542830
  have hstable : (prefixWord ++ tailWord_2542830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542830).length < 2 ^ (prefixWord ++ tailWord_2542830).sum := by decide
  have hdescent : baseEnd_2542830 < baseStart_2542830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542836 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 6]
def baseStart_2542836 : Nat := 118140960795 + 2542836 * 2 ^ 59
def prefixEnd_2542836 : Nat := 4983230072969 + 3 ^ 40 * 2542836 * 2
def baseEnd_2542836 : Nat := 290154909679181861367937

theorem tailTrace_2542836 : CollatzResearch.WordTrace tailWord_2542836 prefixEnd_2542836 290154909679181861367937 := by
  unfold tailWord_2542836
  simp only [CollatzResearch.WordTrace]
  refine ⟨46372424107873464329484181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61829898810497952439312241 46372424107873464329484181)
  ·
    refine ⟨2173707380056568640444571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46372424107873464329484181 2173707380056568640444571)
    ·
      refine ⟨3260561070084852960666857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2173707380056568640444571 3260561070084852960666857)
      ·
        refine ⟨2445420802563639720500143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3260561070084852960666857 2445420802563639720500143)
        ·
          refine ⟨3668131203845459580750215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2445420802563639720500143 3668131203845459580750215)
          ·
            refine ⟨5502196805768189371125323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3668131203845459580750215 5502196805768189371125323)
            ·
              refine ⟨8253295208652284056687985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5502196805768189371125323 8253295208652284056687985)
              ·
                refine ⟨6189971406489213042515989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8253295208652284056687985 6189971406489213042515989)
                ·
                  refine ⟨290154909679181861367937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6189971406489213042515989 290154909679181861367937)
                  ·
                    rfl

theorem cell22_2542836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_2542836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542836 prefixEnd_2542836 := by exact prefixLift 2542836
  have htrace : WordTrace (prefixWord ++ tailWord_2542836) baseStart_2542836 baseEnd_2542836 := by
    simpa [prefixWord, tailWord_2542836, baseEnd_2542836] using wordTrace_append hprefix tailTrace_2542836
  have hstable : (prefixWord ++ tailWord_2542836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542836).length < 2 ^ (prefixWord ++ tailWord_2542836).sum := by decide
  have hdescent : baseEnd_2542836 < baseStart_2542836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542879 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 3, 3]
def baseStart_2542879 : Nat := 118140960795 + 2542879 * 2 ^ 59
def prefixEnd_2542879 : Nat := 4983230072969 + 3 ^ 40 * 2542879 * 2
def baseEnd_2542879 : Nat := 870479448816307805278679

theorem tailTrace_2542879 : CollatzResearch.WordTrace tailWord_2542879 prefixEnd_2542879 870479448816307805278679 := by
  unfold tailWord_2542879
  simp only [CollatzResearch.WordTrace]
  refine ⟨92746416554591147002783691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61830944369727431335189127 92746416554591147002783691)
  ·
    refine ⟨139119624831886720504175537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92746416554591147002783691 139119624831886720504175537)
    ·
      refine ⟨104339718623915040378131653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139119624831886720504175537 104339718623915040378131653)
      ·
        refine ⟨19563697241984070070899685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104339718623915040378131653 19563697241984070070899685)
        ·
          refine ⟨3668193232872013138293691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19563697241984070070899685 3668193232872013138293691)
          ·
            refine ⟨5502289849308019707440537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3668193232872013138293691 5502289849308019707440537)
            ·
              refine ⟨4126717386981014780580403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5502289849308019707440537 4126717386981014780580403)
              ·
                refine ⟨6190076080471522170870605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4126717386981014780580403 6190076080471522170870605)
                ·
                  refine ⟨2321278530176820814076477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6190076080471522170870605 2321278530176820814076477)
                  ·
                    refine ⟨870479448816307805278679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2321278530176820814076477 870479448816307805278679)
                    ·
                      rfl

theorem cell22_2542879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 3].length) (baseStart_2542879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542879 prefixEnd_2542879 := by exact prefixLift 2542879
  have htrace : WordTrace (prefixWord ++ tailWord_2542879) baseStart_2542879 baseEnd_2542879 := by
    simpa [prefixWord, tailWord_2542879, baseEnd_2542879] using wordTrace_append hprefix tailTrace_2542879
  have hstable : (prefixWord ++ tailWord_2542879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542879).length < 2 ^ (prefixWord ++ tailWord_2542879).sum := by decide
  have hdescent : baseEnd_2542879 < baseStart_2542879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542913 : List Nat := [1, 2, 5, 2, 1, 3, 1, 3, 1, 3]
def baseStart_2542913 : Nat := 118140960795 + 2542913 * 2 ^ 59
def prefixEnd_2542913 : Nat := 4983230072969 + 3 ^ 40 * 2542913 * 2
def baseEnd_2542913 : Nat := 870491087711143049928575

theorem tailTrace_2542913 : CollatzResearch.WordTrace tailWord_2542913 prefixEnd_2542913 870491087711143049928575 := by
  unfold tailWord_2542913
  simp only [CollatzResearch.WordTrace]
  refine ⟨92747656636467970809521393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61831771090978647206347595 92747656636467970809521393)
  ·
    refine ⟨69560742477350978107141045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92747656636467970809521393 69560742477350978107141045)
    ·
      refine ⟨6521319607251654197544473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69560742477350978107141045 6521319607251654197544473)
      ·
        refine ⟨4890989705438740648158355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6521319607251654197544473 4890989705438740648158355)
        ·
          refine ⟨7336484558158110972237533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4890989705438740648158355 7336484558158110972237533)
          ·
            refine ⟨2751181709309291614589075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7336484558158110972237533 2751181709309291614589075)
            ·
              refine ⟨4126772563963937421883613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2751181709309291614589075 4126772563963937421883613)
              ·
                refine ⟨1547539711486476533206355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4126772563963937421883613 1547539711486476533206355)
                ·
                  refine ⟨2321309567229714799809533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547539711486476533206355 2321309567229714799809533)
                  ·
                    refine ⟨870491087711143049928575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2321309567229714799809533 870491087711143049928575)
                    ·
                      rfl

theorem cell22_2542913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_2542913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542913 prefixEnd_2542913 := by exact prefixLift 2542913
  have htrace : WordTrace (prefixWord ++ tailWord_2542913) baseStart_2542913 baseEnd_2542913 := by
    simpa [prefixWord, tailWord_2542913, baseEnd_2542913] using wordTrace_append hprefix tailTrace_2542913
  have hstable : (prefixWord ++ tailWord_2542913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542913).length < 2 ^ (prefixWord ++ tailWord_2542913).sum := by decide
  have hdescent : baseEnd_2542913 < baseStart_2542913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542937 : List Nat := [1, 2, 1, 2, 2, 2, 2, 6, 4]
def baseStart_2542937 : Nat := 118140960795 + 2542937 * 2 ^ 59
def prefixEnd_2542937 : Nat := 4983230072969 + 3 ^ 40 * 2542937 * 2
def baseEnd_2542937 : Nat := 290166434467204995776167

theorem tailTrace_2542937 : CollatzResearch.WordTrace tailWord_2542937 prefixEnd_2542937 290166434467204995776167 := by
  unfold tailWord_2542937
  simp only [CollatzResearch.WordTrace]
  refine ⟨92748531988381022908395065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61832354658920681938930043 92748531988381022908395065)
  ·
    refine ⟨69561398991285767181296299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92748531988381022908395065 69561398991285767181296299)
    ·
      refine ⟨104342098486928650771944449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69561398991285767181296299 104342098486928650771944449)
      ·
        refine ⟨78256573865196488078958337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104342098486928650771944449 78256573865196488078958337)
        ·
          refine ⟨58692430398897366059218753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78256573865196488078958337 58692430398897366059218753)
          ·
            refine ⟨44019322799173024544414065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58692430398897366059218753 44019322799173024544414065)
            ·
              refine ⟨33014492099379768408310549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44019322799173024544414065 33014492099379768408310549)
              ·
                refine ⟨1547554317158426644139557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33014492099379768408310549 1547554317158426644139557)
                ·
                  refine ⟨290166434467204995776167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1547554317158426644139557 290166434467204995776167)
                  ·
                    rfl

theorem cell22_2542937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 4].length) (baseStart_2542937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542937 prefixEnd_2542937 := by exact prefixLift 2542937
  have htrace : WordTrace (prefixWord ++ tailWord_2542937) baseStart_2542937 baseEnd_2542937 := by
    simpa [prefixWord, tailWord_2542937, baseEnd_2542937] using wordTrace_append hprefix tailTrace_2542937
  have hstable : (prefixWord ++ tailWord_2542937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542937).length < 2 ^ (prefixWord ++ tailWord_2542937).sum := by decide
  have hdescent : baseEnd_2542937 < baseStart_2542937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542967 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 2, 4]
def baseStart_2542967 : Nat := 118140960795 + 2542967 * 2 ^ 59
def prefixEnd_2542967 : Nat := 4983230072969 + 3 ^ 40 * 2542967 * 2
def baseEnd_2542967 : Nat := 870509573014704909078409

theorem tailTrace_2542967 : CollatzResearch.WordTrace tailWord_2542967 prefixEnd_2542967 870509573014704909078409 := by
  unfold tailWord_2542967
  simp only [CollatzResearch.WordTrace]
  refine ⟨92749626178272338031987155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61833084118848225354658103 92749626178272338031987155)
  ·
    refine ⟨139124439267408507047980733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92749626178272338031987155 139124439267408507047980733)
    ·
      refine ⟨52171664725278190142992775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139124439267408507047980733 52171664725278190142992775)
      ·
        refine ⟨78257497087917285214489163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52171664725278190142992775 78257497087917285214489163)
        ·
          refine ⟨117386245631875927821733745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78257497087917285214489163 117386245631875927821733745)
          ·
            refine ⟨88039684223906945866300309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117386245631875927821733745 88039684223906945866300309)
            ·
              refine ⟨4126860197995638087482827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 88039684223906945866300309 4126860197995638087482827)
              ·
                refine ⟨6190290296993457131224241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4126860197995638087482827 6190290296993457131224241)
                ·
                  refine ⟨4642717722745092848418181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6190290296993457131224241 4642717722745092848418181)
                  ·
                    refine ⟨870509573014704909078409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4642717722745092848418181 870509573014704909078409)
                    ·
                      rfl

theorem cell22_2542967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_2542967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2542967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2542967 prefixEnd_2542967 := by exact prefixLift 2542967
  have htrace : WordTrace (prefixWord ++ tailWord_2542967) baseStart_2542967 baseEnd_2542967 := by
    simpa [prefixWord, tailWord_2542967, baseEnd_2542967] using wordTrace_append hprefix tailTrace_2542967
  have hstable : (prefixWord ++ tailWord_2542967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542967).length < 2 ^ (prefixWord ++ tailWord_2542967).sum := by decide
  have hdescent : baseEnd_2542967 < baseStart_2542967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543016 : List Nat := [2, 1, 6, 1, 2, 1, 3, 6]
def baseStart_2543016 : Nat := 118140960795 + 2543016 * 2 ^ 59
def prefixEnd_2543016 : Nat := 4983230072969 + 3 ^ 40 * 2543016 * 2
def baseEnd_2543016 : Nat := 96725149635120568289251

theorem tailTrace_2543016 : CollatzResearch.WordTrace tailWord_2543016 prefixEnd_2543016 96725149635120568289251 := by
  unfold tailWord_2543016
  simp only [CollatzResearch.WordTrace]
  refine ⟨46375706677547409700260451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61834275570063212933680601 46375706677547409700260451)
  ·
    refine ⟨69563560016321114550390677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46375706677547409700260451 69563560016321114550390677)
    ·
      refine ⟨3260791875765052244549563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69563560016321114550390677 3260791875765052244549563)
      ·
        refine ⟨4891187813647578366824345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3260791875765052244549563 4891187813647578366824345)
        ·
          refine ⟨3668390860235683775118259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4891187813647578366824345 3668390860235683775118259)
          ·
            refine ⟨5502586290353525662677389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3668390860235683775118259 5502586290353525662677389)
            ·
              refine ⟨2063469858882572123504021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5502586290353525662677389 2063469858882572123504021)
              ·
                refine ⟨96725149635120568289251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2063469858882572123504021 96725149635120568289251)
                ·
                  rfl

theorem cell22_2543016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 6].length) (baseStart_2543016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543016 prefixEnd_2543016 := by exact prefixLift 2543016
  have htrace : WordTrace (prefixWord ++ tailWord_2543016) baseStart_2543016 baseEnd_2543016 := by
    simpa [prefixWord, tailWord_2543016, baseEnd_2543016] using wordTrace_append hprefix tailTrace_2543016
  have hstable : (prefixWord ++ tailWord_2543016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543016).length < 2 ^ (prefixWord ++ tailWord_2543016).sum := by decide
  have hdescent : baseEnd_2543016 < baseStart_2543016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543031 : List Nat := [1, 1, 3, 1, 3, 2, 4, 3, 1, 3]
def baseStart_2543031 : Nat := 118140960795 + 2543031 * 2 ^ 59
def prefixEnd_2543031 : Nat := 4983230072969 + 3 ^ 40 * 2543031 * 2
def baseEnd_2543031 : Nat := 870531481522630075478213

theorem tailTrace_2543031 : CollatzResearch.WordTrace tailWord_2543031 prefixEnd_2543031 870531481522630075478213 := by
  unfold tailWord_2543031
  simp only [CollatzResearch.WordTrace]
  refine ⟨92751960450040476962316947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61834640300026984641544631 92751960450040476962316947)
  ·
    refine ⟨139127940675060715443475421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92751960450040476962316947 139127940675060715443475421)
    ·
      refine ⟨52172977753147768291303283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139127940675060715443475421 52172977753147768291303283)
      ·
        refine ⟨78259466629721652436954925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52172977753147768291303283 78259466629721652436954925)
        ·
          refine ⟨29347299986145619663858097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78259466629721652436954925 29347299986145619663858097)
          ·
            refine ⟨22010474989609214747893573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29347299986145619663858097 22010474989609214747893573)
            ·
              refine ⟨4126964060551727765230045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22010474989609214747893573 4126964060551727765230045)
              ·
                refine ⟨1547611522706897911961267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4126964060551727765230045 1547611522706897911961267)
                ·
                  refine ⟨2321417284060346867941901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547611522706897911961267 2321417284060346867941901)
                  ·
                    refine ⟨870531481522630075478213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2321417284060346867941901 870531481522630075478213)
                    ·
                      rfl

theorem cell22_2543031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_2543031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543031 prefixEnd_2543031 := by exact prefixLift 2543031
  have htrace : WordTrace (prefixWord ++ tailWord_2543031) baseStart_2543031 baseEnd_2543031 := by
    simpa [prefixWord, tailWord_2543031, baseEnd_2543031] using wordTrace_append hprefix tailTrace_2543031
  have hstable : (prefixWord ++ tailWord_2543031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543031).length < 2 ^ (prefixWord ++ tailWord_2543031).sum := by decide
  have hdescent : baseEnd_2543031 < baseStart_2543031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543044 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 7]
def baseStart_2543044 : Nat := 118140960795 + 2543044 * 2 ^ 59
def prefixEnd_2543044 : Nat := 4983230072969 + 3 ^ 40 * 2543044 * 2
def baseEnd_2543044 : Nat := 290178643896100791634391

theorem tailTrace_2543044 : CollatzResearch.WordTrace tailWord_2543044 prefixEnd_2543044 290178643896100791634391 := by
  unfold tailWord_2543044
  simp only [CollatzResearch.WordTrace]
  refine ⟨46376217299496690091270093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61834956399328920121693457 46376217299496690091270093)
  ·
    refine ⟨17391081487311258784226285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46376217299496690091270093 17391081487311258784226285)
    ·
      refine ⟨6521655557741722044084857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17391081487311258784226285 6521655557741722044084857)
      ·
        refine ⟨4891241668306291533063643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6521655557741722044084857 4891241668306291533063643)
        ·
          refine ⟨7336862502459437299595465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4891241668306291533063643 7336862502459437299595465)
          ·
            refine ⟨5502646876844577974696599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7336862502459437299595465 5502646876844577974696599)
            ·
              refine ⟨8253970315266866962044899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5502646876844577974696599 8253970315266866962044899)
              ·
                refine ⟨12380955472900300443067349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8253970315266866962044899 12380955472900300443067349)
                ·
                  refine ⟨290178643896100791634391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12380955472900300443067349 290178643896100791634391)
                  ·
                    rfl

theorem cell22_2543044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_2543044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543044 prefixEnd_2543044 := by exact prefixLift 2543044
  have htrace : WordTrace (prefixWord ++ tailWord_2543044) baseStart_2543044 baseEnd_2543044 := by
    simpa [prefixWord, tailWord_2543044, baseEnd_2543044] using wordTrace_append hprefix tailTrace_2543044
  have hstable : (prefixWord ++ tailWord_2543044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543044).length < 2 ^ (prefixWord ++ tailWord_2543044).sum := by decide
  have hdescent : baseEnd_2543044 < baseStart_2543044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543087 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 1, 5]
def baseStart_2543087 : Nat := 118140960795 + 2543087 * 2 ^ 59
def prefixEnd_2543087 : Nat := 4983230072969 + 3 ^ 40 * 2543087 * 2
def baseEnd_2543087 : Nat := 870550651467064596078041

theorem tailTrace_2543087 : CollatzResearch.WordTrace tailWord_2543087 prefixEnd_2543087 870550651467064596078041 := by
  unfold tailWord_2543087
  simp only [CollatzResearch.WordTrace]
  refine ⟨92754002937837598526355515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61836001958558399017570343 92754002937837598526355515)
  ·
    refine ⟨139131004406756397789533273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92754002937837598526355515 139131004406756397789533273)
    ·
      refine ⟨104348253305067298342149955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139131004406756397789533273 104348253305067298342149955)
      ·
        refine ⟨156522379957600947513224933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104348253305067298342149955 156522379957600947513224933)
        ·
          refine ⟨29347946242050177658729675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156522379957600947513224933 29347946242050177658729675)
          ·
            refine ⟨44021919363075266488094513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29347946242050177658729675 44021919363075266488094513)
            ·
              refine ⟨33016439522306449866070885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44021919363075266488094513 33016439522306449866070885)
              ·
                refine ⟨6190582410432459349888291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33016439522306449866070885 6190582410432459349888291)
                ·
                  refine ⟨9285873615648689024832437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6190582410432459349888291 9285873615648689024832437)
                  ·
                    refine ⟨870550651467064596078041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9285873615648689024832437 870550651467064596078041)
                    ·
                      rfl

theorem cell22_2543087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_2543087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543087 prefixEnd_2543087 := by exact prefixLift 2543087
  have htrace : WordTrace (prefixWord ++ tailWord_2543087) baseStart_2543087 baseEnd_2543087 := by
    simpa [prefixWord, tailWord_2543087, baseEnd_2543087] using wordTrace_append hprefix tailTrace_2543087
  have hstable : (prefixWord ++ tailWord_2543087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543087).length < 2 ^ (prefixWord ++ tailWord_2543087).sum := by decide
  have hdescent : baseEnd_2543087 < baseStart_2543087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543106 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 6]
def baseStart_2543106 : Nat := 118140960795 + 2543106 * 2 ^ 59
def prefixEnd_2543106 : Nat := 4983230072969 + 3 ^ 40 * 2543106 * 2
def baseEnd_2543106 : Nat := 290185718518451626617661

theorem tailTrace_2543106 : CollatzResearch.WordTrace tailWord_2543106 prefixEnd_2543106 290185718518451626617661 := by
  unfold tailWord_2543106
  simp only [CollatzResearch.WordTrace]
  refine ⟨23188673981192191192824293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61836463949845843180864781 23188673981192191192824293)
  ·
    refine ⟨4347876371473535848654555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23188673981192191192824293 4347876371473535848654555)
    ·
      refine ⟨6521814557210303772981833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4347876371473535848654555 6521814557210303772981833)
      ·
        refine ⟨4891360917907727829736375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6521814557210303772981833 4891360917907727829736375)
        ·
          refine ⟨7337041376861591744604563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4891360917907727829736375 7337041376861591744604563)
          ·
            refine ⟨11005562065292387616906845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7337041376861591744604563 11005562065292387616906845)
            ·
              refine ⟨4127085774484645356340067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11005562065292387616906845 4127085774484645356340067)
              ·
                refine ⟨6190628661726968034510101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4127085774484645356340067 6190628661726968034510101)
                ·
                  refine ⟨290185718518451626617661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6190628661726968034510101 290185718518451626617661)
                  ·
                    rfl

theorem cell22_2543106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_2543106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543106 prefixEnd_2543106 := by exact prefixLift 2543106
  have htrace : WordTrace (prefixWord ++ tailWord_2543106) baseStart_2543106 baseEnd_2543106 := by
    simpa [prefixWord, tailWord_2543106, baseEnd_2543106] using wordTrace_append hprefix tailTrace_2543106
  have hstable : (prefixWord ++ tailWord_2543106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543106).length < 2 ^ (prefixWord ++ tailWord_2543106).sum := by decide
  have hdescent : baseEnd_2543106 < baseStart_2543106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543136 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 2, 4]
def baseStart_2543136 : Nat := 118140960795 + 2543136 * 2 ^ 59
def prefixEnd_2543136 : Nat := 4983230072969 + 3 ^ 40 * 2543136 * 2
def baseEnd_2543136 : Nat := 870567425168444801602891

theorem tailTrace_2543136 : CollatzResearch.WordTrace tailWord_2543136 prefixEnd_2543136 870567425168444801602891 := by
  unfold tailWord_2543136
  simp only [CollatzResearch.WordTrace]
  refine ⟨46377895057330039947444631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61837193409773386596592841 46377895057330039947444631)
  ·
    refine ⟨69566842585995059921166947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46377895057330039947444631 69566842585995059921166947)
    ·
      refine ⟨104350263878992589881750421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69566842585995059921166947 104350263878992589881750421)
      ·
        refine ⟨4891418619327777650707051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 104350263878992589881750421 4891418619327777650707051)
        ·
          refine ⟨7337127928991666476060577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4891418619327777650707051 7337127928991666476060577)
          ·
            refine ⟨5502845946743749857045433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7337127928991666476060577 5502845946743749857045433)
            ·
              refine ⟨4127134460057812392784075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5502845946743749857045433 4127134460057812392784075)
              ·
                refine ⟨6190701690086718589176113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4127134460057812392784075 6190701690086718589176113)
                ·
                  refine ⟨4643026267565038941882085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6190701690086718589176113 4643026267565038941882085)
                  ·
                    refine ⟨870567425168444801602891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4643026267565038941882085 870567425168444801602891)
                    ·
                      rfl

theorem cell22_2543136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_2543136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543136 prefixEnd_2543136 := by exact prefixLift 2543136
  have htrace : WordTrace (prefixWord ++ tailWord_2543136) baseStart_2543136 baseEnd_2543136 := by
    simpa [prefixWord, tailWord_2543136, baseEnd_2543136] using wordTrace_append hprefix tailTrace_2543136
  have hstable : (prefixWord ++ tailWord_2543136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543136).length < 2 ^ (prefixWord ++ tailWord_2543136).sum := by decide
  have hdescent : baseEnd_2543136 < baseStart_2543136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543213 : List Nat := [1, 5, 1, 1, 4, 2, 1, 2, 5]
def baseStart_2543213 : Nat := 118140960795 + 2543213 * 2 ^ 59
def prefixEnd_2543213 : Nat := 4983230072969 + 3 ^ 40 * 2543213 * 2
def baseEnd_2543213 : Nat := 290197927947347422475885

theorem tailTrace_2543213 : CollatzResearch.WordTrace tailWord_2543213 prefixEnd_2543213 290197927947347422475885 := by
  unfold tailWord_2543213
  simp only [CollatzResearch.WordTrace]
  refine ⟨92758598535381122045442293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61839065690254081363628195 92758598535381122045442293)
  ·
    refine ⟨8696118612691980191760215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92758598535381122045442293 8696118612691980191760215)
    ·
      refine ⟨13044177919037970287640323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8696118612691980191760215 13044177919037970287640323)
      ·
        refine ⟨19566266878556955431460485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13044177919037970287640323 19566266878556955431460485)
        ·
          refine ⟨3668675039729429143398841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19566266878556955431460485 3668675039729429143398841)
          ·
            refine ⟨2751506279797071857549131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3668675039729429143398841 2751506279797071857549131)
            ·
              refine ⟨4127259419695607786323697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2751506279797071857549131 4127259419695607786323697)
              ·
                refine ⟨3095444564771705839742773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4127259419695607786323697 3095444564771705839742773)
                ·
                  refine ⟨290197927947347422475885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3095444564771705839742773 290197927947347422475885)
                  ·
                    rfl

theorem cell22_2543213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_2543213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543213 prefixEnd_2543213 := by exact prefixLift 2543213
  have htrace : WordTrace (prefixWord ++ tailWord_2543213) baseStart_2543213 baseEnd_2543213 := by
    simpa [prefixWord, tailWord_2543213, baseEnd_2543213] using wordTrace_append hprefix tailTrace_2543213
  have hstable : (prefixWord ++ tailWord_2543213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543213).length < 2 ^ (prefixWord ++ tailWord_2543213).sum := by decide
  have hdescent : baseEnd_2543213 < baseStart_2543213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543256 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 4, 3]
def baseStart_2543256 : Nat := 118140960795 + 2543256 * 2 ^ 59
def prefixEnd_2543256 : Nat := 4983230072969 + 3 ^ 40 * 2543256 * 2
def baseEnd_2543256 : Nat := 870608503620804488602523

theorem tailTrace_2543256 : CollatzResearch.WordTrace tailWord_2543256 prefixEnd_2543256 870608503620804488602523 := by
  unfold tailWord_2543256
  simp only [CollatzResearch.WordTrace]
  refine ⟨46380083437112670194628811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61840111249483560259505081 46380083437112670194628811)
  ·
    refine ⟨69570125155669005291943217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46380083437112670194628811 69570125155669005291943217)
    ·
      refine ⟨52177593866751753968957413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69570125155669005291943217 52177593866751753968957413)
      ·
        refine ⟨9783298850015953869179515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52177593866751753968957413 9783298850015953869179515)
        ·
          refine ⟨14674948275023930803769273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9783298850015953869179515 14674948275023930803769273)
          ·
            refine ⟨11006211206267948102826955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14674948275023930803769273 11006211206267948102826955)
            ·
              refine ⟨16509316809401922154240433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11006211206267948102826955 16509316809401922154240433)
              ·
                refine ⟨12381987607051441615680325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16509316809401922154240433 12381987607051441615680325)
                ·
                  refine ⟨2321622676322145302940061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12381987607051441615680325 2321622676322145302940061)
                  ·
                    refine ⟨870608503620804488602523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2321622676322145302940061 870608503620804488602523)
                    ·
                      rfl

theorem cell22_2543256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_2543256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543256 prefixEnd_2543256 := by exact prefixLift 2543256
  have htrace : WordTrace (prefixWord ++ tailWord_2543256) baseStart_2543256 baseEnd_2543256 := by
    simpa [prefixWord, tailWord_2543256, baseEnd_2543256] using wordTrace_append hprefix tailTrace_2543256
  have hstable : (prefixWord ++ tailWord_2543256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543256).length < 2 ^ (prefixWord ++ tailWord_2543256).sum := by decide
  have hdescent : baseEnd_2543256 < baseStart_2543256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543290 : List Nat := [3, 1, 1, 1, 2, 6, 2, 1, 2, 3]
def baseStart_2543290 : Nat := 118140960795 + 2543290 * 2 ^ 59
def prefixEnd_2543290 : Nat := 4983230072969 + 3 ^ 40 * 2543290 * 2
def baseEnd_2543290 : Nat := 870620142515639733252419

theorem tailTrace_2543290 : CollatzResearch.WordTrace tailWord_2543290 prefixEnd_2543290 870620142515639733252419 := by
  unfold tailWord_2543290
  simp only [CollatzResearch.WordTrace]
  refine ⟨23190351739025541048998831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61840937970734776130663549 23190351739025541048998831)
  ·
    refine ⟨34785527608538311573498247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23190351739025541048998831 34785527608538311573498247)
    ·
      refine ⟨52178291412807467360247371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34785527608538311573498247 52178291412807467360247371)
      ·
        refine ⟨78267437119211201040371057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52178291412807467360247371 78267437119211201040371057)
        ·
          refine ⟨58700577839408400780278293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78267437119211201040371057 58700577839408400780278293)
          ·
            refine ⟨2751589586222268786575545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58700577839408400780278293 2751589586222268786575545)
            ·
              refine ⟨2063692189666701589931659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2751589586222268786575545 2063692189666701589931659)
              ·
                refine ⟨3095538284500052384897489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2063692189666701589931659 3095538284500052384897489)
                ·
                  refine ⟨2321653713375039288673117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3095538284500052384897489 2321653713375039288673117)
                  ·
                    refine ⟨870620142515639733252419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2321653713375039288673117 870620142515639733252419)
                    ·
                      rfl

theorem cell22_2543290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_2543290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543290 prefixEnd_2543290 := by exact prefixLift 2543290
  have htrace : WordTrace (prefixWord ++ tailWord_2543290) baseStart_2543290 baseEnd_2543290 := by
    simpa [prefixWord, tailWord_2543290, baseEnd_2543290] using wordTrace_append hprefix tailTrace_2543290
  have hstable : (prefixWord ++ tailWord_2543290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543290).length < 2 ^ (prefixWord ++ tailWord_2543290).sum := by decide
  have hdescent : baseEnd_2543290 < baseStart_2543290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543346 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_2543346 : Nat := 118140960795 + 2543346 * 2 ^ 59
def prefixEnd_2543346 : Nat := 4983230072969 + 3 ^ 40 * 2543346 * 2
def baseEnd_2543346 : Nat := 870639312460074253852247

theorem tailTrace_2543346 : CollatzResearch.WordTrace tailWord_2543346 prefixEnd_2543346 870639312460074253852247 := by
  unfold tailWord_2543346
  simp only [CollatzResearch.WordTrace]
  refine ⟨23190862360974821440008473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61842299629266190506689261 23190862360974821440008473)
  ·
    refine ⟨17393146770731116080006355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23190862360974821440008473 17393146770731116080006355)
    ·
      refine ⟨26089720156096674120009533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17393146770731116080006355 26089720156096674120009533)
      ·
        refine ⟨9783645058536252795003575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26089720156096674120009533 9783645058536252795003575)
        ·
          refine ⟨14675467587804379192505363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9783645058536252795003575 14675467587804379192505363)
          ·
            refine ⟨22013201381706568788758045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14675467587804379192505363 22013201381706568788758045)
            ·
              refine ⟨8254950518139963295784267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22013201381706568788758045 8254950518139963295784267)
              ·
                refine ⟨12382425777209944943676401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8254950518139963295784267 12382425777209944943676401)
                ·
                  refine ⟨9286819332907458707757301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12382425777209944943676401 9286819332907458707757301)
                  ·
                    refine ⟨870639312460074253852247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9286819332907458707757301 870639312460074253852247)
                    ·
                      rfl

theorem cell22_2543346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_2543346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543346 prefixEnd_2543346 := by exact prefixLift 2543346
  have htrace : WordTrace (prefixWord ++ tailWord_2543346) baseStart_2543346 baseEnd_2543346 := by
    simpa [prefixWord, tailWord_2543346, baseEnd_2543346] using wordTrace_append hprefix tailTrace_2543346
  have hstable : (prefixWord ++ tailWord_2543346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543346).length < 2 ^ (prefixWord ++ tailWord_2543346).sum := by decide
  have hdescent : baseEnd_2543346 < baseStart_2543346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543359 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 8]
def baseStart_2543359 : Nat := 118140960795 + 2543359 * 2 ^ 59
def prefixEnd_2543359 : Nat := 4983230072969 + 3 ^ 40 * 2543359 * 2
def baseEnd_2543359 : Nat := 290214587541915517759069

theorem tailTrace_2543359 : CollatzResearch.WordTrace tailWord_2543359 prefixEnd_2543359 290214587541915517759069 := by
  unfold tailWord_2543359
  simp only [CollatzResearch.WordTrace]
  refine ⟨92763923592852188980257131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61842615728568125986838087 92763923592852188980257131)
  ·
    refine ⟨139145885389278283470385697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92763923592852188980257131 139145885389278283470385697)
    ·
      refine ⟨104359414041958712602789273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139145885389278283470385697 104359414041958712602789273)
      ·
        refine ⟨78269560531469034452091955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104359414041958712602789273 78269560531469034452091955)
        ·
          refine ⟨117404340797203551678137933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78269560531469034452091955 117404340797203551678137933)
          ·
            refine ⟨44026627798951331879301725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117404340797203551678137933 44026627798951331879301725)
            ·
              refine ⟨16509985424606749454738147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44026627798951331879301725 16509985424606749454738147)
              ·
                refine ⟨24764978136910124182107221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16509985424606749454738147 24764978136910124182107221)
                ·
                  refine ⟨290214587541915517759069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24764978136910124182107221 290214587541915517759069)
                  ·
                    rfl

theorem cell22_2543359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 8].length) (baseStart_2543359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543359 prefixEnd_2543359 := by exact prefixLift 2543359
  have htrace : WordTrace (prefixWord ++ tailWord_2543359) baseStart_2543359 baseEnd_2543359 := by
    simpa [prefixWord, tailWord_2543359, baseEnd_2543359] using wordTrace_append hprefix tailTrace_2543359
  have hstable : (prefixWord ++ tailWord_2543359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543359).length < 2 ^ (prefixWord ++ tailWord_2543359).sum := by decide
  have hdescent : baseEnd_2543359 < baseStart_2543359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543361 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2543361 : Nat := 118140960795 + 2543361 * 2 ^ 59
def prefixEnd_2543361 : Nat := 4983230072969 + 3 ^ 40 * 2543361 * 2
def baseEnd_2543361 : Nat := 870644447266619214727201

theorem tailTrace_2543361 : CollatzResearch.WordTrace tailWord_2543361 prefixEnd_2543361 870644447266619214727201 := by
  unfold tailWord_2543361
  simp only [CollatzResearch.WordTrace]
  refine ⟨92763996538844943321829937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61842664359229962214553291 92763996538844943321829937)
  ·
    refine ⟨69572997404133707491372453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92763996538844943321829937 69572997404133707491372453)
    ·
      refine ⟨13044937013275070154632335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69572997404133707491372453 13044937013275070154632335)
      ·
        refine ⟨19567405519912605231948503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13044937013275070154632335 19567405519912605231948503)
        ·
          refine ⟨29351108279868907847922755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19567405519912605231948503 29351108279868907847922755)
          ·
            refine ⟨44026662419803361771884133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29351108279868907847922755 44026662419803361771884133)
            ·
              refine ⟨8254999203713130332228275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44026662419803361771884133 8254999203713130332228275)
              ·
                refine ⟨12382498805569695498342413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8254999203713130332228275 12382498805569695498342413)
                ·
                  refine ⟨4643437052088635811878405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12382498805569695498342413 4643437052088635811878405)
                  ·
                    refine ⟨870644447266619214727201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4643437052088635811878405 870644447266619214727201)
                    ·
                      rfl

theorem cell22_2543361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2543361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543361 prefixEnd_2543361 := by exact prefixLift 2543361
  have htrace : WordTrace (prefixWord ++ tailWord_2543361) baseStart_2543361 baseEnd_2543361 := by
    simpa [prefixWord, tailWord_2543361, baseEnd_2543361] using wordTrace_append hprefix tailTrace_2543361
  have hstable : (prefixWord ++ tailWord_2543361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543361).length < 2 ^ (prefixWord ++ tailWord_2543361).sum := by decide
  have hdescent : baseEnd_2543361 < baseStart_2543361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543393 : List Nat := [1, 2, 3, 2, 1, 3, 2, 4, 4]
def baseStart_2543393 : Nat := 118140960795 + 2543393 * 2 ^ 59
def prefixEnd_2543393 : Nat := 4983230072969 + 3 ^ 40 * 2543393 * 2
def baseEnd_2543393 : Nat := 290218467173527265975701

theorem tailTrace_2543393 : CollatzResearch.WordTrace tailWord_2543393 prefixEnd_2543393 290218467173527265975701 := by
  unfold tailWord_2543393
  simp only [CollatzResearch.WordTrace]
  refine ⟨92765163674729012786994833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61843442449819341857996555 92765163674729012786994833)
  ·
    refine ⟨69573872756046759590246125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92765163674729012786994833 69573872756046759590246125)
    ·
      refine ⟨26090202283517534846342297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69573872756046759590246125 26090202283517534846342297)
      ·
        refine ⟨19567651712638151134756723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26090202283517534846342297 19567651712638151134756723)
        ·
          refine ⟨29351477568957226702135085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19567651712638151134756723 29351477568957226702135085)
          ·
            refine ⟨11006804088358960013300657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29351477568957226702135085 11006804088358960013300657)
            ·
              refine ⟨8255103066269220009975493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11006804088358960013300657 8255103066269220009975493)
              ·
                refine ⟨1547831824925478751870405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8255103066269220009975493 1547831824925478751870405)
                ·
                  refine ⟨290218467173527265975701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1547831824925478751870405 290218467173527265975701)
                  ·
                    rfl

theorem cell22_2543393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 4].length) (baseStart_2543393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543393 prefixEnd_2543393 := by exact prefixLift 2543393
  have htrace : WordTrace (prefixWord ++ tailWord_2543393) baseStart_2543393 baseEnd_2543393 := by
    simpa [prefixWord, tailWord_2543393, baseEnd_2543393] using wordTrace_append hprefix tailTrace_2543393
  have hstable : (prefixWord ++ tailWord_2543393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543393).length < 2 ^ (prefixWord ++ tailWord_2543393).sum := by decide
  have hdescent : baseEnd_2543393 < baseStart_2543393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543459 : List Nat := [1, 1, 1, 5, 5, 1, 2, 1, 2, 3]
def baseStart_2543459 : Nat := 118140960795 + 2543459 * 2 ^ 59
def prefixEnd_2543459 : Nat := 4983230072969 + 3 ^ 40 * 2543459 * 2
def baseEnd_2543459 : Nat := 870677994669379625776901

theorem tailTrace_2543459 : CollatzResearch.WordTrace tailWord_2543459 prefixEnd_2543459 870677994669379625776901 := by
  unfold tailWord_2543459
  simp only [CollatzResearch.WordTrace]
  refine ⟨92767570892489906058897431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61845047261659937372598287 92767570892489906058897431)
  ·
    refine ⟨139151356338734859088346147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92767570892489906058897431 139151356338734859088346147)
    ·
      refine ⟨208727034508102288632519221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139151356338734859088346147 208727034508102288632519221)
      ·
        refine ⟨19568159485134589559298677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 208727034508102288632519221 19568159485134589559298677)
        ·
          refine ⟨1834514951731367771184251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19568159485134589559298677 1834514951731367771184251)
          ·
            refine ⟨2751772427597051656776377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834514951731367771184251 2751772427597051656776377)
            ·
              refine ⟨2063829320697788742582283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2751772427597051656776377 2063829320697788742582283)
              ·
                refine ⟨3095743981046683113873425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2063829320697788742582283 3095743981046683113873425)
                ·
                  refine ⟨2321807985785012335405069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3095743981046683113873425 2321807985785012335405069)
                  ·
                    refine ⟨870677994669379625776901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2321807985785012335405069 870677994669379625776901)
                    ·
                      rfl

theorem cell22_2543459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 2, 3].length) (baseStart_2543459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543459 prefixEnd_2543459 := by exact prefixLift 2543459
  have htrace : WordTrace (prefixWord ++ tailWord_2543459) baseStart_2543459 baseEnd_2543459 := by
    simpa [prefixWord, tailWord_2543459, baseEnd_2543459] using wordTrace_append hprefix tailTrace_2543459
  have hstable : (prefixWord ++ tailWord_2543459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543459).length < 2 ^ (prefixWord ++ tailWord_2543459).sum := by decide
  have hdescent : baseEnd_2543459 < baseStart_2543459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543543 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 4, 3]
def baseStart_2543543 : Nat := 118140960795 + 2543543 * 2 ^ 59
def prefixEnd_2543543 : Nat := 4983230072969 + 3 ^ 40 * 2543543 * 2
def baseEnd_2543543 : Nat := 870706749586031406676643

theorem tailTrace_2543543 : CollatzResearch.WordTrace tailWord_2543543 prefixEnd_2543543 870706749586031406676643 := by
  unfold tailWord_2543543
  simp only [CollatzResearch.WordTrace]
  refine ⟨92770634624185588404955283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61847089749457058936636855 92770634624185588404955283)
  ·
    refine ⟨139155951936278382607432925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92770634624185588404955283 139155951936278382607432925)
    ·
      refine ⟨52183481976104393477787347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139155951936278382607432925 52183481976104393477787347)
      ·
        refine ⟨78275222964156590216681021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52183481976104393477787347 78275222964156590216681021)
        ·
          refine ⟨29353208611558721331255383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78275222964156590216681021 29353208611558721331255383)
          ·
            refine ⟨44029812917338081996883075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29353208611558721331255383 44029812917338081996883075)
            ·
              refine ⟨66044719376007122995324613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44029812917338081996883075 66044719376007122995324613)
              ·
                refine ⟨12383384883001335561623365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66044719376007122995324613 12383384883001335561623365)
                ·
                  refine ⟨2321884665562750417804381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12383384883001335561623365 2321884665562750417804381)
                  ·
                    refine ⟨870706749586031406676643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2321884665562750417804381 870706749586031406676643)
                    ·
                      rfl

theorem cell22_2543543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_2543543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543543 prefixEnd_2543543 := by exact prefixLift 2543543
  have htrace : WordTrace (prefixWord ++ tailWord_2543543) baseStart_2543543 baseEnd_2543543 := by
    simpa [prefixWord, tailWord_2543543, baseEnd_2543543] using wordTrace_append hprefix tailTrace_2543543
  have hstable : (prefixWord ++ tailWord_2543543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543543).length < 2 ^ (prefixWord ++ tailWord_2543543).sum := by decide
  have hdescent : baseEnd_2543543 < baseStart_2543543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543545 : List Nat := [1, 2, 1, 4, 2, 1, 4, 3, 4]
def baseStart_2543545 : Nat := 118140960795 + 2543545 * 2 ^ 59
def prefixEnd_2543545 : Nat := 4983230072969 + 3 ^ 40 * 2543545 * 2
def baseEnd_2543545 : Nat := 290235811408968022708879

theorem tailTrace_2543545 : CollatzResearch.WordTrace tailWord_2543545 prefixEnd_2543545 290235811408968022708879 := by
  unfold tailWord_2543545
  simp only [CollatzResearch.WordTrace]
  refine ⟨92770707570178342746528089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61847138380118895164352059 92770707570178342746528089)
  ·
    refine ⟨69578030677633757059896067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92770707570178342746528089 69578030677633757059896067)
    ·
      refine ⟨104367046016450635589844101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69578030677633757059896067 104367046016450635589844101)
      ·
        refine ⟨19568821128084494173095769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104367046016450635589844101 19568821128084494173095769)
        ·
          refine ⟨14676615846063370629821827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19568821128084494173095769 14676615846063370629821827)
          ·
            refine ⟨22014923769095055944732741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14676615846063370629821827 22014923769095055944732741)
            ·
              refine ⟨4127798206705322989637389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22014923769095055944732741 4127798206705322989637389)
              ·
                refine ⟨1547924327514496121114021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4127798206705322989637389 1547924327514496121114021)
                ·
                  refine ⟨290235811408968022708879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1547924327514496121114021 290235811408968022708879)
                  ·
                    rfl

theorem cell22_2543545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 4].length) (baseStart_2543545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543545 prefixEnd_2543545 := by exact prefixLift 2543545
  have htrace : WordTrace (prefixWord ++ tailWord_2543545) baseStart_2543545 baseEnd_2543545 := by
    simpa [prefixWord, tailWord_2543545, baseEnd_2543545] using wordTrace_append hprefix tailTrace_2543545
  have hstable : (prefixWord ++ tailWord_2543545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543545).length < 2 ^ (prefixWord ++ tailWord_2543545).sum := by decide
  have hdescent : baseEnd_2543545 < baseStart_2543545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543560 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 4, 3]
def baseStart_2543560 : Nat := 118140960795 + 2543560 * 2 ^ 59
def prefixEnd_2543560 : Nat := 4983230072969 + 3 ^ 40 * 2543560 * 2
def baseEnd_2543560 : Nat := 870712569033449029001591

theorem tailTrace_2543560 : CollatzResearch.WordTrace tailWord_2543560 prefixEnd_2543560 870712569033449029001591 := by
  unfold tailWord_2543560
  simp only [CollatzResearch.WordTrace]
  refine ⟨46385627332562000154162067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61847503110082666872216089 46385627332562000154162067)
  ·
    refine ⟨69578440998843000231243101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46385627332562000154162067 69578440998843000231243101)
    ·
      refine ⟨26091915374566125086716163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69578440998843000231243101 26091915374566125086716163)
      ·
        refine ⟨39137873061849187630074245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26091915374566125086716163 39137873061849187630074245)
        ·
          refine ⟨7338351199096722680638921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39137873061849187630074245 7338351199096722680638921)
          ·
            refine ⟨5503763399322542010479191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7338351199096722680638921 5503763399322542010479191)
            ·
              refine ⟨8255645098983813015718787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5503763399322542010479191 8255645098983813015718787)
              ·
                refine ⟨12383467648475719523578181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8255645098983813015718787 12383467648475719523578181)
                ·
                  refine ⟨2321900184089197410670909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12383467648475719523578181 2321900184089197410670909)
                  ·
                    refine ⟨870712569033449029001591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2321900184089197410670909 870712569033449029001591)
                    ·
                      rfl

theorem cell22_2543560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_2543560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543560 prefixEnd_2543560 := by exact prefixLift 2543560
  have htrace : WordTrace (prefixWord ++ tailWord_2543560) baseStart_2543560 baseEnd_2543560 := by
    simpa [prefixWord, tailWord_2543560, baseEnd_2543560] using wordTrace_append hprefix tailTrace_2543560
  have hstable : (prefixWord ++ tailWord_2543560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543560).length < 2 ^ (prefixWord ++ tailWord_2543560).sum := by decide
  have hdescent : baseEnd_2543560 < baseStart_2543560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543577 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 1, 5]
def baseStart_2543577 : Nat := 118140960795 + 2543577 * 2 ^ 59
def prefixEnd_2543577 : Nat := 4983230072969 + 3 ^ 40 * 2543577 * 2
def baseEnd_2543577 : Nat := 870718388480866651326539

theorem tailTrace_2543577 : CollatzResearch.WordTrace tailWord_2543577 prefixEnd_2543577 870718388480866651326539 := by
  unfold tailWord_2543577
  simp only [CollatzResearch.WordTrace]
  refine ⟨92771874706062412211692985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61847916470708274807795323 92771874706062412211692985)
  ·
    refine ⟨69578906029546809158769739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92771874706062412211692985 69578906029546809158769739)
    ·
      refine ⟨104368359044320213738154609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69578906029546809158769739 104368359044320213738154609)
      ·
        refine ⟨78276269283240160303615957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104368359044320213738154609 78276269283240160303615957)
        ·
          refine ⟨1834600061325941257115999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 78276269283240160303615957 1834600061325941257115999)
          ·
            refine ⟨2751900091988911885673999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834600061325941257115999 2751900091988911885673999)
            ·
              refine ⟨4127850137983367828510999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2751900091988911885673999 4127850137983367828510999)
              ·
                refine ⟨6191775206975051742766499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4127850137983367828510999 6191775206975051742766499)
                ·
                  refine ⟨9287662810462577614149749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6191775206975051742766499 9287662810462577614149749)
                  ·
                    refine ⟨870718388480866651326539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9287662810462577614149749 870718388480866651326539)
                    ·
                      rfl

theorem cell22_2543577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 1, 5].length) (baseStart_2543577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543577 prefixEnd_2543577 := by exact prefixLift 2543577
  have htrace : WordTrace (prefixWord ++ tailWord_2543577) baseStart_2543577 baseEnd_2543577 := by
    simpa [prefixWord, tailWord_2543577, baseEnd_2543577] using wordTrace_append hprefix tailTrace_2543577
  have hstable : (prefixWord ++ tailWord_2543577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543577).length < 2 ^ (prefixWord ++ tailWord_2543577).sum := by decide
  have hdescent : baseEnd_2543577 < baseStart_2543577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543635 : List Nat := [1, 1, 1, 2, 1, 4, 6, 1, 5]
def baseStart_2543635 : Nat := 118140960795 + 2543635 * 2 ^ 59
def prefixEnd_2543635 : Nat := 4983230072969 + 3 ^ 40 * 2543635 * 2
def baseEnd_2543635 : Nat := 290246081022057944458787

theorem tailTrace_2543635 : CollatzResearch.WordTrace tailWord_2543635 prefixEnd_2543635 290246081022057944458787 := by
  unfold tailWord_2543635
  simp only [CollatzResearch.WordTrace]
  refine ⟨92773990139852288117304359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61849326759901525411536239 92773990139852288117304359)
  ·
    refine ⟨139160985209778432175956539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92773990139852288117304359 139160985209778432175956539)
    ·
      refine ⟨208741477814667648263934809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139160985209778432175956539 208741477814667648263934809)
      ·
        refine ⟨156556108361000736197951107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208741477814667648263934809 156556108361000736197951107)
        ·
          refine ⟨234834162541501104296926661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156556108361000736197951107 234834162541501104296926661)
          ·
            refine ⟨44031405476531457055673749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234834162541501104296926661 44031405476531457055673749)
            ·
              refine ⟨2063972131712412049484707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44031405476531457055673749 2063972131712412049484707)
              ·
                refine ⟨3095958197568618074227061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2063972131712412049484707 3095958197568618074227061)
                ·
                  refine ⟨290246081022057944458787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3095958197568618074227061 290246081022057944458787)
                  ·
                    rfl

theorem cell22_2543635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 5].length) (baseStart_2543635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543635 prefixEnd_2543635 := by exact prefixLift 2543635
  have htrace : WordTrace (prefixWord ++ tailWord_2543635) baseStart_2543635 baseEnd_2543635 := by
    simpa [prefixWord, tailWord_2543635, baseEnd_2543635] using wordTrace_append hprefix tailTrace_2543635
  have hstable : (prefixWord ++ tailWord_2543635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543635).length < 2 ^ (prefixWord ++ tailWord_2543635).sum := by decide
  have hdescent : baseEnd_2543635 < baseStart_2543635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543673 : List Nat := [1, 2, 1, 5, 4, 1, 2, 2, 1, 3]
def baseStart_2543673 : Nat := 118140960795 + 2543673 * 2 ^ 59
def prefixEnd_2543673 : Nat := 4983230072969 + 3 ^ 40 * 2543673 * 2
def baseEnd_2543673 : Nat := 870751251242754400926245

theorem tailTrace_2543673 : CollatzResearch.WordTrace tailWord_2543673 prefixEnd_2543673 870751251242754400926245 := by
  unfold tailWord_2543673
  simp only [CollatzResearch.WordTrace]
  refine ⟨92775376113714620607187673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61850250742476413738125115 92775376113714620607187673)
  ·
    refine ⟨69581532085285965455390755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92775376113714620607187673 69581532085285965455390755)
    ·
      refine ⟨104372298127928948183086133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69581532085285965455390755 104372298127928948183086133)
      ·
        refine ⟨9784902949493338892164325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104372298127928948183086133 9784902949493338892164325)
        ·
          refine ⟨1834669303030001042280811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9784902949493338892164325 1834669303030001042280811)
          ·
            refine ⟨2752003954545001563421217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834669303030001042280811 2752003954545001563421217)
            ·
              refine ⟨2064002965908751172565913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2752003954545001563421217 2064002965908751172565913)
              ·
                refine ⟨1548002224431563379424435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2064002965908751172565913 1548002224431563379424435)
                ·
                  refine ⟨2322003336647345069136653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548002224431563379424435 2322003336647345069136653)
                  ·
                    refine ⟨870751251242754400926245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2322003336647345069136653 870751251242754400926245)
                    ·
                      rfl

theorem cell22_2543673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 1, 3].length) (baseStart_2543673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543673 prefixEnd_2543673 := by exact prefixLift 2543673
  have htrace : WordTrace (prefixWord ++ tailWord_2543673) baseStart_2543673 baseEnd_2543673 := by
    simpa [prefixWord, tailWord_2543673, baseEnd_2543673] using wordTrace_append hprefix tailTrace_2543673
  have hstable : (prefixWord ++ tailWord_2543673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543673).length < 2 ^ (prefixWord ++ tailWord_2543673).sum := by decide
  have hdescent : baseEnd_2543673 < baseStart_2543673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543800 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 3, 4]
def baseStart_2543800 : Nat := 118140960795 + 2543800 * 2 ^ 59
def prefixEnd_2543800 : Nat := 4983230072969 + 3 ^ 40 * 2543800 * 2
def baseEnd_2543800 : Nat := 870794725938168403000855

theorem tailTrace_2543800 : CollatzResearch.WordTrace tailWord_2543800 prefixEnd_2543800 870794725938168403000855 := by
  unfold tailWord_2543800
  simp only [CollatzResearch.WordTrace]
  refine ⟨46390004092127260648530427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61853338789503014198040569 46390004092127260648530427)
  ·
    refine ⟨69585006138190890972795641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46390004092127260648530427 69585006138190890972795641)
    ·
      refine ⟨52188754603643168229596731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69585006138190890972795641 52188754603643168229596731)
      ·
        refine ⟨78283131905464752344395097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52188754603643168229596731 78283131905464752344395097)
        ·
          refine ⟨58712348929098564258296323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78283131905464752344395097 58712348929098564258296323)
          ·
            refine ⟨88068523393647846387444485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58712348929098564258296323 88068523393647846387444485)
            ·
              refine ⟨16512848136308971197645841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88068523393647846387444485 16512848136308971197645841)
              ·
                refine ⟨12384636102231728398234381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16512848136308971197645841 12384636102231728398234381)
                ·
                  refine ⟨4644238538336898149337893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12384636102231728398234381 4644238538336898149337893)
                  ·
                    refine ⟨870794725938168403000855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4644238538336898149337893 870794725938168403000855)
                    ·
                      rfl

theorem cell22_2543800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_2543800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543800 prefixEnd_2543800 := by exact prefixLift 2543800
  have htrace : WordTrace (prefixWord ++ tailWord_2543800) baseStart_2543800 baseEnd_2543800 := by
    simpa [prefixWord, tailWord_2543800, baseEnd_2543800] using wordTrace_append hprefix tailTrace_2543800
  have hstable : (prefixWord ++ tailWord_2543800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543800).length < 2 ^ (prefixWord ++ tailWord_2543800).sum := by decide
  have hdescent : baseEnd_2543800 < baseStart_2543800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543862 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_2543862 : Nat := 118140960795 + 2543862 * 2 ^ 59
def prefixEnd_2543862 : Nat := 4983230072969 + 3 ^ 40 * 2543862 * 2
def baseEnd_2543862 : Nat := 870815949805220907950665

theorem tailTrace_2543862 : CollatzResearch.WordTrace tailWord_2543862 prefixEnd_2543862 870815949805220907950665 := by
  unfold tailWord_2543862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5798891844376869117863615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61854846340019937257211893 5798891844376869117863615)
  ·
    refine ⟨8698337766565303676795423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5798891844376869117863615 8698337766565303676795423)
    ·
      refine ⟨13047506649847955515193135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8698337766565303676795423 13047506649847955515193135)
      ·
        refine ⟨19571259974771933272789703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13047506649847955515193135 19571259974771933272789703)
        ·
          refine ⟨29356889962157899909184555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19571259974771933272789703 29356889962157899909184555)
          ·
            refine ⟨44035334943236849863776833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29356889962157899909184555 44035334943236849863776833)
            ·
              refine ⟨33026501207427637397832625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44035334943236849863776833 33026501207427637397832625)
              ·
                refine ⟨24769875905570728048374469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33026501207427637397832625 24769875905570728048374469)
                ·
                  refine ⟨4644351732294511509070213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24769875905570728048374469 4644351732294511509070213)
                  ·
                    refine ⟨870815949805220907950665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4644351732294511509070213 870815949805220907950665)
                    ·
                      rfl

theorem cell22_2543862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_2543862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543862 prefixEnd_2543862 := by exact prefixLift 2543862
  have htrace : WordTrace (prefixWord ++ tailWord_2543862) baseStart_2543862 baseEnd_2543862 := by
    simpa [prefixWord, tailWord_2543862, baseEnd_2543862] using wordTrace_append hprefix tailTrace_2543862
  have hstable : (prefixWord ++ tailWord_2543862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543862).length < 2 ^ (prefixWord ++ tailWord_2543862).sum := by decide
  have hdescent : baseEnd_2543862 < baseStart_2543862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543879 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 1, 6]
def baseStart_2543879 : Nat := 118140960795 + 2543879 * 2 ^ 59
def prefixEnd_2543879 : Nat := 4983230072969 + 3 ^ 40 * 2543879 * 2
def baseEnd_2543879 : Nat := 870821769252638530275613

theorem tailTrace_2543879 : CollatzResearch.WordTrace tailWord_2543879 prefixEnd_2543879 870821769252638530275613 := by
  unfold tailWord_2543879
  simp only [CollatzResearch.WordTrace]
  refine ⟨92782889550968317789186691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61855259700645545192791127 92782889550968317789186691)
  ·
    refine ⟨139174334326452476683780037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92782889550968317789186691 139174334326452476683780037)
    ·
      refine ⟨26095187686209839378208757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139174334326452476683780037 26095187686209839378208757)
      ·
        refine ⟨2446423845582172441707071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26095187686209839378208757 2446423845582172441707071)
        ·
          refine ⟨3669635768373258662560607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2446423845582172441707071 3669635768373258662560607)
          ·
            refine ⟨5504453652559887993840911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3669635768373258662560607 5504453652559887993840911)
            ·
              refine ⟨8256680478839831990761367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5504453652559887993840911 8256680478839831990761367)
              ·
                refine ⟨12385020718259747986142051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8256680478839831990761367 12385020718259747986142051)
                ·
                  refine ⟨18577531077389621979213077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12385020718259747986142051 18577531077389621979213077)
                  ·
                    refine ⟨870821769252638530275613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18577531077389621979213077 870821769252638530275613)
                    ·
                      rfl

theorem cell22_2543879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_2543879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543879 prefixEnd_2543879 := by exact prefixLift 2543879
  have htrace : WordTrace (prefixWord ++ tailWord_2543879) baseStart_2543879 baseEnd_2543879 := by
    simpa [prefixWord, tailWord_2543879, baseEnd_2543879] using wordTrace_append hprefix tailTrace_2543879
  have hstable : (prefixWord ++ tailWord_2543879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543879).length < 2 ^ (prefixWord ++ tailWord_2543879).sum := by decide
  have hdescent : baseEnd_2543879 < baseStart_2543879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543898 : List Nat := [3, 1, 1, 3, 5, 1, 1, 2, 2, 3]
def baseStart_2543898 : Nat := 118140960795 + 2543898 * 2 ^ 59
def prefixEnd_2543898 : Nat := 4983230072969 + 3 ^ 40 * 2543898 * 2
def baseEnd_2543898 : Nat := 870828273340928814050555

theorem tailTrace_2543898 : CollatzResearch.WordTrace tailWord_2543898 prefixEnd_2543898 870828273340928814050555 := by
  unfold tailWord_2543898
  simp only [CollatzResearch.WordTrace]
  refine ⟨23195895634474871008532087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61855721691932989356085565 23195895634474871008532087)
  ·
    refine ⟨34793843451712306512798131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23195895634474871008532087 34793843451712306512798131)
    ·
      refine ⟨52190765177568459769197197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34793843451712306512798131 52190765177568459769197197)
      ·
        refine ⟨19571536941588172413448949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52190765177568459769197197 19571536941588172413448949)
        ·
          refine ⟨1834831588273891163760839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19571536941588172413448949 1834831588273891163760839)
          ·
            refine ⟨2752247382410836745641259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834831588273891163760839 2752247382410836745641259)
            ·
              refine ⟨4128371073616255118461889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2752247382410836745641259 4128371073616255118461889)
              ·
                refine ⟨3096278305212191338846417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4128371073616255118461889 3096278305212191338846417)
                ·
                  refine ⟨2322208728909143504134813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3096278305212191338846417 2322208728909143504134813)
                  ·
                    refine ⟨870828273340928814050555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2322208728909143504134813 870828273340928814050555)
                    ·
                      rfl

theorem cell22_2543898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_2543898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543898 prefixEnd_2543898 := by exact prefixLift 2543898
  have htrace : WordTrace (prefixWord ++ tailWord_2543898) baseStart_2543898 baseEnd_2543898 := by
    simpa [prefixWord, tailWord_2543898, baseEnd_2543898] using wordTrace_append hprefix tailTrace_2543898
  have hstable : (prefixWord ++ tailWord_2543898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543898).length < 2 ^ (prefixWord ++ tailWord_2543898).sum := by decide
  have hdescent : baseEnd_2543898 < baseStart_2543898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543920 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 1, 7]
def baseStart_2543920 : Nat := 118140960795 + 2543920 * 2 ^ 59
def prefixEnd_2543920 : Nat := 4983230072969 + 3 ^ 40 * 2543920 * 2
def baseEnd_2543920 : Nat := 870835804390528090000487

theorem tailTrace_2543920 : CollatzResearch.WordTrace tailWord_2543920 prefixEnd_2543920 870835804390528090000487 := by
  unfold tailWord_2543920
  simp only [CollatzResearch.WordTrace]
  refine ⟨46392192471909890895714607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61856256629213187860952809 46392192471909890895714607)
  ·
    refine ⟨69588288707864836343571911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46392192471909890895714607 69588288707864836343571911)
    ·
      refine ⟨104382433061797254515357867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69588288707864836343571911 104382433061797254515357867)
      ·
        refine ⟨156573649592695881773036801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104382433061797254515357867 156573649592695881773036801)
        ·
          refine ⟨117430237194521911329777601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156573649592695881773036801 117430237194521911329777601)
          ·
            refine ⟨88072677895891433497333201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117430237194521911329777601 88072677895891433497333201)
            ·
              refine ⟨66054508421918575122999901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88072677895891433497333201 66054508421918575122999901)
              ·
                refine ⟨24770440658219465671124963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66054508421918575122999901 24770440658219465671124963)
                ·
                  refine ⟨37155660987329198506687445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24770440658219465671124963 37155660987329198506687445)
                  ·
                    refine ⟨870835804390528090000487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37155660987329198506687445 870835804390528090000487)
                    ·
                      rfl

theorem cell22_2543920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_2543920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543920 prefixEnd_2543920 := by exact prefixLift 2543920
  have htrace : WordTrace (prefixWord ++ tailWord_2543920) baseStart_2543920 baseEnd_2543920 := by
    simpa [prefixWord, tailWord_2543920, baseEnd_2543920] using wordTrace_append hprefix tailTrace_2543920
  have hstable : (prefixWord ++ tailWord_2543920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543920).length < 2 ^ (prefixWord ++ tailWord_2543920).sum := by decide
  have hdescent : baseEnd_2543920 < baseStart_2543920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543966 : List Nat := [4, 4, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2543966 : Nat := 118140960795 + 2543966 * 2 ^ 59
def prefixEnd_2543966 : Nat := 4983230072969 + 3 ^ 40 * 2543966 * 2
def baseEnd_2543966 : Nat := 870851551130599303350347

theorem tailTrace_2543966 : CollatzResearch.WordTrace tailWord_2543966 prefixEnd_2543966 870851551130599303350347 := by
  unfold tailWord_2543966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11598257837706641455950469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61857375134435421098402501 11598257837706641455950469)
  ·
    refine ⟨2174673344569995272990713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11598257837706641455950469 2174673344569995272990713)
    ·
      refine ⟨1631005008427496454743035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2174673344569995272990713 1631005008427496454743035)
      ·
        refine ⟨2446507512641244682114553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1631005008427496454743035 2446507512641244682114553)
        ·
          refine ⟨1834880634480933511585915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2446507512641244682114553 1834880634480933511585915)
          ·
            refine ⟨2752320951721400267378873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834880634480933511585915 2752320951721400267378873)
            ·
              refine ⟨2064240713791050200534155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2752320951721400267378873 2064240713791050200534155)
              ·
                refine ⟨3096361070686575300801233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2064240713791050200534155 3096361070686575300801233)
                ·
                  refine ⟨2322270803014931475600925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3096361070686575300801233 2322270803014931475600925)
                  ·
                    refine ⟨870851551130599303350347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2322270803014931475600925 870851551130599303350347)
                    ·
                      rfl

theorem cell22_2543966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2543966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543966 prefixEnd_2543966 := by exact prefixLift 2543966
  have htrace : WordTrace (prefixWord ++ tailWord_2543966) baseStart_2543966 baseEnd_2543966 := by
    simpa [prefixWord, tailWord_2543966, baseEnd_2543966] using wordTrace_append hprefix tailTrace_2543966
  have hstable : (prefixWord ++ tailWord_2543966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543966).length < 2 ^ (prefixWord ++ tailWord_2543966).sum := by decide
  have hdescent : baseEnd_2543966 < baseStart_2543966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543967 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 6]
def baseStart_2543967 : Nat := 118140960795 + 2543967 * 2 ^ 59
def prefixEnd_2543967 : Nat := 4983230072969 + 3 ^ 40 * 2543967 * 2
def baseEnd_2543967 : Nat := 290283964483678544691781

theorem tailTrace_2543967 : CollatzResearch.WordTrace tailWord_2543967 prefixEnd_2543967 290283964483678544691781 := by
  unfold tailWord_2543967
  simp only [CollatzResearch.WordTrace]
  refine ⟨92786099174649508818390155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61857399449766339212260103 92786099174649508818390155)
  ·
    refine ⟨139179148761974263227585233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92786099174649508818390155 139179148761974263227585233)
    ·
      refine ⟨104384361571480697420688925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139179148761974263227585233 104384361571480697420688925)
      ·
        refine ⟨39144135589305261532758347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104384361571480697420688925 39144135589305261532758347)
        ·
          refine ⟨58716203383957892299137521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39144135589305261532758347 58716203383957892299137521)
          ·
            refine ⟨44037152537968419224353141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58716203383957892299137521 44037152537968419224353141)
            ·
              refine ⟨4128483050434539302283107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44037152537968419224353141 4128483050434539302283107)
              ·
                refine ⟨6192724575651808953424661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4128483050434539302283107 6192724575651808953424661)
                ·
                  refine ⟨290283964483678544691781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6192724575651808953424661 290283964483678544691781)
                  ·
                    rfl

theorem cell22_2543967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 6].length) (baseStart_2543967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543967 prefixEnd_2543967 := by exact prefixLift 2543967
  have htrace : WordTrace (prefixWord ++ tailWord_2543967) baseStart_2543967 baseEnd_2543967 := by
    simpa [prefixWord, tailWord_2543967, baseEnd_2543967] using wordTrace_append hprefix tailTrace_2543967
  have hstable : (prefixWord ++ tailWord_2543967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543967).length < 2 ^ (prefixWord ++ tailWord_2543967).sum := by decide
  have hdescent : baseEnd_2543967 < baseStart_2543967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543986 : List Nat := [3, 2, 1, 2, 1, 5, 1, 2, 1, 4]
def baseStart_2543986 : Nat := 118140960795 + 2543986 * 2 ^ 59
def prefixEnd_2543986 : Nat := 4983230072969 + 3 ^ 40 * 2543986 * 2
def baseEnd_2543986 : Nat := 870858397539325917850285

theorem tailTrace_2543986 : CollatzResearch.WordTrace tailWord_2543986 prefixEnd_2543986 870858397539325917850285 := by
  unfold tailWord_2543986
  simp only [CollatzResearch.WordTrace]
  refine ⟨23196698040395168765832953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61857861441053783375554541 23196698040395168765832953)
  ·
    refine ⟨17397523530296376574374715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23196698040395168765832953 17397523530296376574374715)
    ·
      refine ⟨26096285295444564861562073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17397523530296376574374715 26096285295444564861562073)
      ·
        refine ⟨19572213971583423646171555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26096285295444564861562073 19572213971583423646171555)
        ·
          refine ⟨29358320957375135469257333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19572213971583423646171555 29358320957375135469257333)
          ·
            refine ⟨2752342589753918950242875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29358320957375135469257333 2752342589753918950242875)
            ·
              refine ⟨4128513884630878425364313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2752342589753918950242875 4128513884630878425364313)
              ·
                refine ⟨3096385413473158819023235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4128513884630878425364313 3096385413473158819023235)
                ·
                  refine ⟨4644578120209738228534853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3096385413473158819023235 4644578120209738228534853)
                  ·
                    refine ⟨870858397539325917850285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4644578120209738228534853 870858397539325917850285)
                    ·
                      rfl

theorem cell22_2543986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_2543986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2543986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2543986 prefixEnd_2543986 := by exact prefixLift 2543986
  have htrace : WordTrace (prefixWord ++ tailWord_2543986) baseStart_2543986 baseEnd_2543986 := by
    simpa [prefixWord, tailWord_2543986, baseEnd_2543986] using wordTrace_append hprefix tailTrace_2543986
  have hstable : (prefixWord ++ tailWord_2543986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543986).length < 2 ^ (prefixWord ++ tailWord_2543986).sum := by decide
  have hdescent : baseEnd_2543986 < baseStart_2543986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544149 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 4, 4]
def baseStart_2544149 : Nat := 118140960795 + 2544149 * 2 ^ 59
def prefixEnd_2544149 : Nat := 4983230072969 + 3 ^ 40 * 2544149 * 2
def baseEnd_2544149 : Nat := 870914195770447826024785

theorem tailTrace_2544149 : CollatzResearch.WordTrace tailWord_2544149 prefixEnd_2544149 870914195770447826024785 := by
  unfold tailWord_2544149
  simp only [CollatzResearch.WordTrace]
  refine ⟨92792737259990153901515501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61861824839993435934343667 92792737259990153901515501)
  ·
    refine ⟨34797276472496307713068313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92792737259990153901515501 34797276472496307713068313)
    ·
      refine ⟨26097957354372230784801235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34797276472496307713068313 26097957354372230784801235)
      ·
        refine ⟨39146936031558346177201853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26097957354372230784801235 39146936031558346177201853)
        ·
          refine ⟨14680101011834379816450695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39146936031558346177201853 14680101011834379816450695)
          ·
            refine ⟨22020151517751569724676043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14680101011834379816450695 22020151517751569724676043)
            ·
              refine ⟨33030227276627354587014065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22020151517751569724676043 33030227276627354587014065)
              ·
                refine ⟨24772670457470515940260549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33030227276627354587014065 24772670457470515940260549)
                ·
                  refine ⟨4644875710775721738798853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24772670457470515940260549 4644875710775721738798853)
                  ·
                    refine ⟨870914195770447826024785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4644875710775721738798853 870914195770447826024785)
                    ·
                      rfl

theorem cell22_2544149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_2544149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544149 prefixEnd_2544149 := by exact prefixLift 2544149
  have htrace : WordTrace (prefixWord ++ tailWord_2544149) baseStart_2544149 baseEnd_2544149 := by
    simpa [prefixWord, tailWord_2544149, baseEnd_2544149] using wordTrace_append hprefix tailTrace_2544149
  have hstable : (prefixWord ++ tailWord_2544149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544149).length < 2 ^ (prefixWord ++ tailWord_2544149).sum := by decide
  have hdescent : baseEnd_2544149 < baseStart_2544149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544198 : List Nat := [6, 1, 1, 1, 2, 1, 3, 7]
def baseStart_2544198 : Nat := 118140960795 + 2544198 * 2 ^ 59
def prefixEnd_2544198 : Nat := 4983230072969 + 3 ^ 40 * 2544198 * 2
def baseEnd_2544198 : Nat := 96770107719092003505515

theorem tailTrace_2544198 : CollatzResearch.WordTrace tailWord_2544198 prefixEnd_2544198 96770107719092003505515 := by
  unfold tailWord_2544198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2899828888650394852189039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61863016291208423513366165 2899828888650394852189039)
  ·
    refine ⟨4349743332975592278283559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2899828888650394852189039 4349743332975592278283559)
    ·
      refine ⟨6524614999463388417425339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4349743332975592278283559 6524614999463388417425339)
      ·
        refine ⟨9786922499195082626138009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6524614999463388417425339 9786922499195082626138009)
        ·
          refine ⟨7340191874396311969603507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9786922499195082626138009 7340191874396311969603507)
          ·
            refine ⟨11010287811594467954405261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7340191874396311969603507 11010287811594467954405261)
            ·
              refine ⟨4128857929347925482901973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11010287811594467954405261 4128857929347925482901973)
              ·
                refine ⟨96770107719092003505515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4128857929347925482901973 96770107719092003505515)
                ·
                  rfl

theorem cell22_2544198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_2544198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544198 prefixEnd_2544198 := by exact prefixLift 2544198
  have htrace : WordTrace (prefixWord ++ tailWord_2544198) baseStart_2544198 baseEnd_2544198 := by
    simpa [prefixWord, tailWord_2544198, baseEnd_2544198] using wordTrace_append hprefix tailTrace_2544198
  have hstable : (prefixWord ++ tailWord_2544198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544198).length < 2 ^ (prefixWord ++ tailWord_2544198).sum := by decide
  have hdescent : baseEnd_2544198 < baseStart_2544198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544305 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 6]
def baseStart_2544305 : Nat := 118140960795 + 2544305 * 2 ^ 59
def prefixEnd_2544305 : Nat := 4983230072969 + 3 ^ 40 * 2544305 * 2
def baseEnd_2544305 : Nat := 290322532586171806374769

theorem tailTrace_2544305 : CollatzResearch.WordTrace tailWord_2544305 prefixEnd_2544305 290322532586171806374769 := by
  unfold tailWord_2544305
  simp only [CollatzResearch.WordTrace]
  refine ⟨92798427047424992544194369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61865618031616661696129579 92798427047424992544194369)
  ·
    refine ⟨69598820285568744408145777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92798427047424992544194369 69598820285568744408145777)
    ·
      refine ⟨52199115214176558306109333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69598820285568744408145777 52199115214176558306109333)
      ·
        refine ⟨2446833525664526170598875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52199115214176558306109333 2446833525664526170598875)
        ·
          refine ⟨3670250288496789255898313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2446833525664526170598875 3670250288496789255898313)
          ·
            refine ⟨2752687716372591941923735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3670250288496789255898313 2752687716372591941923735)
            ·
              refine ⟨4129031574558887912885603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2752687716372591941923735 4129031574558887912885603)
              ·
                refine ⟨6193547361838331869328405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4129031574558887912885603 6193547361838331869328405)
                ·
                  refine ⟨290322532586171806374769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6193547361838331869328405 290322532586171806374769)
                  ·
                    rfl

theorem cell22_2544305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 6].length) (baseStart_2544305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544305 prefixEnd_2544305 := by exact prefixLift 2544305
  have htrace : WordTrace (prefixWord ++ tailWord_2544305) baseStart_2544305 baseEnd_2544305 := by
    simpa [prefixWord, tailWord_2544305, baseEnd_2544305] using wordTrace_append hprefix tailTrace_2544305
  have hstable : (prefixWord ++ tailWord_2544305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544305).length < 2 ^ (prefixWord ++ tailWord_2544305).sum := by decide
  have hdescent : baseEnd_2544305 < baseStart_2544305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544316 : List Nat := [2, 2, 2, 3, 1, 1, 4, 7]
def baseStart_2544316 : Nat := 118140960795 + 2544316 * 2 ^ 59
def prefixEnd_2544316 : Nat := 4983230072969 + 3 ^ 40 * 2544316 * 2
def baseEnd_2544316 : Nat := 96774595920368339677697

theorem tailTrace_2544316 : CollatzResearch.WordTrace tailWord_2544316 prefixEnd_2544316 96774595920368339677697 := by
  unfold tailWord_2544316
  simp only [CollatzResearch.WordTrace]
  refine ⟨46399414125192570711422401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61865885500256760948563201 46399414125192570711422401)
  ·
    refine ⟨34799560593894428033566801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46399414125192570711422401 34799560593894428033566801)
    ·
      refine ⟨26099670445420821025175101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34799560593894428033566801 26099670445420821025175101)
      ·
        refine ⟨9787376417032807884440663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26099670445420821025175101 9787376417032807884440663)
        ·
          refine ⟨14681064625549211826660995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9787376417032807884440663 14681064625549211826660995)
          ·
            refine ⟨22021596938323817739991493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14681064625549211826660995 22021596938323817739991493)
            ·
              refine ⟨4129049425935715826248405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22021596938323817739991493 4129049425935715826248405)
              ·
                refine ⟨96774595920368339677697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4129049425935715826248405 96774595920368339677697)
                ·
                  rfl

theorem cell22_2544316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 7].length) (baseStart_2544316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544316 prefixEnd_2544316 := by exact prefixLift 2544316
  have htrace : WordTrace (prefixWord ++ tailWord_2544316) baseStart_2544316 baseEnd_2544316 := by
    simpa [prefixWord, tailWord_2544316, baseEnd_2544316] using wordTrace_append hprefix tailTrace_2544316
  have hstable : (prefixWord ++ tailWord_2544316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544316).length < 2 ^ (prefixWord ++ tailWord_2544316).sum := by decide
  have hdescent : baseEnd_2544316 < baseStart_2544316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544320 : List Nat := [2, 1, 1, 2, 4, 2, 4, 1, 2, 3]
def baseStart_2544320 : Nat := 118140960795 + 2544320 * 2 ^ 59
def prefixEnd_2544320 : Nat := 4983230072969 + 3 ^ 40 * 2544320 * 2
def baseEnd_2544320 : Nat := 870972732565060379999261

theorem tailTrace_2544320 : CollatzResearch.WordTrace tailWord_2544320 prefixEnd_2544320 870972732565060379999261 := by
  unfold tailWord_2544320
  simp only [CollatzResearch.WordTrace]
  refine ⟨46399487071185325052995207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61865982761580433403993609 46399487071185325052995207)
  ·
    refine ⟨69599230606777987579492811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46399487071185325052995207 69599230606777987579492811)
    ·
      refine ⟨104398845910166981369239217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69599230606777987579492811 104398845910166981369239217)
      ·
        refine ⟨78299134432625236026929413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104398845910166981369239217 78299134432625236026929413)
        ·
          refine ⟨14681087706117231755049265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78299134432625236026929413 14681087706117231755049265)
          ·
            refine ⟨11010815779587923816286949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14681087706117231755049265 11010815779587923816286949)
            ·
              refine ⟨2064527958672735715553803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11010815779587923816286949 2064527958672735715553803)
              ·
                refine ⟨3096791938009103573330705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2064527958672735715553803 3096791938009103573330705)
                ·
                  refine ⟨2322593953506827679998029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3096791938009103573330705 2322593953506827679998029)
                  ·
                    refine ⟨870972732565060379999261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2322593953506827679998029 870972732565060379999261)
                    ·
                      rfl

theorem cell22_2544320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 2, 3].length) (baseStart_2544320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544320 prefixEnd_2544320 := by exact prefixLift 2544320
  have htrace : WordTrace (prefixWord ++ tailWord_2544320) baseStart_2544320 baseEnd_2544320 := by
    simpa [prefixWord, tailWord_2544320, baseEnd_2544320] using wordTrace_append hprefix tailTrace_2544320
  have hstable : (prefixWord ++ tailWord_2544320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544320).length < 2 ^ (prefixWord ++ tailWord_2544320).sum := by decide
  have hdescent : baseEnd_2544320 < baseStart_2544320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544361 : List Nat := [1, 2, 1, 1, 1, 2, 5, 4, 5]
def baseStart_2544361 : Nat := 118140960795 + 2544361 * 2 ^ 59
def prefixEnd_2544361 : Nat := 4983230072969 + 3 ^ 40 * 2544361 * 2
def baseEnd_2544361 : Nat := 290328922567649979908045

theorem tailTrace_2544361 : CollatzResearch.WordTrace tailWord_2544361 prefixEnd_2544361 290328922567649979908045 := by
  unfold tailWord_2544361
  simp only [CollatzResearch.WordTrace]
  refine ⟨92800469535222114108232937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61866979690148076072155291 92800469535222114108232937)
  ·
    refine ⟨69600352151416585581174703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92800469535222114108232937 69600352151416585581174703)
    ·
      refine ⟨104400528227124878371762055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69600352151416585581174703 104400528227124878371762055)
      ·
        refine ⟨156600792340687317557643083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104400528227124878371762055 156600792340687317557643083)
        ·
          refine ⟨234901188511030976336464625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156600792340687317557643083 234901188511030976336464625)
          ·
            refine ⟨176175891383273232252348469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234901188511030976336464625 176175891383273232252348469)
            ·
              refine ⟨16516489817181865523657669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 176175891383273232252348469 16516489817181865523657669)
              ·
                refine ⟨3096841840721599785685813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16516489817181865523657669 3096841840721599785685813)
                ·
                  refine ⟨290328922567649979908045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3096841840721599785685813 290328922567649979908045)
                  ·
                    rfl

theorem cell22_2544361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 5].length) (baseStart_2544361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544361 prefixEnd_2544361 := by exact prefixLift 2544361
  have htrace : WordTrace (prefixWord ++ tailWord_2544361) baseStart_2544361 baseEnd_2544361 := by
    simpa [prefixWord, tailWord_2544361, baseEnd_2544361] using wordTrace_append hprefix tailTrace_2544361
  have hstable : (prefixWord ++ tailWord_2544361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544361).length < 2 ^ (prefixWord ++ tailWord_2544361).sum := by decide
  have hdescent : baseEnd_2544361 < baseStart_2544361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544376 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 2, 5]
def baseStart_2544376 : Nat := 118140960795 + 2544376 * 2 ^ 59
def prefixEnd_2544376 : Nat := 4983230072969 + 3 ^ 40 * 2544376 * 2
def baseEnd_2544376 : Nat := 870991902509494900599089

theorem tailTrace_2544376 : CollatzResearch.WordTrace tailWord_2544376 prefixEnd_2544376 870991902509494900599089 := by
  unfold tailWord_2544376
  simp only [CollatzResearch.WordTrace]
  refine ⟨46400508315083885835014491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61867344420111847780019321 46400508315083885835014491)
  ·
    refine ⟨69600762472625828752521737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46400508315083885835014491 69600762472625828752521737)
    ·
      refine ⟨52200571854469371564391303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69600762472625828752521737 52200571854469371564391303)
      ·
        refine ⟨78300857781704057346586955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52200571854469371564391303 78300857781704057346586955)
        ·
          refine ⟨117451286672556086019880433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78300857781704057346586955 117451286672556086019880433)
          ·
            refine ⟨88088465004417064514910325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117451286672556086019880433 88088465004417064514910325)
            ·
              refine ⟨8258293594164099798272843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88088465004417064514910325 8258293594164099798272843)
              ·
                refine ⟨12387440391246149697409265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8258293594164099798272843 12387440391246149697409265)
                ·
                  refine ⟨9290580293434612273056949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12387440391246149697409265 9290580293434612273056949)
                  ·
                    refine ⟨870991902509494900599089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9290580293434612273056949 870991902509494900599089)
                    ·
                      rfl

theorem cell22_2544376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_2544376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544376 prefixEnd_2544376 := by exact prefixLift 2544376
  have htrace : WordTrace (prefixWord ++ tailWord_2544376) baseStart_2544376 baseEnd_2544376 := by
    simpa [prefixWord, tailWord_2544376, baseEnd_2544376] using wordTrace_append hprefix tailTrace_2544376
  have hstable : (prefixWord ++ tailWord_2544376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544376).length < 2 ^ (prefixWord ++ tailWord_2544376).sum := by decide
  have hdescent : baseEnd_2544376 < baseStart_2544376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544429 : List Nat := [1, 5, 3, 2, 1, 1, 3, 1, 5]
def baseStart_2544429 : Nat := 118140960795 + 2544429 * 2 ^ 59
def prefixEnd_2544429 : Nat := 4983230072969 + 3 ^ 40 * 2544429 * 2
def baseEnd_2544429 : Nat := 290336681830873476341309

theorem tailTrace_2544429 : CollatzResearch.WordTrace tailWord_2544429 prefixEnd_2544429 290336681830873476341309 := by
  unfold tailWord_2544429
  simp only [CollatzResearch.WordTrace]
  refine ⟨92802949698975761721708341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61868633132650507814472227 92802949698975761721708341)
  ·
    refine ⟨8700276534278977661410157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92802949698975761721708341 8700276534278977661410157)
    ·
      refine ⟨3262603700354616623028809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8700276534278977661410157 3262603700354616623028809)
      ·
        refine ⟨2446952775265962467271607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3262603700354616623028809 2446952775265962467271607)
        ·
          refine ⟨3670429162898943700907411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2446952775265962467271607 3670429162898943700907411)
          ·
            refine ⟨5505643744348415551361117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3670429162898943700907411 5505643744348415551361117)
            ·
              refine ⟨2064616404130655831760419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5505643744348415551361117 2064616404130655831760419)
              ·
                refine ⟨3096924606195983747640629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2064616404130655831760419 3096924606195983747640629)
                ·
                  refine ⟨290336681830873476341309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3096924606195983747640629 290336681830873476341309)
                  ·
                    rfl

theorem cell22_2544429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_2544429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544429 prefixEnd_2544429 := by exact prefixLift 2544429
  have htrace : WordTrace (prefixWord ++ tailWord_2544429) baseStart_2544429 baseEnd_2544429 := by
    simpa [prefixWord, tailWord_2544429, baseEnd_2544429] using wordTrace_append hprefix tailTrace_2544429
  have hstable : (prefixWord ++ tailWord_2544429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544429).length < 2 ^ (prefixWord ++ tailWord_2544429).sum := by decide
  have hdescent : baseEnd_2544429 < baseStart_2544429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544451 : List Nat := [1, 1, 1, 3, 1, 4, 3, 8]
def baseStart_2544451 : Nat := 118140960795 + 2544451 * 2 ^ 59
def prefixEnd_2544451 : Nat := 4983230072969 + 3 ^ 40 * 2544451 * 2
def baseEnd_2544451 : Nat := 96779730726913300552651

theorem tailTrace_2544451 : CollatzResearch.WordTrace tailWord_2544451 prefixEnd_2544451 96779730726913300552651 := by
  unfold tailWord_2544451
  simp only [CollatzResearch.WordTrace]
  refine ⟨92803752104896059479009207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61869168069930706319339471 92803752104896059479009207)
  ·
    refine ⟨139205628157344089218513811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92803752104896059479009207 139205628157344089218513811)
    ·
      refine ⟨208808442236016133827770717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139205628157344089218513811 208808442236016133827770717)
      ·
        refine ⟨78303165838506050185414019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208808442236016133827770717 78303165838506050185414019)
        ·
          refine ⟨117454748757759075278121029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78303165838506050185414019 117454748757759075278121029)
          ·
            refine ⟨22022765392079826614647693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117454748757759075278121029 22022765392079826614647693)
            ·
              refine ⟨8258537022029934980492885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22022765392079826614647693 8258537022029934980492885)
              ·
                refine ⟨96779730726913300552651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8258537022029934980492885 96779730726913300552651)
                ·
                  rfl

theorem cell22_2544451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 8].length) (baseStart_2544451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544451 prefixEnd_2544451 := by exact prefixLift 2544451
  have htrace : WordTrace (prefixWord ++ tailWord_2544451) baseStart_2544451 baseEnd_2544451 := by
    simpa [prefixWord, tailWord_2544451, baseEnd_2544451] using wordTrace_append hprefix tailTrace_2544451
  have hstable : (prefixWord ++ tailWord_2544451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544451).length < 2 ^ (prefixWord ++ tailWord_2544451).sum := by decide
  have hdescent : baseEnd_2544451 < baseStart_2544451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544545 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 2, 5]
def baseStart_2544545 : Nat := 118140960795 + 2544545 * 2 ^ 59
def prefixEnd_2544545 : Nat := 4983230072969 + 3 ^ 40 * 2544545 * 2
def baseEnd_2544545 : Nat := 871049754663234793123571

theorem tailTrace_2544545 : CollatzResearch.WordTrace tailWord_2544545 prefixEnd_2544545 871049754663234793123571 := by
  unfold tailWord_2544545
  simp only [CollatzResearch.WordTrace]
  refine ⟨92807180566555513532931089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61871453711037009021954059 92807180566555513532931089)
  ·
    refine ⟨69605385424916635149698317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92807180566555513532931089 69605385424916635149698317)
    ·
      refine ⟨26102019534343738181136869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69605385424916635149698317 26102019534343738181136869)
      ·
        refine ⟨4894128662689450908963163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26102019534343738181136869 4894128662689450908963163)
        ·
          refine ⟨7341192994034176363444745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4894128662689450908963163 7341192994034176363444745)
          ·
            refine ⟨5505894745525632272583559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7341192994034176363444745 5505894745525632272583559)
            ·
              refine ⟨8258842118288448408875339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5505894745525632272583559 8258842118288448408875339)
              ·
                refine ⟨12388263177432672613313009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8258842118288448408875339 12388263177432672613313009)
                ·
                  refine ⟨9291197383074504459984757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12388263177432672613313009 9291197383074504459984757)
                  ·
                    refine ⟨871049754663234793123571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9291197383074504459984757 871049754663234793123571)
                    ·
                      rfl

theorem cell22_2544545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_2544545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544545 prefixEnd_2544545 := by exact prefixLift 2544545
  have htrace : WordTrace (prefixWord ++ tailWord_2544545) baseStart_2544545 baseEnd_2544545 := by
    simpa [prefixWord, tailWord_2544545, baseEnd_2544545] using wordTrace_append hprefix tailTrace_2544545
  have hstable : (prefixWord ++ tailWord_2544545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544545).length < 2 ^ (prefixWord ++ tailWord_2544545).sum := by decide
  have hdescent : baseEnd_2544545 < baseStart_2544545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544605 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2544605 : Nat := 118140960795 + 2544605 * 2 ^ 59
def prefixEnd_2544605 : Nat := 4983230072969 + 3 ^ 40 * 2544605 * 2
def baseEnd_2544605 : Nat := 871070293889414636623387

theorem tailTrace_2544605 : CollatzResearch.WordTrace tailWord_2544605 prefixEnd_2544605 871070293889414636623387 := by
  unfold tailWord_2544605
  simp only [CollatzResearch.WordTrace]
  refine ⟨92809368946338143780115269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61872912630892095853410179 92809368946338143780115269)
  ·
    refine ⟨17401756677438401958771613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92809368946338143780115269 17401756677438401958771613)
    ·
      refine ⟨6525658754039400734539355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17401756677438401958771613 6525658754039400734539355)
      ·
        refine ⟨9788488131059101101809033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6525658754039400734539355 9788488131059101101809033)
        ·
          refine ⟨7341366098294325826356775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9788488131059101101809033 7341366098294325826356775)
          ·
            refine ⟨11012049147441488739535163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7341366098294325826356775 11012049147441488739535163)
            ·
              refine ⟨16518073721162233109302745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11012049147441488739535163 16518073721162233109302745)
              ·
                refine ⟨12388555290871674831977059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16518073721162233109302745 12388555290871674831977059)
                ·
                  refine ⟨18582832936307512247965589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12388555290871674831977059 18582832936307512247965589)
                  ·
                    refine ⟨871070293889414636623387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18582832936307512247965589 871070293889414636623387)
                    ·
                      rfl

theorem cell22_2544605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2544605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544605 prefixEnd_2544605 := by exact prefixLift 2544605
  have htrace : WordTrace (prefixWord ++ tailWord_2544605) baseStart_2544605 baseEnd_2544605 := by
    simpa [prefixWord, tailWord_2544605, baseEnd_2544605] using wordTrace_append hprefix tailTrace_2544605
  have hstable : (prefixWord ++ tailWord_2544605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544605).length < 2 ^ (prefixWord ++ tailWord_2544605).sum := by decide
  have hdescent : baseEnd_2544605 < baseStart_2544605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544607 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 1, 5]
def baseStart_2544607 : Nat := 118140960795 + 2544607 * 2 ^ 59
def prefixEnd_2544607 : Nat := 4983230072969 + 3 ^ 40 * 2544607 * 2
def baseEnd_2544607 : Nat := 871070978530287298073381

theorem tailTrace_2544607 : CollatzResearch.WordTrace tailWord_2544607 prefixEnd_2544607 871070978530287298073381 := by
  unfold tailWord_2544607
  simp only [CollatzResearch.WordTrace]
  refine ⟨92809441892330898121688075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61872961261553932081125383 92809441892330898121688075)
  ·
    refine ⟨139214162838496347182532113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92809441892330898121688075 139214162838496347182532113)
    ·
      refine ⟨104410622128872260386899085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139214162838496347182532113 104410622128872260386899085)
      ·
        refine ⟨39153983298327097645087157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104410622128872260386899085 39153983298327097645087157)
        ·
          refine ⟨3670685934218165404226921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39153983298327097645087157 3670685934218165404226921)
          ·
            refine ⟨2753014450663624053170191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3670685934218165404226921 2753014450663624053170191)
            ·
              refine ⟨4129521675995436079755287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753014450663624053170191 4129521675995436079755287)
              ·
                refine ⟨6194282513993154119632931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4129521675995436079755287 6194282513993154119632931)
                ·
                  refine ⟨9291423770989731179449397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6194282513993154119632931 9291423770989731179449397)
                  ·
                    refine ⟨871070978530287298073381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9291423770989731179449397 871070978530287298073381)
                    ·
                      rfl

theorem cell22_2544607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 5].length) (baseStart_2544607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544607 prefixEnd_2544607 := by exact prefixLift 2544607
  have htrace : WordTrace (prefixWord ++ tailWord_2544607) baseStart_2544607 baseEnd_2544607 := by
    simpa [prefixWord, tailWord_2544607, baseEnd_2544607] using wordTrace_append hprefix tailTrace_2544607
  have hstable : (prefixWord ++ tailWord_2544607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544607).length < 2 ^ (prefixWord ++ tailWord_2544607).sum := by decide
  have hdescent : baseEnd_2544607 < baseStart_2544607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544626 : List Nat := [3, 2, 1, 5, 1, 2, 1, 3, 4]
def baseStart_2544626 : Nat := 118140960795 + 2544626 * 2 ^ 59
def prefixEnd_2544626 : Nat := 4983230072969 + 3 ^ 40 * 2544626 * 2
def baseEnd_2544626 : Nat := 290359160872859193949441

theorem tailTrace_2544626 : CollatzResearch.WordTrace tailWord_2544626 prefixEnd_2544626 290359160872859193949441 := by
  unfold tailWord_2544626
  simp only [CollatzResearch.WordTrace]
  refine ⟨23202533719815516091657433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61873423252841376244419821 23202533719815516091657433)
  ·
    refine ⟨17401900289861637068743075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23202533719815516091657433 17401900289861637068743075)
    ·
      refine ⟨26102850434792455603114613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17401900289861637068743075 26102850434792455603114613)
      ·
        refine ⟨2447142228261792712791995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26102850434792455603114613 2447142228261792712791995)
        ·
          refine ⟨3670713342392689069187993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2447142228261792712791995 3670713342392689069187993)
          ·
            refine ⟨2753035006794516801890995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3670713342392689069187993 2753035006794516801890995)
            ·
              refine ⟨4129552510191775202836493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753035006794516801890995 4129552510191775202836493)
              ·
                refine ⟨1548582191321915701063685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4129552510191775202836493 1548582191321915701063685)
                ·
                  refine ⟨290359160872859193949441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1548582191321915701063685 290359160872859193949441)
                  ·
                    rfl

theorem cell22_2544626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_2544626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544626 prefixEnd_2544626 := by exact prefixLift 2544626
  have htrace : WordTrace (prefixWord ++ tailWord_2544626) baseStart_2544626 baseEnd_2544626 := by
    simpa [prefixWord, tailWord_2544626, baseEnd_2544626] using wordTrace_append hprefix tailTrace_2544626
  have hstable : (prefixWord ++ tailWord_2544626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544626).length < 2 ^ (prefixWord ++ tailWord_2544626).sum := by decide
  have hdescent : baseEnd_2544626 < baseStart_2544626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544652 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 3, 3]
def baseStart_2544652 : Nat := 118140960795 + 2544652 * 2 ^ 59
def prefixEnd_2544652 : Nat := 4983230072969 + 3 ^ 40 * 2544652 * 2
def baseEnd_2544652 : Nat := 871086382949922180698243

theorem tailTrace_2544652 : CollatzResearch.WordTrace tailWord_2544652 prefixEnd_2544652 871086382949922180698243 := by
  unfold tailWord_2544652
  simp only [CollatzResearch.WordTrace]
  refine ⟨46405541588583935403538105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61874055451445247204717473 46405541588583935403538105)
  ·
    refine ⟨34804156191437951552653579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46405541588583935403538105 34804156191437951552653579)
    ·
      refine ⟨52206234287156927328980369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34804156191437951552653579 52206234287156927328980369)
      ·
        refine ⟨39154675715367695496735277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52206234287156927328980369 39154675715367695496735277)
        ·
          refine ⟨14683003393262885811275729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39154675715367695496735277 14683003393262885811275729)
          ·
            refine ⟨11012252544947164358456797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14683003393262885811275729 11012252544947164358456797)
            ·
              refine ⟨4129594704355186634421299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11012252544947164358456797 4129594704355186634421299)
              ·
                refine ⟨6194392056532779951631949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4129594704355186634421299 6194392056532779951631949)
                ·
                  refine ⟨2322897021199792481861981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6194392056532779951631949 2322897021199792481861981)
                  ·
                    refine ⟨871086382949922180698243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2322897021199792481861981 871086382949922180698243)
                    ·
                      rfl

theorem cell22_2544652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_2544652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544652 prefixEnd_2544652 := by exact prefixLift 2544652
  have htrace : WordTrace (prefixWord ++ tailWord_2544652) baseStart_2544652 baseEnd_2544652 := by
    simpa [prefixWord, tailWord_2544652, baseEnd_2544652] using wordTrace_append hprefix tailTrace_2544652
  have hstable : (prefixWord ++ tailWord_2544652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544652).length < 2 ^ (prefixWord ++ tailWord_2544652).sum := by decide
  have hdescent : baseEnd_2544652 < baseStart_2544652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544658 : List Nat := [3, 2, 5, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2544658 : Nat := 118140960795 + 2544658 * 2 ^ 59
def prefixEnd_2544658 : Nat := 4983230072969 + 3 ^ 40 * 2544658 * 2
def baseEnd_2544658 : Nat := 871088436872540165048225

theorem tailTrace_2544658 : CollatzResearch.WordTrace tailWord_2544658 prefixEnd_2544658 871088436872540165048225 := by
  unfold tailWord_2544658
  simp only [CollatzResearch.WordTrace]
  refine ⟨23202825503786533457948657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61874201343430755887863085 23202825503786533457948657)
  ·
    refine ⟨17402119127839900093461493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23202825503786533457948657 17402119127839900093461493)
    ·
      refine ⟨1631448668234990633762015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17402119127839900093461493 1631448668234990633762015)
      ·
        refine ⟨2447173002352485950643023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1631448668234990633762015 2447173002352485950643023)
        ·
          refine ⟨3670759503528728925964535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2447173002352485950643023 3670759503528728925964535)
          ·
            refine ⟨5506139255293093388946803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3670759503528728925964535 5506139255293093388946803)
            ·
              refine ⟨8259208882939640083420205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5506139255293093388946803 8259208882939640083420205)
              ·
                refine ⟨3097203331102365031282577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8259208882939640083420205 3097203331102365031282577)
                ·
                  refine ⟨2322902498326773773461933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3097203331102365031282577 2322902498326773773461933)
                  ·
                    refine ⟨871088436872540165048225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2322902498326773773461933 871088436872540165048225)
                    ·
                      rfl

theorem cell22_2544658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2544658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544658 prefixEnd_2544658 := by exact prefixLift 2544658
  have htrace : WordTrace (prefixWord ++ tailWord_2544658) baseStart_2544658 baseEnd_2544658 := by
    simpa [prefixWord, tailWord_2544658, baseEnd_2544658] using wordTrace_append hprefix tailTrace_2544658
  have hstable : (prefixWord ++ tailWord_2544658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544658).length < 2 ^ (prefixWord ++ tailWord_2544658).sum := by decide
  have hdescent : baseEnd_2544658 < baseStart_2544658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544746 : List Nat := [3, 1, 3, 2, 2, 3, 2, 1, 1, 4]
def baseStart_2544746 : Nat := 118140960795 + 2544746 * 2 ^ 59
def prefixEnd_2544746 : Nat := 4983230072969 + 3 ^ 40 * 2544746 * 2
def baseEnd_2544746 : Nat := 871118561070937268847955

theorem tailTrace_2544746 : CollatzResearch.WordTrace tailWord_2544746 prefixEnd_2544746 871118561070937268847955 := by
  unfold tailWord_2544746
  simp only [CollatzResearch.WordTrace]
  refine ⟨23203627909706831215249523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61876341092551549907332061 23203627909706831215249523)
  ·
    refine ⟨34805441864560246822874285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23203627909706831215249523 34805441864560246822874285)
    ·
      refine ⟨13052040699210092558577857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34805441864560246822874285 13052040699210092558577857)
      ·
        refine ⟨9789030524407569418933393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13052040699210092558577857 9789030524407569418933393)
        ·
          refine ⟨7341772893305677064200045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9789030524407569418933393 7341772893305677064200045)
          ·
            refine ⟨2753164834989628899075017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7341772893305677064200045 2753164834989628899075017)
            ·
              refine ⟨2064873626242221674306263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2753164834989628899075017 2064873626242221674306263)
              ·
                refine ⟨3097310439363332511459395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2064873626242221674306263 3097310439363332511459395)
                ·
                  refine ⟨4645965659044998767189093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3097310439363332511459395 4645965659044998767189093)
                  ·
                    refine ⟨871118561070937268847955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4645965659044998767189093 871118561070937268847955)
                    ·
                      rfl

theorem cell22_2544746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_2544746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544746 prefixEnd_2544746 := by exact prefixLift 2544746
  have htrace : WordTrace (prefixWord ++ tailWord_2544746) baseStart_2544746 baseEnd_2544746 := by
    simpa [prefixWord, tailWord_2544746, baseEnd_2544746] using wordTrace_append hprefix tailTrace_2544746
  have hstable : (prefixWord ++ tailWord_2544746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544746).length < 2 ^ (prefixWord ++ tailWord_2544746).sum := by decide
  have hdescent : baseEnd_2544746 < baseStart_2544746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544776 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 1, 5]
def baseStart_2544776 : Nat := 118140960795 + 2544776 * 2 ^ 59
def prefixEnd_2544776 : Nat := 4983230072969 + 3 ^ 40 * 2544776 * 2
def baseEnd_2544776 : Nat := 871128830684027190597863

theorem tailTrace_2544776 : CollatzResearch.WordTrace tailWord_2544776 prefixEnd_2544776 871128830684027190597863 := by
  unfold tailWord_2544776
  simp only [CollatzResearch.WordTrace]
  refine ⟨46407802914359319992295091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61877070552479093323060121 46407802914359319992295091)
  ·
    refine ⟨69611704371538979988442637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46407802914359319992295091 69611704371538979988442637)
    ·
      refine ⟨26104389139327117495665989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69611704371538979988442637 26104389139327117495665989)
      ·
        refine ⟨4894572963623834530437373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26104389139327117495665989 4894572963623834530437373)
        ·
          refine ⟨1835464861358937948914015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4894572963623834530437373 1835464861358937948914015)
          ·
            refine ⟨2753197292038406923371023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835464861358937948914015 2753197292038406923371023)
            ·
              refine ⟨4129795938057610385056535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753197292038406923371023 4129795938057610385056535)
              ·
                refine ⟨6194693907086415577584803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4129795938057610385056535 6194693907086415577584803)
                ·
                  refine ⟨9292040860629623366377205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6194693907086415577584803 9292040860629623366377205)
                  ·
                    refine ⟨871128830684027190597863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9292040860629623366377205 871128830684027190597863)
                    ·
                      rfl

theorem cell22_2544776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_2544776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544776 prefixEnd_2544776 := by exact prefixLift 2544776
  have htrace : WordTrace (prefixWord ++ tailWord_2544776) baseStart_2544776 baseEnd_2544776 := by
    simpa [prefixWord, tailWord_2544776, baseEnd_2544776] using wordTrace_append hprefix tailTrace_2544776
  have hstable : (prefixWord ++ tailWord_2544776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544776).length < 2 ^ (prefixWord ++ tailWord_2544776).sum := by decide
  have hdescent : baseEnd_2544776 < baseStart_2544776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544787 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 3, 3]
def baseStart_2544787 : Nat := 118140960795 + 2544787 * 2 ^ 59
def prefixEnd_2544787 : Nat := 4983230072969 + 3 ^ 40 * 2544787 * 2
def baseEnd_2544787 : Nat := 871132596208826828572829

theorem tailTrace_2544787 : CollatzResearch.WordTrace tailWord_2544787 prefixEnd_2544787 871132596208826828572829 := by
  unfold tailWord_2544787
  simp only [CollatzResearch.WordTrace]
  refine ⟨92816007031678788863240615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61877338021119192575493743 92816007031678788863240615)
  ·
    refine ⟨139224010547518183294860923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92816007031678788863240615 139224010547518183294860923)
    ·
      refine ⟨208836015821277274942291385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139224010547518183294860923 208836015821277274942291385)
      ·
        refine ⟨156627011865957956206718539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208836015821277274942291385 156627011865957956206718539)
        ·
          refine ⟨234940517798936934310077809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156627011865957956206718539 234940517798936934310077809)
          ·
            refine ⟨176205388349202700732558357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234940517798936934310077809 176205388349202700732558357)
            ·
              refine ⟨8259627578868876596838673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 176205388349202700732558357 8259627578868876596838673)
              ·
                refine ⟨6194720684151657447629005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8259627578868876596838673 6194720684151657447629005)
                ·
                  refine ⟨2323020256556871542860877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6194720684151657447629005 2323020256556871542860877)
                  ·
                    refine ⟨871132596208826828572829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2323020256556871542860877 871132596208826828572829)
                    ·
                      rfl

theorem cell22_2544787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 3].length) (baseStart_2544787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544787 prefixEnd_2544787 := by exact prefixLift 2544787
  have htrace : WordTrace (prefixWord ++ tailWord_2544787) baseStart_2544787 baseEnd_2544787 := by
    simpa [prefixWord, tailWord_2544787, baseEnd_2544787] using wordTrace_append hprefix tailTrace_2544787
  have hstable : (prefixWord ++ tailWord_2544787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544787).length < 2 ^ (prefixWord ++ tailWord_2544787).sum := by decide
  have hdescent : baseEnd_2544787 < baseStart_2544787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544800 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 9]
def baseStart_2544800 : Nat := 118140960795 + 2544800 * 2 ^ 59
def prefixEnd_2544800 : Nat := 4983230072969 + 3 ^ 40 * 2544800 * 2
def baseEnd_2544800 : Nat := 290379015458166375999263

theorem tailTrace_2544800 : CollatzResearch.WordTrace tailWord_2544800 prefixEnd_2544800 290379015458166375999263 := by
  unfold tailWord_2544800
  simp only [CollatzResearch.WordTrace]
  refine ⟨46408240590315846041731927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61877654120421128055642569 46408240590315846041731927)
  ·
    refine ⟨69612360885473769062597891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46408240590315846041731927 69612360885473769062597891)
    ·
      refine ⟨104418541328210653593896837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69612360885473769062597891 104418541328210653593896837)
      ·
        refine ⟨19578476499039497548855657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104418541328210653593896837 19578476499039497548855657)
        ·
          refine ⟨14683857374279623161641743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19578476499039497548855657 14683857374279623161641743)
          ·
            refine ⟨22025786061419434742462615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14683857374279623161641743 22025786061419434742462615)
            ·
              refine ⟨33038679092129152113693923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22025786061419434742462615 33038679092129152113693923)
              ·
                refine ⟨49558018638193728170540885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33038679092129152113693923 49558018638193728170540885)
                ·
                  refine ⟨290379015458166375999263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49558018638193728170540885 290379015458166375999263)
                  ·
                    rfl

theorem cell22_2544800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 9].length) (baseStart_2544800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544800 prefixEnd_2544800 := by exact prefixLift 2544800
  have htrace : WordTrace (prefixWord ++ tailWord_2544800) baseStart_2544800 baseEnd_2544800 := by
    simpa [prefixWord, tailWord_2544800, baseEnd_2544800] using wordTrace_append hprefix tailTrace_2544800
  have hstable : (prefixWord ++ tailWord_2544800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544800).length < 2 ^ (prefixWord ++ tailWord_2544800).sum := by decide
  have hdescent : baseEnd_2544800 < baseStart_2544800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544815 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 4, 5]
def baseStart_2544815 : Nat := 118140960795 + 2544815 * 2 ^ 59
def prefixEnd_2544815 : Nat := 4983230072969 + 3 ^ 40 * 2544815 * 2
def baseEnd_2544815 : Nat := 871142181181044088872743

theorem tailTrace_2544815 : CollatzResearch.WordTrace tailWord_2544815 prefixEnd_2544815 871142181181044088872743 := by
  unfold tailWord_2544815
  simp only [CollatzResearch.WordTrace]
  refine ⟨92817028275577349645259899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61878018850384899763506599 92817028275577349645259899)
  ·
    refine ⟨139225542413366024467889849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92817028275577349645259899 139225542413366024467889849)
    ·
      refine ⟨104419156810024518350917387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139225542413366024467889849 104419156810024518350917387)
      ·
        refine ⟨156628735215036777526376081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104419156810024518350917387 156628735215036777526376081)
        ·
          refine ⟨117471551411277583144782061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156628735215036777526376081 117471551411277583144782061)
          ·
            refine ⟨44051831779229093679293273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117471551411277583144782061 44051831779229093679293273)
            ·
              refine ⟨33038873834421820259469955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44051831779229093679293273 33038873834421820259469955)
              ·
                refine ⟨49558310751632730389204933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33038873834421820259469955 49558310751632730389204933)
                ·
                  refine ⟨9292183265931136947975925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49558310751632730389204933 9292183265931136947975925)
                  ·
                    refine ⟨871142181181044088872743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9292183265931136947975925 871142181181044088872743)
                    ·
                      rfl

theorem cell22_2544815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_2544815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544815 prefixEnd_2544815 := by exact prefixLift 2544815
  have htrace : WordTrace (prefixWord ++ tailWord_2544815) baseStart_2544815 baseEnd_2544815 := by
    simpa [prefixWord, tailWord_2544815, baseEnd_2544815] using wordTrace_append hprefix tailTrace_2544815
  have hstable : (prefixWord ++ tailWord_2544815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544815).length < 2 ^ (prefixWord ++ tailWord_2544815).sum := by decide
  have hdescent : baseEnd_2544815 < baseStart_2544815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544817 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 7]
def baseStart_2544817 : Nat := 118140960795 + 2544817 * 2 ^ 59
def prefixEnd_2544817 : Nat := 4983230072969 + 3 ^ 40 * 2544817 * 2
def baseEnd_2544817 : Nat := 290380955273972250107579

theorem tailTrace_2544817 : CollatzResearch.WordTrace tailWord_2544817 prefixEnd_2544817 290380955273972250107579 := by
  unfold tailWord_2544817
  simp only [CollatzResearch.WordTrace]
  refine ⟨92817101221570103986832705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61878067481046735991221803 92817101221570103986832705)
  ·
    refine ⟨69612825916177577990124529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92817101221570103986832705 69612825916177577990124529)
    ·
      refine ⟨52209619437133183492593397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69612825916177577990124529 52209619437133183492593397)
      ·
        refine ⟨4894651822231235952430631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52209619437133183492593397 4894651822231235952430631)
        ·
          refine ⟨7341977733346853928645947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4894651822231235952430631 7341977733346853928645947)
          ·
            refine ⟨11012966600020280892968921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7341977733346853928645947 11012966600020280892968921)
            ·
              refine ⟨8259724950015210669726691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11012966600020280892968921 8259724950015210669726691)
              ·
                refine ⟨12389587425022816004590037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8259724950015210669726691 12389587425022816004590037)
                ·
                  refine ⟨290380955273972250107579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12389587425022816004590037 290380955273972250107579)
                  ·
                    rfl

theorem cell22_2544817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 7].length) (baseStart_2544817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544817 prefixEnd_2544817 := by exact prefixLift 2544817
  have htrace : WordTrace (prefixWord ++ tailWord_2544817) baseStart_2544817 baseEnd_2544817 := by
    simpa [prefixWord, tailWord_2544817, baseEnd_2544817] using wordTrace_append hprefix tailTrace_2544817
  have hstable : (prefixWord ++ tailWord_2544817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544817).length < 2 ^ (prefixWord ++ tailWord_2544817).sum := by decide
  have hdescent : baseEnd_2544817 < baseStart_2544817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544847 : List Nat := [1, 1, 2, 1, 1, 3, 2, 6, 1, 4]
def baseStart_2544847 : Nat := 118140960795 + 2544847 * 2 ^ 59
def prefixEnd_2544847 : Nat := 4983230072969 + 3 ^ 40 * 2544847 * 2
def baseEnd_2544847 : Nat := 871153135435006672072645

theorem tailTrace_2544847 : CollatzResearch.WordTrace tailWord_2544847 prefixEnd_2544847 871153135435006672072645 := by
  unfold tailWord_2544847
  simp only [CollatzResearch.WordTrace]
  refine ⟨92818195411461419110424795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61878796940974279406949863 92818195411461419110424795)
  ·
    refine ⟨139227293117192128665637193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92818195411461419110424795 139227293117192128665637193)
    ·
      refine ⟨104420469837894096499227895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139227293117192128665637193 104420469837894096499227895)
      ·
        refine ⟨156630704756841144748841843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104420469837894096499227895 156630704756841144748841843)
        ·
          refine ⟨234946057135261717123262765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156630704756841144748841843 234946057135261717123262765)
          ·
            refine ⟨88104771425723143921223537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234946057135261717123262765 88104771425723143921223537)
            ·
              refine ⟨66078578569292357940917653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88104771425723143921223537 66078578569292357940917653)
              ·
                refine ⟨3097433370435579278480515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66078578569292357940917653 3097433370435579278480515)
                ·
                  refine ⟨4646150055653368917720773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3097433370435579278480515 4646150055653368917720773)
                  ·
                    refine ⟨871153135435006672072645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4646150055653368917720773 871153135435006672072645)
                    ·
                      rfl

theorem cell22_2544847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 4].length) (baseStart_2544847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544847 prefixEnd_2544847 := by exact prefixLift 2544847
  have htrace : WordTrace (prefixWord ++ tailWord_2544847) baseStart_2544847 baseEnd_2544847 := by
    simpa [prefixWord, tailWord_2544847, baseEnd_2544847] using wordTrace_append hprefix tailTrace_2544847
  have hstable : (prefixWord ++ tailWord_2544847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544847).length < 2 ^ (prefixWord ++ tailWord_2544847).sum := by decide
  have hdescent : baseEnd_2544847 < baseStart_2544847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544894 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_2544894 : Nat := 118140960795 + 2544894 * 2 ^ 59
def prefixEnd_2544894 : Nat := 4983230072969 + 3 ^ 40 * 2544894 * 2
def baseEnd_2544894 : Nat := 871169224495514216147501

theorem tailTrace_2544894 : CollatzResearch.WordTrace tailWord_2544894 prefixEnd_2544894 871169224495514216147501 := by
  unfold tailWord_2544894
  simp only [CollatzResearch.WordTrace]
  refine ⟨11602488705286393267173217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61879939761527430758257157 11602488705286393267173217)
  ·
    refine ⟨8701866528964794950379913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11602488705286393267173217 8701866528964794950379913)
    ·
      refine ⟨6526399896723596212784935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8701866528964794950379913 6526399896723596212784935)
      ·
        refine ⟨9789599845085394319177403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6526399896723596212784935 9789599845085394319177403)
        ·
          refine ⟨14684399767628091478766105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9789599845085394319177403 14684399767628091478766105)
          ·
            refine ⟨11013299825721068609074579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14684399767628091478766105 11013299825721068609074579)
            ·
              refine ⟨16519949738581602913611869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11013299825721068609074579 16519949738581602913611869)
              ·
                refine ⟨6194981151968101092604451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16519949738581602913611869 6194981151968101092604451)
                ·
                  refine ⟨9292471727952151638906677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6194981151968101092604451 9292471727952151638906677)
                  ·
                    refine ⟨871169224495514216147501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9292471727952151638906677 871169224495514216147501)
                    ·
                      rfl

theorem cell22_2544894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_2544894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544894 prefixEnd_2544894 := by exact prefixLift 2544894
  have htrace : WordTrace (prefixWord ++ tailWord_2544894) baseStart_2544894 baseEnd_2544894 := by
    simpa [prefixWord, tailWord_2544894, baseEnd_2544894] using wordTrace_append hprefix tailTrace_2544894
  have hstable : (prefixWord ++ tailWord_2544894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544894).length < 2 ^ (prefixWord ++ tailWord_2544894).sum := by decide
  have hdescent : baseEnd_2544894 < baseStart_2544894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544928 : List Nat := [2, 1, 1, 5, 3, 2, 1, 2, 2, 3]
def baseStart_2544928 : Nat := 118140960795 + 2544928 * 2 ^ 59
def prefixEnd_2544928 : Nat := 4983230072969 + 3 ^ 40 * 2544928 * 2
def baseEnd_2544928 : Nat := 871180863390349460797397

theorem tailTrace_2544928 : CollatzResearch.WordTrace tailWord_2544928 prefixEnd_2544928 871180863390349460797397 := by
  unfold tailWord_2544928
  simp only [CollatzResearch.WordTrace]
  refine ⟨46410574862083984972061719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61880766482778646629415625 46410574862083984972061719)
  ·
    refine ⟨69615862293125977458092579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46410574862083984972061719 69615862293125977458092579)
    ·
      refine ⟨104423793439688966187138869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69615862293125977458092579 104423793439688966187138869)
      ·
        refine ⟨9789730634970840580044269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104423793439688966187138869 9789730634970840580044269)
        ·
          refine ⟨3671148988114065217516601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9789730634970840580044269 3671148988114065217516601)
          ·
            refine ⟨2753361741085548913137451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3671148988114065217516601 2753361741085548913137451)
            ·
              refine ⟨4130042611628323369706177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753361741085548913137451 4130042611628323369706177)
              ·
                refine ⟨3097531958721242527279633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4130042611628323369706177 3097531958721242527279633)
                ·
                  refine ⟨2323148969040931895459725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3097531958721242527279633 2323148969040931895459725)
                  ·
                    refine ⟨871180863390349460797397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2323148969040931895459725 871180863390349460797397)
                    ·
                      rfl

theorem cell22_2544928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 2, 3].length) (baseStart_2544928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2544928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2544928 prefixEnd_2544928 := by exact prefixLift 2544928
  have htrace : WordTrace (prefixWord ++ tailWord_2544928) baseStart_2544928 baseEnd_2544928 := by
    simpa [prefixWord, tailWord_2544928, baseEnd_2544928] using wordTrace_append hprefix tailTrace_2544928
  have hstable : (prefixWord ++ tailWord_2544928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544928).length < 2 ^ (prefixWord ++ tailWord_2544928).sum := by decide
  have hdescent : baseEnd_2544928 < baseStart_2544928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545029 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 6, 3]
def baseStart_2545029 : Nat := 118140960795 + 2545029 * 2 ^ 59
def prefixEnd_2545029 : Nat := 4983230072969 + 3 ^ 40 * 2545029 * 2
def baseEnd_2545029 : Nat := 871215437754418864022087

theorem tailTrace_2545029 : CollatzResearch.WordTrace tailWord_2545029 prefixEnd_2545029 871215437754418864022087 := by
  unfold tailWord_2545029
  simp only [CollatzResearch.WordTrace]
  refine ⟨92824833496802064193550141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61883222331201376129033427 92824833496802064193550141)
  ·
    refine ⟨34809312561300774072581303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92824833496802064193550141 34809312561300774072581303)
    ·
      refine ⟨52213968841951161108871955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34809312561300774072581303 52213968841951161108871955)
      ·
        refine ⟨78320953262926741663307933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52213968841951161108871955 78320953262926741663307933)
        ·
          refine ⟨29370357473597528123740475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78320953262926741663307933 29370357473597528123740475)
          ·
            refine ⟨44055536210396292185610713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29370357473597528123740475 44055536210396292185610713)
            ·
              refine ⟨33041652157797219139208035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44055536210396292185610713 33041652157797219139208035)
              ·
                refine ⟨49562478236695828708812053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33041652157797219139208035 49562478236695828708812053)
                ·
                  refine ⟨2323241167345116970725565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49562478236695828708812053 2323241167345116970725565)
                  ·
                    refine ⟨871215437754418864022087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2323241167345116970725565 871215437754418864022087)
                    ·
                      rfl

theorem cell22_2545029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_2545029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545029 prefixEnd_2545029 := by exact prefixLift 2545029
  have htrace : WordTrace (prefixWord ++ tailWord_2545029) baseStart_2545029 baseEnd_2545029 := by
    simpa [prefixWord, tailWord_2545029, baseEnd_2545029] using wordTrace_append hprefix tailTrace_2545029
  have hstable : (prefixWord ++ tailWord_2545029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545029).length < 2 ^ (prefixWord ++ tailWord_2545029).sum := by decide
  have hdescent : baseEnd_2545029 < baseStart_2545029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545033 : List Nat := [1, 2, 1, 1, 7, 1, 3, 1, 1, 4]
def baseStart_2545033 : Nat := 118140960795 + 2545033 * 2 ^ 59
def prefixEnd_2545033 : Nat := 4983230072969 + 3 ^ 40 * 2545033 * 2
def baseEnd_2545033 : Nat := 871216807036164186922075

theorem tailTrace_2545033 : CollatzResearch.WordTrace tailWord_2545033 prefixEnd_2545033 871216807036164186922075 := by
  unfold tailWord_2545033
  simp only [CollatzResearch.WordTrace]
  refine ⟨92824979388787572876695753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61883319592525048584463835 92824979388787572876695753)
  ·
    refine ⟨69618734541590679657521815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92824979388787572876695753 69618734541590679657521815)
    ·
      refine ⟨104428101812386019486282723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69618734541590679657521815 104428101812386019486282723)
      ·
        refine ⟨156642152718579029229424085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104428101812386019486282723 156642152718579029229424085)
        ·
          refine ⟨3671300454341695997564627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 156642152718579029229424085 3671300454341695997564627)
          ·
            refine ⟨5506950681512543996346941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3671300454341695997564627 5506950681512543996346941)
            ·
              refine ⟨2065106505567203998630103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5506950681512543996346941 2065106505567203998630103)
              ·
                refine ⟨3097659758350805997945155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065106505567203998630103 3097659758350805997945155)
                ·
                  refine ⟨4646489637526208996917733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3097659758350805997945155 4646489637526208996917733)
                  ·
                    refine ⟨871216807036164186922075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4646489637526208996917733 871216807036164186922075)
                    ·
                      rfl

theorem cell22_2545033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 1, 4].length) (baseStart_2545033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545033 prefixEnd_2545033 := by exact prefixLift 2545033
  have htrace : WordTrace (prefixWord ++ tailWord_2545033) baseStart_2545033 baseEnd_2545033 := by
    simpa [prefixWord, tailWord_2545033, baseEnd_2545033] using wordTrace_append hprefix tailTrace_2545033
  have hstable : (prefixWord ++ tailWord_2545033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545033).length < 2 ^ (prefixWord ++ tailWord_2545033).sum := by decide
  have hdescent : baseEnd_2545033 < baseStart_2545033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545048 : List Nat := [2, 1, 2, 5, 2, 1, 1, 4, 4]
def baseStart_2545048 : Nat := 118140960795 + 2545048 * 2 ^ 59
def prefixEnd_2545048 : Nat := 4983230072969 + 3 ^ 40 * 2545048 * 2
def baseEnd_2545048 : Nat := 290407313947569715932343

theorem tailTrace_2545048 : CollatzResearch.WordTrace tailWord_2545048 prefixEnd_2545048 290407313947569715932343 := by
  unfold tailWord_2545048
  simp only [CollatzResearch.WordTrace]
  refine ⟨46412763241866615219245899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61883684322488820292327865 46412763241866615219245899)
  ·
    refine ⟨69619144862799922828868849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46412763241866615219245899 69619144862799922828868849)
    ·
      refine ⟨52214358647099942121651637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69619144862799922828868849 52214358647099942121651637)
      ·
        refine ⟨4895096123165619573904841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52214358647099942121651637 4895096123165619573904841)
        ·
          refine ⟨3671322092374214680428631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4895096123165619573904841 3671322092374214680428631)
          ·
            refine ⟨5506983138561322020642947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3671322092374214680428631 5506983138561322020642947)
            ·
              refine ⟨8260474707841983030964421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5506983138561322020642947 8260474707841983030964421)
              ·
                refine ⟨1548839007720371818305829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8260474707841983030964421 1548839007720371818305829)
                ·
                  refine ⟨290407313947569715932343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1548839007720371818305829 290407313947569715932343)
                  ·
                    rfl

theorem cell22_2545048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 4].length) (baseStart_2545048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545048 prefixEnd_2545048 := by exact prefixLift 2545048
  have htrace : WordTrace (prefixWord ++ tailWord_2545048) baseStart_2545048 baseEnd_2545048 := by
    simpa [prefixWord, tailWord_2545048, baseEnd_2545048] using wordTrace_append hprefix tailTrace_2545048
  have hstable : (prefixWord ++ tailWord_2545048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545048).length < 2 ^ (prefixWord ++ tailWord_2545048).sum := by decide
  have hdescent : baseEnd_2545048 < baseStart_2545048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545119 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 2, 5]
def baseStart_2545119 : Nat := 118140960795 + 2545119 * 2 ^ 59
def prefixEnd_2545119 : Nat := 4983230072969 + 3 ^ 40 * 2545119 * 2
def baseEnd_2545119 : Nat := 871246246593688629271811

theorem tailTrace_2545119 : CollatzResearch.WordTrace tailWord_2545119 prefixEnd_2545119 871246246593688629271811 := by
  unfold tailWord_2545119
  simp only [CollatzResearch.WordTrace]
  refine ⟨92828116066476009564326411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61885410710984006376217607 92828116066476009564326411)
  ·
    refine ⟨139242174099714014346489617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92828116066476009564326411 139242174099714014346489617)
    ·
      refine ⟨104431630574785510759867213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139242174099714014346489617 104431630574785510759867213)
      ·
        refine ⟨39161861465544566534950205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104431630574785510759867213 39161861465544566534950205)
        ·
          refine ⟨14685698049579212450606327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39161861465544566534950205 14685698049579212450606327)
          ·
            refine ⟨22028547074368818675909491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14685698049579212450606327 22028547074368818675909491)
            ·
              refine ⟨33042820611553228013864237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22028547074368818675909491 33042820611553228013864237)
              ·
                refine ⟨12391057729332460505199089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33042820611553228013864237 12391057729332460505199089)
                ·
                  refine ⟨9293293296999345378899317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12391057729332460505199089 9293293296999345378899317)
                  ·
                    refine ⟨871246246593688629271811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9293293296999345378899317 871246246593688629271811)
                    ·
                      rfl

theorem cell22_2545119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_2545119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545119 prefixEnd_2545119 := by exact prefixLift 2545119
  have htrace : WordTrace (prefixWord ++ tailWord_2545119) baseStart_2545119 baseEnd_2545119 := by
    simpa [prefixWord, tailWord_2545119, baseEnd_2545119] using wordTrace_append hprefix tailTrace_2545119
  have hstable : (prefixWord ++ tailWord_2545119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545119).length < 2 ^ (prefixWord ++ tailWord_2545119).sum := by decide
  have hdescent : baseEnd_2545119 < baseStart_2545119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545142 : List Nat := [5, 1, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_2545142 : Nat := 118140960795 + 2545142 * 2 ^ 59
def prefixEnd_2545142 : Nat := 4983230072969 + 3 ^ 40 * 2545142 * 2
def baseEnd_2545142 : Nat := 871254119963724235946741

theorem tailTrace_2545142 : CollatzResearch.WordTrace tailWord_2545142 prefixEnd_2545142 871254119963724235946741 := by
  unfold tailWord_2545142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5801809684087042780775855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61885969963595122994942453 5801809684087042780775855)
  ·
    refine ⟨8702714526130564171163783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5801809684087042780775855 8702714526130564171163783)
    ·
      refine ⟨13054071789195846256745675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8702714526130564171163783 13054071789195846256745675)
      ·
        refine ⟨19581107683793769385118513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13054071789195846256745675 19581107683793769385118513)
        ·
          refine ⟨14685830762845327038838885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19581107683793769385118513 14685830762845327038838885)
          ·
            refine ⟨2753593268033498819782291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14685830762845327038838885 2753593268033498819782291)
            ·
              refine ⟨4130389902050248229673437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753593268033498819782291 4130389902050248229673437)
              ·
                refine ⟨1548896213268843086127539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4130389902050248229673437 1548896213268843086127539)
                ·
                  refine ⟨2323344319903264629191309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548896213268843086127539 2323344319903264629191309)
                  ·
                    refine ⟨871254119963724235946741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2323344319903264629191309 871254119963724235946741)
                    ·
                      rfl

theorem cell22_2545142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_2545142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545142 prefixEnd_2545142 := by exact prefixLift 2545142
  have htrace : WordTrace (prefixWord ++ tailWord_2545142) baseStart_2545142 baseEnd_2545142 := by
    simpa [prefixWord, tailWord_2545142, baseEnd_2545142] using wordTrace_append hprefix tailTrace_2545142
  have hstable : (prefixWord ++ tailWord_2545142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545142).length < 2 ^ (prefixWord ++ tailWord_2545142).sum := by decide
  have hdescent : baseEnd_2545142 < baseStart_2545142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545172 : List Nat := [2, 4, 3, 1, 2, 2, 2, 1, 5]
def baseStart_2545172 : Nat := 118140960795 + 2545172 * 2 ^ 59
def prefixEnd_2545172 : Nat := 4983230072969 + 3 ^ 40 * 2545172 * 2
def baseEnd_2545172 : Nat := 290421463192271385898883

theorem tailTrace_2545172 : CollatzResearch.WordTrace tailWord_2545172 prefixEnd_2545172 290421463192271385898883 := by
  unfold tailWord_2545172
  simp only [CollatzResearch.WordTrace]
  refine ⟨46415024567641999808002885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61886699423522666410670513 46415024567641999808002885)
  ·
    refine ⟨8702817106432874964000541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46415024567641999808002885 8702817106432874964000541)
    ·
      refine ⟨3263556414912328111500203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8702817106432874964000541 3263556414912328111500203)
      ·
        refine ⟨4895334622368492167250305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3263556414912328111500203 4895334622368492167250305)
        ·
          refine ⟨3671500966776369125437729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4895334622368492167250305 3671500966776369125437729)
          ·
            refine ⟨2753625725082276844078297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3671500966776369125437729 2753625725082276844078297)
            ·
              refine ⟨2065219293811707633058723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2753625725082276844078297 2065219293811707633058723)
              ·
                refine ⟨3097828940717561449588085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065219293811707633058723 3097828940717561449588085)
                ·
                  refine ⟨290421463192271385898883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3097828940717561449588085 290421463192271385898883)
                  ·
                    rfl

theorem cell22_2545172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_2545172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545172 prefixEnd_2545172 := by exact prefixLift 2545172
  have htrace : WordTrace (prefixWord ++ tailWord_2545172) baseStart_2545172 baseEnd_2545172 := by
    simpa [prefixWord, tailWord_2545172, baseEnd_2545172] using wordTrace_append hprefix tailTrace_2545172
  have hstable : (prefixWord ++ tailWord_2545172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545172).length < 2 ^ (prefixWord ++ tailWord_2545172).sum := by decide
  have hdescent : baseEnd_2545172 < baseStart_2545172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545181 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_2545181 : Nat := 118140960795 + 2545181 * 2 ^ 59
def prefixEnd_2545181 : Nat := 4983230072969 + 3 ^ 40 * 2545181 * 2
def baseEnd_2545181 : Nat := 871267470460741134221621

theorem tailTrace_2545181 : CollatzResearch.WordTrace tailWord_2545181 prefixEnd_2545181 871267470460741134221621 := by
  unfold tailWord_2545181
  simp only [CollatzResearch.WordTrace]
  refine ⟨92830377392251394153083397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61886918261500929435388931 92830377392251394153083397)
  ·
    refine ⟨17405695761047136403703137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92830377392251394153083397 17405695761047136403703137)
    ·
      refine ⟨13054271820785352302777353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17405695761047136403703137 13054271820785352302777353)
      ·
        refine ⟨9790703865589014227083015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13054271820785352302777353 9790703865589014227083015)
        ·
          refine ⟨14686055798383521340624523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9790703865589014227083015 14686055798383521340624523)
          ·
            refine ⟨22029083697575282010936785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14686055798383521340624523 22029083697575282010936785)
            ·
              refine ⟨16521812773181461508202589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22029083697575282010936785 16521812773181461508202589)
              ·
                refine ⟨6195679789943048065575971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16521812773181461508202589 6195679789943048065575971)
                ·
                  refine ⟨9293519684914572098363957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6195679789943048065575971 9293519684914572098363957)
                  ·
                    refine ⟨871267470460741134221621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9293519684914572098363957 871267470460741134221621)
                    ·
                      rfl

theorem cell22_2545181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_2545181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545181 prefixEnd_2545181 := by exact prefixLift 2545181
  have htrace : WordTrace (prefixWord ++ tailWord_2545181) baseStart_2545181 baseEnd_2545181 := by
    simpa [prefixWord, tailWord_2545181, baseEnd_2545181] using wordTrace_append hprefix tailTrace_2545181
  have hstable : (prefixWord ++ tailWord_2545181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545181).length < 2 ^ (prefixWord ++ tailWord_2545181).sum := by decide
  have hdescent : baseEnd_2545181 < baseStart_2545181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545198 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2545198 : Nat := 118140960795 + 2545198 * 2 ^ 59
def prefixEnd_2545198 : Nat := 4983230072969 + 3 ^ 40 * 2545198 * 2
def baseEnd_2545198 : Nat := 871273289908158756546569

theorem tailTrace_2545198 : CollatzResearch.WordTrace tailWord_2545198 prefixEnd_2545198 871273289908158756546569 := by
  unfold tailWord_2545198
  simp only [CollatzResearch.WordTrace]
  refine ⟨11603874679148725757056531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61887331622126537370968165 11603874679148725757056531)
  ·
    refine ⟨17405812018723088635584797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11603874679148725757056531 17405812018723088635584797)
    ·
      refine ⟨6527179507021158238344299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17405812018723088635584797 6527179507021158238344299)
      ·
        refine ⟨9790769260531737357516449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6527179507021158238344299 9790769260531737357516449)
        ·
          refine ⟨7343076945398803018137337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9790769260531737357516449 7343076945398803018137337)
          ·
            refine ⟨5507307709049102263603003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7343076945398803018137337 5507307709049102263603003)
            ·
              refine ⟨8260961563573653395404505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5507307709049102263603003 8260961563573653395404505)
              ·
                refine ⟨6195721172680240046553379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8260961563573653395404505 6195721172680240046553379)
                ·
                  refine ⟨9293581759020360069830069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6195721172680240046553379 9293581759020360069830069)
                  ·
                    refine ⟨871273289908158756546569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9293581759020360069830069 871273289908158756546569)
                    ·
                      rfl

theorem cell22_2545198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2545198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545198 prefixEnd_2545198 := by exact prefixLift 2545198
  have htrace : WordTrace (prefixWord ++ tailWord_2545198) baseStart_2545198 baseEnd_2545198 := by
    simpa [prefixWord, tailWord_2545198, baseEnd_2545198] using wordTrace_append hprefix tailTrace_2545198
  have hstable : (prefixWord ++ tailWord_2545198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545198).length < 2 ^ (prefixWord ++ tailWord_2545198).sum := by decide
  have hdescent : baseEnd_2545198 < baseStart_2545198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545290 : List Nat := [3, 1, 2, 3, 2, 2, 3, 1, 5]
def baseStart_2545290 : Nat := 118140960795 + 2545290 * 2 ^ 59
def prefixEnd_2545290 : Nat := 4983230072969 + 3 ^ 40 * 2545290 * 2
def baseEnd_2545290 : Nat := 290434927796100394415429

theorem tailTrace_2545290 : CollatzResearch.WordTrace tailWord_2545290 prefixEnd_2545290 290434927796100394415429 := by
  unfold tailWord_2545290
  simp only [CollatzResearch.WordTrace]
  refine ⟨23208588237214126442200331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61889568632571003845867549 23208588237214126442200331)
  ·
    refine ⟨34812882355821189663300497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23208588237214126442200331 34812882355821189663300497)
    ·
      refine ⟨26109661766865892247475373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34812882355821189663300497 26109661766865892247475373)
      ·
        refine ⟨9791123162574709592803265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26109661766865892247475373 9791123162574709592803265)
        ·
          refine ⟨7343342371931032194602449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9791123162574709592803265 7343342371931032194602449)
          ·
            refine ⟨5507506778948274145951837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7343342371931032194602449 5507506778948274145951837)
            ·
              refine ⟨2065315042105602804731939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5507506778948274145951837 2065315042105602804731939)
              ·
                refine ⟨3097972563158404207097909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065315042105602804731939 3097972563158404207097909)
                ·
                  refine ⟨290434927796100394415429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3097972563158404207097909 290434927796100394415429)
                  ·
                    rfl

theorem cell22_2545290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_2545290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545290 prefixEnd_2545290 := by exact prefixLift 2545290
  have htrace : WordTrace (prefixWord ++ tailWord_2545290) baseStart_2545290 baseEnd_2545290 := by
    simpa [prefixWord, tailWord_2545290, baseEnd_2545290] using wordTrace_append hprefix tailTrace_2545290
  have hstable : (prefixWord ++ tailWord_2545290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545290).length < 2 ^ (prefixWord ++ tailWord_2545290).sum := by decide
  have hdescent : baseEnd_2545290 < baseStart_2545290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545303 : List Nat := [1, 1, 3, 3, 2, 2, 1, 4, 1, 4]
def baseStart_2545303 : Nat := 118140960795 + 2545303 * 2 ^ 59
def prefixEnd_2545303 : Nat := 4983230072969 + 3 ^ 40 * 2545303 * 2
def baseEnd_2545303 : Nat := 871309233553973482671247

theorem tailTrace_2545303 : CollatzResearch.WordTrace tailWord_2545303 prefixEnd_2545303 871309233553973482671247 := by
  unfold tailWord_2545303
  simp only [CollatzResearch.WordTrace]
  refine ⟨92834827097809408989024563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61889884731872939326016375 92834827097809408989024563)
  ·
    refine ⟨139252240646714113483536845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92834827097809408989024563 139252240646714113483536845)
    ·
      refine ⟨52219590242517792556326317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139252240646714113483536845 52219590242517792556326317)
      ·
        refine ⟨19582346340944172208622369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52219590242517792556326317 19582346340944172208622369)
        ·
          refine ⟨14686759755708129156466777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19582346340944172208622369 14686759755708129156466777)
          ·
            refine ⟨11015069816781096867350083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14686759755708129156466777 11015069816781096867350083)
            ·
              refine ⟨16522604725171645301025125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11015069816781096867350083 16522604725171645301025125)
              ·
                refine ⟨3097988385969683493942211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16522604725171645301025125 3097988385969683493942211)
                ·
                  refine ⟨4646982578954525240913317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3097988385969683493942211 4646982578954525240913317)
                  ·
                    refine ⟨871309233553973482671247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4646982578954525240913317 871309233553973482671247)
                    ·
                      rfl

theorem cell22_2545303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_2545303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545303 prefixEnd_2545303 := by exact prefixLift 2545303
  have htrace : WordTrace (prefixWord ++ tailWord_2545303) baseStart_2545303 baseEnd_2545303 := by
    simpa [prefixWord, tailWord_2545303, baseEnd_2545303] using wordTrace_append hprefix tailTrace_2545303
  have hstable : (prefixWord ++ tailWord_2545303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545303).length < 2 ^ (prefixWord ++ tailWord_2545303).sum := by decide
  have hdescent : baseEnd_2545303 < baseStart_2545303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545311 : List Nat := [1, 1, 2, 7, 2, 1, 1, 3, 1, 3]
def baseStart_2545311 : Nat := 118140960795 + 2545311 * 2 ^ 59
def prefixEnd_2545311 : Nat := 4983230072969 + 3 ^ 40 * 2545311 * 2
def baseEnd_2545311 : Nat := 871311972117464128471223

theorem tailTrace_2545311 : CollatzResearch.WordTrace tailWord_2545311 prefixEnd_2545311 871311972117464128471223 := by
  unfold tailWord_2545311
  simp only [CollatzResearch.WordTrace]
  refine ⟨92835118881780426355315787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61890079254520284236877191 92835118881780426355315787)
  ·
    refine ⟨139252678322670639532973681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92835118881780426355315787 139252678322670639532973681)
    ·
      refine ⟨104439508742002979649730261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139252678322670639532973681 104439508742002979649730261)
      ·
        refine ⟨2447800986140694835540553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 104439508742002979649730261 2447800986140694835540553)
        ·
          refine ⟨1835850739605521126655415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2447800986140694835540553 1835850739605521126655415)
          ·
            refine ⟨2753776109408281689983123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835850739605521126655415 2753776109408281689983123)
            ·
              refine ⟨4130664164112422534974685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753776109408281689983123 4130664164112422534974685)
              ·
                refine ⟨1548999061542158450615507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4130664164112422534974685 1548999061542158450615507)
                ·
                  refine ⟨2323498592313237675923261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548999061542158450615507 2323498592313237675923261)
                  ·
                    refine ⟨871311972117464128471223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2323498592313237675923261 871311972117464128471223)
                    ·
                      rfl

theorem cell22_2545311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 1, 3].length) (baseStart_2545311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545311 prefixEnd_2545311 := by exact prefixLift 2545311
  have htrace : WordTrace (prefixWord ++ tailWord_2545311) baseStart_2545311 baseEnd_2545311 := by
    simpa [prefixWord, tailWord_2545311, baseEnd_2545311] using wordTrace_append hprefix tailTrace_2545311
  have hstable : (prefixWord ++ tailWord_2545311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545311).length < 2 ^ (prefixWord ++ tailWord_2545311).sum := by decide
  have hdescent : baseEnd_2545311 < baseStart_2545311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545348 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_2545348 : Nat := 118140960795 + 2545348 * 2 ^ 59
def prefixEnd_2545348 : Nat := 4983230072969 + 3 ^ 40 * 2545348 * 2
def baseEnd_2545348 : Nat := 871324637973608365296109

theorem tailTrace_2545348 : CollatzResearch.WordTrace tailWord_2545348 prefixEnd_2545348 871324637973608365296109 := by
  unfold tailWord_2545348
  simp only [CollatzResearch.WordTrace]
  refine ⟨46418234191323190837206349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61890978921764254449608465 46418234191323190837206349)
  ·
    refine ⟨17406837821746196563952381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46418234191323190837206349 17406837821746196563952381)
    ·
      refine ⟨6527564183154823711482143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17406837821746196563952381 6527564183154823711482143)
      ·
        refine ⟨9791346274732235567223215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6527564183154823711482143 9791346274732235567223215)
        ·
          refine ⟨14687019412098353350834823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9791346274732235567223215 14687019412098353350834823)
          ·
            refine ⟨22030529118147530026252235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14687019412098353350834823 22030529118147530026252235)
            ·
              refine ⟨33045793677221295039378353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22030529118147530026252235 33045793677221295039378353)
              ·
                refine ⟨24784345257915971279533765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33045793677221295039378353 24784345257915971279533765)
                ·
                  refine ⟨4647064735859244614912581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24784345257915971279533765 4647064735859244614912581)
                  ·
                    refine ⟨871324637973608365296109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4647064735859244614912581 871324637973608365296109)
                    ·
                      rfl

theorem cell22_2545348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_2545348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545348 prefixEnd_2545348 := by exact prefixLift 2545348
  have htrace : WordTrace (prefixWord ++ tailWord_2545348) baseStart_2545348 baseEnd_2545348 := by
    simpa [prefixWord, tailWord_2545348, baseEnd_2545348] using wordTrace_append hprefix tailTrace_2545348
  have hstable : (prefixWord ++ tailWord_2545348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545348).length < 2 ^ (prefixWord ++ tailWord_2545348).sum := by decide
  have hdescent : baseEnd_2545348 < baseStart_2545348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545470 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 6]
def baseStart_2545470 : Nat := 118140960795 + 2545470 * 2 ^ 59
def prefixEnd_2545470 : Nat := 4983230072969 + 3 ^ 40 * 2545470 * 2
def baseEnd_2545470 : Nat := 290455467022280237915245

theorem tailTrace_2545470 : CollatzResearch.WordTrace tailWord_2545470 prefixEnd_2545470 290455467022280237915245 := by
  unfold tailWord_2545470
  simp only [CollatzResearch.WordTrace]
  refine ⟨11605114761025549563794233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61893945392136264340235909 11605114761025549563794233)
  ·
    refine ⟨8703836070769162172845675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11605114761025549563794233 8703836070769162172845675)
    ·
      refine ⟨13055754106153743259268513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8703836070769162172845675 13055754106153743259268513)
      ·
        refine ⟨9791815579615307444451385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13055754106153743259268513 9791815579615307444451385)
        ·
          refine ⟨7343861684711480583338539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9791815579615307444451385 7343861684711480583338539)
          ·
            refine ⟨11015792527067220875007809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7343861684711480583338539 11015792527067220875007809)
            ·
              refine ⟨8261844395300415656255857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11015792527067220875007809 8261844395300415656255857)
              ·
                refine ⟨6196383296475311742191893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8261844395300415656255857 6196383296475311742191893)
                ·
                  refine ⟨290455467022280237915245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6196383296475311742191893 290455467022280237915245)
                  ·
                    rfl

theorem cell22_2545470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_2545470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545470 prefixEnd_2545470 := by exact prefixLift 2545470
  have htrace : WordTrace (prefixWord ++ tailWord_2545470) baseStart_2545470 baseEnd_2545470 := by
    simpa [prefixWord, tailWord_2545470, baseEnd_2545470] using wordTrace_append hprefix tailTrace_2545470
  have hstable : (prefixWord ++ tailWord_2545470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545470).length < 2 ^ (prefixWord ++ tailWord_2545470).sum := by decide
  have hdescent : baseEnd_2545470 < baseStart_2545470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545530 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 3, 3]
def baseStart_2545530 : Nat := 118140960795 + 2545530 * 2 ^ 59
def prefixEnd_2545530 : Nat := 4983230072969 + 3 ^ 40 * 2545530 * 2
def baseEnd_2545530 : Nat := 871386940293020557245551

theorem tailTrace_2545530 : CollatzResearch.WordTrace tailWord_2545530 prefixEnd_2545530 871386940293020557245551 := by
  unfold tailWord_2545530
  simp only [CollatzResearch.WordTrace]
  refine ⟨23210776616996756689384511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61895404311991351171692029 23210776616996756689384511)
  ·
    refine ⟨34816164925495135034076767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23210776616996756689384511 34816164925495135034076767)
    ·
      refine ⟨52224247388242702551115151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34816164925495135034076767 52224247388242702551115151)
      ·
        refine ⟨78336371082364053826672727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52224247388242702551115151 78336371082364053826672727)
        ·
          refine ⟨117504556623546080740009091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78336371082364053826672727 117504556623546080740009091)
          ·
            refine ⟨176256834935319121110013637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117504556623546080740009091 176256834935319121110013637)
            ·
              refine ⟨33048156550372335208127557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176256834935319121110013637 33048156550372335208127557)
              ·
                refine ⟨6196529353194812851523917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33048156550372335208127557 6196529353194812851523917)
                ·
                  refine ⟨2323698507448054819321469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6196529353194812851523917 2323698507448054819321469)
                  ·
                    refine ⟨871386940293020557245551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2323698507448054819321469 871386940293020557245551)
                    ·
                      rfl

theorem cell22_2545530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_2545530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545530 prefixEnd_2545530 := by exact prefixLift 2545530
  have htrace : WordTrace (prefixWord ++ tailWord_2545530) baseStart_2545530 baseEnd_2545530 := by
    simpa [prefixWord, tailWord_2545530, baseEnd_2545530] using wordTrace_append hprefix tailTrace_2545530
  have hstable : (prefixWord ++ tailWord_2545530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545530).length < 2 ^ (prefixWord ++ tailWord_2545530).sum := by decide
  have hdescent : baseEnd_2545530 < baseStart_2545530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545534 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2545534 : Nat := 118140960795 + 2545534 * 2 ^ 59
def prefixEnd_2545534 : Nat := 4983230072969 + 3 ^ 40 * 2545534 * 2
def baseEnd_2545534 : Nat := 871388309574765880145539

theorem tailTrace_2545534 : CollatzResearch.WordTrace tailWord_2545534 prefixEnd_2545534 871388309574765880145539 := by
  unfold tailWord_2545534
  simp only [CollatzResearch.WordTrace]
  refine ⟨11605406544996566930085457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61895501573315023627122437 11605406544996566930085457)
  ·
    refine ⟨8704054908747425197564093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11605406544996566930085457 8704054908747425197564093)
    ·
      refine ⟨3264020590780284449086535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8704054908747425197564093 3264020590780284449086535)
      ·
        refine ⟨4896030886170426673629803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3264020590780284449086535 4896030886170426673629803)
        ·
          refine ⟨7344046329255640010444705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4896030886170426673629803 7344046329255640010444705)
          ·
            refine ⟨5508034746941730007833529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7344046329255640010444705 5508034746941730007833529)
            ·
              refine ⟨4131026060206297505875147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5508034746941730007833529 4131026060206297505875147)
              ·
                refine ⟨6196539090309446258812721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4131026060206297505875147 6196539090309446258812721)
                ·
                  refine ⟨4647404317732084694109541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6196539090309446258812721 4647404317732084694109541)
                  ·
                    refine ⟨871388309574765880145539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4647404317732084694109541 871388309574765880145539)
                    ·
                      rfl

theorem cell22_2545534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2545534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545534 prefixEnd_2545534 := by exact prefixLift 2545534
  have htrace : WordTrace (prefixWord ++ tailWord_2545534) baseStart_2545534 baseEnd_2545534 := by
    simpa [prefixWord, tailWord_2545534, baseEnd_2545534] using wordTrace_append hprefix tailTrace_2545534
  have hstable : (prefixWord ++ tailWord_2545534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545534).length < 2 ^ (prefixWord ++ tailWord_2545534).sum := by decide
  have hdescent : baseEnd_2545534 < baseStart_2545534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545547 : List Nat := [1, 1, 1, 1, 4, 2, 1, 7, 1, 3]
def baseStart_2545547 : Nat := 118140960795 + 2545547 * 2 ^ 59
def prefixEnd_2545547 : Nat := 4983230072969 + 3 ^ 40 * 2545547 * 2
def baseEnd_2545547 : Nat := 871392759740438179570499

theorem tailTrace_2545547 : CollatzResearch.WordTrace tailWord_2545547 prefixEnd_2545547 871392759740438179570499 := by
  unfold tailWord_2545547
  simp only [CollatzResearch.WordTrace]
  refine ⟨92843726508925438660906895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61895817672616959107271263 92843726508925438660906895)
  ·
    refine ⟨139265589763388157991360343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92843726508925438660906895 139265589763388157991360343)
    ·
      refine ⟨208898384645082236987040515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139265589763388157991360343 208898384645082236987040515)
      ·
        refine ⟨313347576967623355480560773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208898384645082236987040515 313347576967623355480560773)
        ·
          refine ⟨58752670681429379152605145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313347576967623355480560773 58752670681429379152605145)
          ·
            refine ⟨44064503011072034364453859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58752670681429379152605145 44064503011072034364453859)
            ·
              refine ⟨66096754516608051546680789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44064503011072034364453859 66096754516608051546680789)
              ·
                refine ⟨1549142683983001208125331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 66096754516608051546680789 1549142683983001208125331)
                ·
                  refine ⟨2323714025974501812187997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1549142683983001208125331 2323714025974501812187997)
                  ·
                    refine ⟨871392759740438179570499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2323714025974501812187997 871392759740438179570499)
                    ·
                      rfl

theorem cell22_2545547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 1, 3].length) (baseStart_2545547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545547 prefixEnd_2545547 := by exact prefixLift 2545547
  have htrace : WordTrace (prefixWord ++ tailWord_2545547) baseStart_2545547 baseEnd_2545547 := by
    simpa [prefixWord, tailWord_2545547, baseEnd_2545547] using wordTrace_append hprefix tailTrace_2545547
  have hstable : (prefixWord ++ tailWord_2545547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545547).length < 2 ^ (prefixWord ++ tailWord_2545547).sum := by decide
  have hdescent : baseEnd_2545547 < baseStart_2545547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545566 : List Nat := [4, 3, 1, 3, 2, 1, 1, 7]
def baseStart_2545566 : Nat := 118140960795 + 2545566 * 2 ^ 59
def prefixEnd_2545566 : Nat := 4983230072969 + 3 ^ 40 * 2545566 * 2
def baseEnd_2545566 : Nat := 96822140425414273705049

theorem tailTrace_2545566 : CollatzResearch.WordTrace tailWord_2545566 prefixEnd_2545566 96822140425414273705049 := by
  unfold tailWord_2545566
  simp only [CollatzResearch.WordTrace]
  refine ⟨11605552436982075613231069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61896279663904403270565701 11605552436982075613231069)
  ·
    refine ⟨4352082163868278354961651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11605552436982075613231069 4352082163868278354961651)
    ·
      refine ⟨6528123245802417532442477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4352082163868278354961651 6528123245802417532442477)
      ·
        refine ⟨2448046217175906574665929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6528123245802417532442477 2448046217175906574665929)
        ·
          refine ⟨1836034662881929930999447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2448046217175906574665929 1836034662881929930999447)
          ·
            refine ⟨2754051994322894896499171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1836034662881929930999447 2754051994322894896499171)
            ·
              refine ⟨4131077991484342344748757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2754051994322894896499171 4131077991484342344748757)
              ·
                refine ⟨96822140425414273705049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4131077991484342344748757 96822140425414273705049)
                ·
                  rfl

theorem cell22_2545566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_2545566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545566 prefixEnd_2545566 := by exact prefixLift 2545566
  have htrace : WordTrace (prefixWord ++ tailWord_2545566) baseStart_2545566 baseEnd_2545566 := by
    simpa [prefixWord, tailWord_2545566, baseEnd_2545566] using wordTrace_append hprefix tailTrace_2545566
  have hstable : (prefixWord ++ tailWord_2545566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545566).length < 2 ^ (prefixWord ++ tailWord_2545566).sum := by decide
  have hdescent : baseEnd_2545566 < baseStart_2545566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545575 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 1, 7]
def baseStart_2545575 : Nat := 118140960795 + 2545575 * 2 ^ 59
def prefixEnd_2545575 : Nat := 4983230072969 + 3 ^ 40 * 2545575 * 2
def baseEnd_2545575 : Nat := 871402344712655439870413

theorem tailTrace_2545575 : CollatzResearch.WordTrace tailWord_2545575 prefixEnd_2545575 871402344712655439870413 := by
  unfold tailWord_2545575
  simp only [CollatzResearch.WordTrace]
  refine ⟨92844747752823999442926179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61896498501882666295284119 92844747752823999442926179)
  ·
    refine ⟨139267121629235999164389269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92844747752823999442926179 139267121629235999164389269)
    ·
      refine ⟨6528146326370437460830747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139267121629235999164389269 6528146326370437460830747)
      ·
        refine ⟨9792219489555656191246121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6528146326370437460830747 9792219489555656191246121)
        ·
          refine ⟨7344164617166742143434591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9792219489555656191246121 7344164617166742143434591)
          ·
            refine ⟨11016246925750113215151887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7344164617166742143434591 11016246925750113215151887)
            ·
              refine ⟨16524370388625169822727831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11016246925750113215151887 16524370388625169822727831)
              ·
                refine ⟨24786555582937754734091747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16524370388625169822727831 24786555582937754734091747)
                ·
                  refine ⟨37179833374406632101137621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24786555582937754734091747 37179833374406632101137621)
                  ·
                    refine ⟨871402344712655439870413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37179833374406632101137621 871402344712655439870413)
                    ·
                      rfl

theorem cell22_2545575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_2545575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545575 prefixEnd_2545575 := by exact prefixLift 2545575
  have htrace : WordTrace (prefixWord ++ tailWord_2545575) baseStart_2545575 baseEnd_2545575 := by
    simpa [prefixWord, tailWord_2545575, baseEnd_2545575] using wordTrace_append hprefix tailTrace_2545575
  have hstable : (prefixWord ++ tailWord_2545575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545575).length < 2 ^ (prefixWord ++ tailWord_2545575).sum := by decide
  have hdescent : baseEnd_2545575 < baseStart_2545575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545628 : List Nat := [2, 2, 6, 1, 1, 1, 3, 1, 5]
def baseStart_2545628 : Nat := 118140960795 + 2545628 * 2 ^ 59
def prefixEnd_2545628 : Nat := 4983230072969 + 3 ^ 40 * 2545628 * 2
def baseEnd_2545628 : Nat := 290473495898593656098417

theorem tailTrace_2545628 : CollatzResearch.WordTrace tailWord_2545628 prefixEnd_2545628 290473495898593656098417 := by
  unfold tailWord_2545628
  simp only [CollatzResearch.WordTrace]
  refine ⟨46423340410815994747302769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61897787214421326329737025 46423340410815994747302769)
  ·
    refine ⟨34817505308111996060477077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46423340410815994747302769 34817505308111996060477077)
    ·
      refine ⟨1632070561317749815334863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34817505308111996060477077 1632070561317749815334863)
      ·
        refine ⟨2448105841976624723002295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1632070561317749815334863 2448105841976624723002295)
        ·
          refine ⟨3672158762964937084503443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2448105841976624723002295 3672158762964937084503443)
          ·
            refine ⟨5508238144447405626755165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3672158762964937084503443 5508238144447405626755165)
            ·
              refine ⟨2065589304167777110033187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5508238144447405626755165 2065589304167777110033187)
              ·
                refine ⟨3098383956251665665049781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065589304167777110033187 3098383956251665665049781)
                ·
                  refine ⟨290473495898593656098417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3098383956251665665049781 290473495898593656098417)
                  ·
                    rfl

theorem cell22_2545628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_2545628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545628 prefixEnd_2545628 := by exact prefixLift 2545628
  have htrace : WordTrace (prefixWord ++ tailWord_2545628) baseStart_2545628 baseEnd_2545628 := by
    simpa [prefixWord, tailWord_2545628, baseEnd_2545628] using wordTrace_append hprefix tailTrace_2545628
  have hstable : (prefixWord ++ tailWord_2545628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545628).length < 2 ^ (prefixWord ++ tailWord_2545628).sum := by decide
  have hdescent : baseEnd_2545628 < baseStart_2545628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545635 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 1, 6]
def baseStart_2545635 : Nat := 118140960795 + 2545635 * 2 ^ 59
def prefixEnd_2545635 : Nat := 4983230072969 + 3 ^ 40 * 2545635 * 2
def baseEnd_2545635 : Nat := 871422883938835283370229

theorem tailTrace_2545635 : CollatzResearch.WordTrace tailWord_2545635 prefixEnd_2545635 871422883938835283370229 := by
  unfold tailWord_2545635
  simp only [CollatzResearch.WordTrace]
  refine ⟨92846936132606629690110359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61897957421737753126740239 92846936132606629690110359)
  ·
    refine ⟨139270404198909944535165539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92846936132606629690110359 139270404198909944535165539)
    ·
      refine ⟨208905606298364916802748309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139270404198909944535165539 208905606298364916802748309)
      ·
        refine ⟨9792450295235855475128827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 208905606298364916802748309 9792450295235855475128827)
        ·
          refine ⟨14688675442853783212693241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9792450295235855475128827 14688675442853783212693241)
          ·
            refine ⟨11016506582140337409519931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14688675442853783212693241 11016506582140337409519931)
            ·
              refine ⟨16524759873210506114279897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11016506582140337409519931 16524759873210506114279897)
              ·
                refine ⟨12393569904907879585709923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16524759873210506114279897 12393569904907879585709923)
                ·
                  refine ⟨18590354857361819378564885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12393569904907879585709923 18590354857361819378564885)
                  ·
                    refine ⟨871422883938835283370229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18590354857361819378564885 871422883938835283370229)
                    ·
                      rfl

theorem cell22_2545635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 6].length) (baseStart_2545635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545635 prefixEnd_2545635 := by exact prefixLift 2545635
  have htrace : WordTrace (prefixWord ++ tailWord_2545635) baseStart_2545635 baseEnd_2545635 := by
    simpa [prefixWord, tailWord_2545635, baseEnd_2545635] using wordTrace_append hprefix tailTrace_2545635
  have hstable : (prefixWord ++ tailWord_2545635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545635).length < 2 ^ (prefixWord ++ tailWord_2545635).sum := by decide
  have hdescent : baseEnd_2545635 < baseStart_2545635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545729 : List Nat := [1, 2, 5, 1, 2, 2, 2, 2, 5]
def baseStart_2545729 : Nat := 118140960795 + 2545729 * 2 ^ 59
def prefixEnd_2545729 : Nat := 4983230072969 + 3 ^ 40 * 2545729 * 2
def baseEnd_2545729 : Nat := 290485020686616790506647

theorem tailTrace_2545729 : CollatzResearch.WordTrace tailWord_2545729 prefixEnd_2545729 290485020686616790506647 := by
  unfold tailWord_2545729
  simp only [CollatzResearch.WordTrace]
  refine ⟨92850364594266083744032241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61900243062844055829354827 92850364594266083744032241)
  ·
    refine ⟨69637773445699562808024181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92850364594266083744032241 69637773445699562808024181)
    ·
      refine ⟨6528541260534334013252267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69637773445699562808024181 6528541260534334013252267)
      ·
        refine ⟨9792811890801501019878401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6528541260534334013252267 9792811890801501019878401)
        ·
          refine ⟨7344608918101125764908801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9792811890801501019878401 7344608918101125764908801)
          ·
            refine ⟨5508456688575844323681601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7344608918101125764908801 5508456688575844323681601)
            ·
              refine ⟨4131342516431883242761201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5508456688575844323681601 4131342516431883242761201)
              ·
                refine ⟨3098506887323912432070901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4131342516431883242761201 3098506887323912432070901)
                ·
                  refine ⟨290485020686616790506647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3098506887323912432070901 290485020686616790506647)
                  ·
                    rfl

theorem cell22_2545729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 5].length) (baseStart_2545729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545729 prefixEnd_2545729 := by exact prefixLift 2545729
  have htrace : WordTrace (prefixWord ++ tailWord_2545729) baseStart_2545729 baseEnd_2545729 := by
    simpa [prefixWord, tailWord_2545729, baseEnd_2545729] using wordTrace_append hprefix tailTrace_2545729
  have hstable : (prefixWord ++ tailWord_2545729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545729).length < 2 ^ (prefixWord ++ tailWord_2545729).sum := by decide
  have hdescent : baseEnd_2545729 < baseStart_2545729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545742 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_2545742 : Nat := 118140960795 + 2545742 * 2 ^ 59
def prefixEnd_2545742 : Nat := 4983230072969 + 3 ^ 40 * 2545742 * 2
def baseEnd_2545742 : Nat := 871459512225522670944901

theorem tailTrace_2545742 : CollatzResearch.WordTrace tailWord_2545742 prefixEnd_2545742 871459512225522670944901 := by
  unfold tailWord_2545742
  simp only [CollatzResearch.WordTrace]
  refine ⟨11606354842902373370531935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61900559162145991309503653 11606354842902373370531935)
  ·
    refine ⟨17409532264353560055797903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11606354842902373370531935 17409532264353560055797903)
    ·
      refine ⟨26114298396530340083696855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17409532264353560055797903 26114298396530340083696855)
      ·
        refine ⟨39171447594795510125545283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26114298396530340083696855 39171447594795510125545283)
        ·
          refine ⟨58757171392193265188317925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39171447594795510125545283 58757171392193265188317925)
          ·
            refine ⟨11016969636036237222809611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58757171392193265188317925 11016969636036237222809611)
            ·
              refine ⟨16525454454054355834214417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11016969636036237222809611 16525454454054355834214417)
              ·
                refine ⟨12394090840540766875660813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16525454454054355834214417 12394090840540766875660813)
                ·
                  refine ⟨4647784065202787578372805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12394090840540766875660813 4647784065202787578372805)
                  ·
                    refine ⟨871459512225522670944901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4647784065202787578372805 871459512225522670944901)
                    ·
                      rfl

theorem cell22_2545742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_2545742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545742 prefixEnd_2545742 := by exact prefixLift 2545742
  have htrace : WordTrace (prefixWord ++ tailWord_2545742) baseStart_2545742 baseEnd_2545742 := by
    simpa [prefixWord, tailWord_2545742, baseEnd_2545742] using wordTrace_append hprefix tailTrace_2545742
  have hstable : (prefixWord ++ tailWord_2545742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545742).length < 2 ^ (prefixWord ++ tailWord_2545742).sum := by decide
  have hdescent : baseEnd_2545742 < baseStart_2545742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545772 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 1, 5]
def baseStart_2545772 : Nat := 118140960795 + 2545772 * 2 ^ 59
def prefixEnd_2545772 : Nat := 4983230072969 + 3 ^ 40 * 2545772 * 2
def baseEnd_2545772 : Nat := 871469781838612592694809

theorem tailTrace_2545772 : CollatzResearch.WordTrace tailWord_2545772 prefixEnd_2545772 871469781838612592694809 := by
  unfold tailWord_2545772
  simp only [CollatzResearch.WordTrace]
  refine ⟨46425966466555151043923785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61901288622073534725231713 46425966466555151043923785)
  ·
    refine ⟨34819474849916363282942839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46425966466555151043923785 34819474849916363282942839)
    ·
      refine ⟨52229212274874544924414259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34819474849916363282942839 52229212274874544924414259)
      ·
        refine ⟨78343818412311817386621389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52229212274874544924414259 78343818412311817386621389)
        ·
          refine ⟨29378931904616931519983021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78343818412311817386621389 29378931904616931519983021)
          ·
            refine ⟨11017099464231349319993633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29378931904616931519983021 11017099464231349319993633)
            ·
              refine ⟨8262824598173511989995225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11017099464231349319993633 8262824598173511989995225)
              ·
                refine ⟨6197118448630133992496419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8262824598173511989995225 6197118448630133992496419)
                ·
                  refine ⟨9295677672945200988744629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6197118448630133992496419 9295677672945200988744629)
                  ·
                    refine ⟨871469781838612592694809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9295677672945200988744629 871469781838612592694809)
                    ·
                      rfl

theorem cell22_2545772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_2545772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545772 prefixEnd_2545772 := by exact prefixLift 2545772
  have htrace : WordTrace (prefixWord ++ tailWord_2545772) baseStart_2545772 baseEnd_2545772 := by
    simpa [prefixWord, tailWord_2545772, baseEnd_2545772] using wordTrace_append hprefix tailTrace_2545772
  have hstable : (prefixWord ++ tailWord_2545772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545772).length < 2 ^ (prefixWord ++ tailWord_2545772).sum := by decide
  have hdescent : baseEnd_2545772 < baseStart_2545772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545776 : List Nat := [2, 1, 1, 1, 5, 4, 2, 1, 1, 4]
def baseStart_2545776 : Nat := 118140960795 + 2545776 * 2 ^ 59
def prefixEnd_2545776 : Nat := 4983230072969 + 3 ^ 40 * 2545776 * 2
def baseEnd_2545776 : Nat := 871471151120357915594797

theorem tailTrace_2545776 : CollatzResearch.WordTrace tailWord_2545776 prefixEnd_2545776 871471151120357915594797 := by
  unfold tailWord_2545776
  simp only [CollatzResearch.WordTrace]
  refine ⟨46426039412547905385496591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61901385883397207180662121 46426039412547905385496591)
  ·
    refine ⟨69639059118821858078244887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46426039412547905385496591 69639059118821858078244887)
    ·
      refine ⟨104458588678232787117367331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69639059118821858078244887 104458588678232787117367331)
      ·
        refine ⟨156687883017349180676050997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104458588678232787117367331 156687883017349180676050997)
        ·
          refine ⟨14689489032876485688379781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156687883017349180676050997 14689489032876485688379781)
          ·
            refine ⟨2754279193664341066571209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14689489032876485688379781 2754279193664341066571209)
            ·
              refine ⟨2065709395248255799928407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2754279193664341066571209 2065709395248255799928407)
              ·
                refine ⟨3098564092872383699892611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065709395248255799928407 3098564092872383699892611)
                ·
                  refine ⟨4647846139308575549838917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3098564092872383699892611 4647846139308575549838917)
                  ·
                    refine ⟨871471151120357915594797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4647846139308575549838917 871471151120357915594797)
                    ·
                      rfl

theorem cell22_2545776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 1, 4].length) (baseStart_2545776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545776 prefixEnd_2545776 := by exact prefixLift 2545776
  have htrace : WordTrace (prefixWord ++ tailWord_2545776) baseStart_2545776 baseEnd_2545776 := by
    simpa [prefixWord, tailWord_2545776, baseEnd_2545776] using wordTrace_append hprefix tailTrace_2545776
  have hstable : (prefixWord ++ tailWord_2545776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545776).length < 2 ^ (prefixWord ++ tailWord_2545776).sum := by decide
  have hdescent : baseEnd_2545776 < baseStart_2545776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545789 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 4, 3]
def baseStart_2545789 : Nat := 118140960795 + 2545789 * 2 ^ 59
def prefixEnd_2545789 : Nat := 4983230072969 + 3 ^ 40 * 2545789 * 2
def baseEnd_2545789 : Nat := 871475601286030215019757

theorem tailTrace_2545789 : CollatzResearch.WordTrace tailWord_2545789 prefixEnd_2545789 871475601286030215019757 := by
  unfold tailWord_2545789
  simp only [CollatzResearch.WordTrace]
  refine ⟨92852552974048713991216421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61901701982699142660810947 92852552974048713991216421)
  ·
    refine ⟨17409853682634133873353079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92852552974048713991216421 17409853682634133873353079)
    ·
      refine ⟨26114780523951200810029619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17409853682634133873353079 26114780523951200810029619)
      ·
        refine ⟨39172170785926801215044429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26114780523951200810029619 39172170785926801215044429)
        ·
          refine ⟨14689564044722550455641661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39172170785926801215044429 14689564044722550455641661)
          ·
            refine ⟨5508586516770956420865623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14689564044722550455641661 5508586516770956420865623)
            ·
              refine ⟨8262879775156434631298435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5508586516770956420865623 8262879775156434631298435)
              ·
                refine ⟨12394319662734651946947653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8262879775156434631298435 12394319662734651946947653)
                ·
                  refine ⟨2323934936762747240052685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12394319662734651946947653 2323934936762747240052685)
                  ·
                    refine ⟨871475601286030215019757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2323934936762747240052685 871475601286030215019757)
                    ·
                      rfl

theorem cell22_2545789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_2545789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545789 prefixEnd_2545789 := by exact prefixLift 2545789
  have htrace : WordTrace (prefixWord ++ tailWord_2545789) baseStart_2545789 baseEnd_2545789 := by
    simpa [prefixWord, tailWord_2545789, baseEnd_2545789] using wordTrace_append hprefix tailTrace_2545789
  have hstable : (prefixWord ++ tailWord_2545789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545789).length < 2 ^ (prefixWord ++ tailWord_2545789).sum := by decide
  have hdescent : baseEnd_2545789 < baseStart_2545789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545806 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 1, 5]
def baseStart_2545806 : Nat := 118140960795 + 2545806 * 2 ^ 59
def prefixEnd_2545806 : Nat := 4983230072969 + 3 ^ 40 * 2545806 * 2
def baseEnd_2545806 : Nat := 871481420733447837344705

theorem tailTrace_2545806 : CollatzResearch.WordTrace tailWord_2545806 prefixEnd_2545806 871481420733447837344705 := by
  unfold tailWord_2545806
  simp only [CollatzResearch.WordTrace]
  refine ⟨11606646626873390736823159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61902115343324750596390181 11606646626873390736823159)
  ·
    refine ⟨17409969940310086105234739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11606646626873390736823159 17409969940310086105234739)
    ·
      refine ⟨26114954910465129157852109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17409969940310086105234739 26114954910465129157852109)
      ·
        refine ⟨9793108091424423434194541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26114954910465129157852109 9793108091424423434194541)
        ·
          refine ⟨3672415534284158787822953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9793108091424423434194541 3672415534284158787822953)
          ·
            refine ⟨2754311650713119090867215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3672415534284158787822953 2754311650713119090867215)
            ·
              refine ⟨4131467476069678636300823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2754311650713119090867215 4131467476069678636300823)
              ·
                refine ⟨6197201214104517954451235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4131467476069678636300823 6197201214104517954451235)
                ·
                  refine ⟨9295801821156776931676853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6197201214104517954451235 9295801821156776931676853)
                  ·
                    refine ⟨871481420733447837344705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9295801821156776931676853 871481420733447837344705)
                    ·
                      rfl

theorem cell22_2545806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_2545806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545806 prefixEnd_2545806 := by exact prefixLift 2545806
  have htrace : WordTrace (prefixWord ++ tailWord_2545806) baseStart_2545806 baseEnd_2545806 := by
    simpa [prefixWord, tailWord_2545806, baseEnd_2545806] using wordTrace_append hprefix tailTrace_2545806
  have hstable : (prefixWord ++ tailWord_2545806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545806).length < 2 ^ (prefixWord ++ tailWord_2545806).sum := by decide
  have hdescent : baseEnd_2545806 < baseStart_2545806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545838 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2545838 : Nat := 118140960795 + 2545838 * 2 ^ 59
def prefixEnd_2545838 : Nat := 4983230072969 + 3 ^ 40 * 2545838 * 2
def baseEnd_2545838 : Nat := 871492374987410420544607

theorem tailTrace_2545838 : CollatzResearch.WordTrace tailWord_2545838 prefixEnd_2545838 871492374987410420544607 := by
  unfold tailWord_2545838
  simp only [CollatzResearch.WordTrace]
  refine ⟨11606792518858899419968771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61902893433914130239833445 11606792518858899419968771)
  ·
    refine ⟨17410188778288349129953157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11606792518858899419968771 17410188778288349129953157)
    ·
      refine ⟨3264410395929065461866217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17410188778288349129953157 3264410395929065461866217)
      ·
        refine ⟨2448307796946799096399663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3264410395929065461866217 2448307796946799096399663)
        ·
          refine ⟨3672461695420198644599495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2448307796946799096399663 3672461695420198644599495)
          ·
            refine ⟨5508692543130297966899243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3672461695420198644599495 5508692543130297966899243)
            ·
              refine ⟨8263038814695446950348865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5508692543130297966899243 8263038814695446950348865)
              ·
                refine ⟨6197279111021585212761649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8263038814695446950348865 6197279111021585212761649)
                ·
                  refine ⟨4647959333266188909571237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6197279111021585212761649 4647959333266188909571237)
                  ·
                    refine ⟨871492374987410420544607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4647959333266188909571237 871492374987410420544607)
                    ·
                      rfl

theorem cell22_2545838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2545838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545838 prefixEnd_2545838 := by exact prefixLift 2545838
  have htrace : WordTrace (prefixWord ++ tailWord_2545838) baseStart_2545838 baseEnd_2545838 := by
    simpa [prefixWord, tailWord_2545838, baseEnd_2545838] using wordTrace_append hprefix tailTrace_2545838
  have hstable : (prefixWord ++ tailWord_2545838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545838).length < 2 ^ (prefixWord ++ tailWord_2545838).sum := by decide
  have hdescent : baseEnd_2545838 < baseStart_2545838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545847 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 7]
def baseStart_2545847 : Nat := 118140960795 + 2545847 * 2 ^ 59
def prefixEnd_2545847 : Nat := 4983230072969 + 3 ^ 40 * 2545847 * 2
def baseEnd_2545847 : Nat := 290498485290445799023193

theorem tailTrace_2545847 : CollatzResearch.WordTrace tailWord_2545847 prefixEnd_2545847 290498485290445799023193 := by
  unfold tailWord_2545847
  simp only [CollatzResearch.WordTrace]
  refine ⟨92854668407838589896827795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61903112271892393264551863 92854668407838589896827795)
  ·
    refine ⟨139282002611757884845241693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92854668407838589896827795 139282002611757884845241693)
    ·
      refine ⟨52230750979409206816965635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139282002611757884845241693 52230750979409206816965635)
      ·
        refine ⟨78346126469113810225448453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52230750979409206816965635 78346126469113810225448453)
        ·
          refine ⟨14689898712958839417271585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78346126469113810225448453 14689898712958839417271585)
          ·
            refine ⟨11017424034719129562953689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14689898712958839417271585 11017424034719129562953689)
            ·
              refine ⟨8263068026039347172215267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11017424034719129562953689 8263068026039347172215267)
              ·
                refine ⟨12394602039059020758322901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8263068026039347172215267 12394602039059020758322901)
                ·
                  refine ⟨290498485290445799023193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12394602039059020758322901 290498485290445799023193)
                  ·
                    rfl

theorem cell22_2545847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 7].length) (baseStart_2545847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545847 prefixEnd_2545847 := by exact prefixLift 2545847
  have htrace : WordTrace (prefixWord ++ tailWord_2545847) baseStart_2545847 baseEnd_2545847 := by
    simpa [prefixWord, tailWord_2545847, baseEnd_2545847] using wordTrace_append hprefix tailTrace_2545847
  have hstable : (prefixWord ++ tailWord_2545847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545847).length < 2 ^ (prefixWord ++ tailWord_2545847).sum := by decide
  have hdescent : baseEnd_2545847 < baseStart_2545847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545857 : List Nat := [1, 2, 6, 1, 3, 1, 2, 1, 2, 3]
def baseStart_2545857 : Nat := 118140960795 + 2545857 * 2 ^ 59
def prefixEnd_2545857 : Nat := 4983230072969 + 3 ^ 40 * 2545857 * 2
def baseEnd_2545857 : Nat := 871498879075700704319549

theorem tailTrace_2545857 : CollatzResearch.WordTrace tailWord_2545857 prefixEnd_2545857 871498879075700704319549 := by
  unfold tailWord_2545857
  simp only [CollatzResearch.WordTrace]
  refine ⟨92855033137802361604691825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61903355425201574403127883 92855033137802361604691825)
  ·
    refine ⟨69641274853351771203518869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92855033137802361604691825 69641274853351771203518869)
    ·
      refine ⟨3264434758750864275164947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69641274853351771203518869 3264434758750864275164947)
      ·
        refine ⟨4896652138126296412747421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3264434758750864275164947 4896652138126296412747421)
        ·
          refine ⟨1836244551797361154780283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4896652138126296412747421 1836244551797361154780283)
          ·
            refine ⟨2754366827696041732170425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1836244551797361154780283 2754366827696041732170425)
            ·
              refine ⟨2065775120772031299127819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2754366827696041732170425 2065775120772031299127819)
              ·
                refine ⟨3098662681158046948691729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065775120772031299127819 3098662681158046948691729)
                ·
                  refine ⟨2323997010868535211518797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3098662681158046948691729 2323997010868535211518797)
                  ·
                    refine ⟨871498879075700704319549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2323997010868535211518797 871498879075700704319549)
                    ·
                      rfl

theorem cell22_2545857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_2545857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545857 prefixEnd_2545857 := by exact prefixLift 2545857
  have htrace : WordTrace (prefixWord ++ tailWord_2545857) baseStart_2545857 baseEnd_2545857 := by
    simpa [prefixWord, tailWord_2545857, baseEnd_2545857] using wordTrace_append hprefix tailTrace_2545857
  have hstable : (prefixWord ++ tailWord_2545857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545857).length < 2 ^ (prefixWord ++ tailWord_2545857).sum := by decide
  have hdescent : baseEnd_2545857 < baseStart_2545857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545907 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 3, 5]
def baseStart_2545907 : Nat := 118140960795 + 2545907 * 2 ^ 59
def prefixEnd_2545907 : Nat := 4983230072969 + 3 ^ 40 * 2545907 * 2
def baseEnd_2545907 : Nat := 871515995097517240569395

theorem tailTrace_2545907 : CollatzResearch.WordTrace tailWord_2545907 prefixEnd_2545907 871515995097517240569395 := by
  unfold tailWord_2545907
  simp only [CollatzResearch.WordTrace]
  refine ⟨92856856787621220144011975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61904571191747480096007983 92856856787621220144011975)
  ·
    refine ⟨139285285181431830216017963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92856856787621220144011975 139285285181431830216017963)
    ·
      refine ⟨208927927772147745324026945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139285285181431830216017963 208927927772147745324026945)
      ·
        refine ⟨156695945829110808993020209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208927927772147745324026945 156695945829110808993020209)
        ·
          refine ⟨117521959371833106744765157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156695945829110808993020209 117521959371833106744765157)
          ·
            refine ⟨22035367382218707514643467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117521959371833106744765157 22035367382218707514643467)
            ·
              refine ⟨33053051073328061271965201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22035367382218707514643467 33053051073328061271965201)
              ·
                refine ⟨24789788304996045953973901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33053051073328061271965201 24789788304996045953973901)
                ·
                  refine ⟨9296170614373517232740213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24789788304996045953973901 9296170614373517232740213)
                  ·
                    refine ⟨871515995097517240569395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9296170614373517232740213 871515995097517240569395)
                    ·
                      rfl

theorem cell22_2545907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 5].length) (baseStart_2545907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545907 prefixEnd_2545907 := by exact prefixLift 2545907
  have htrace : WordTrace (prefixWord ++ tailWord_2545907) baseStart_2545907 baseEnd_2545907 := by
    simpa [prefixWord, tailWord_2545907, baseEnd_2545907] using wordTrace_append hprefix tailTrace_2545907
  have hstable : (prefixWord ++ tailWord_2545907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545907).length < 2 ^ (prefixWord ++ tailWord_2545907).sum := by decide
  have hdescent : baseEnd_2545907 < baseStart_2545907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545954 : List Nat := [3, 3, 1, 1, 3, 2, 9]
def baseStart_2545954 : Nat := 118140960795 + 2545954 * 2 ^ 59
def prefixEnd_2545954 : Nat := 4983230072969 + 3 ^ 40 * 2545954 * 2
def baseEnd_2545954 : Nat := 32278966079926843875713

theorem tailTrace_2545954 : CollatzResearch.WordTrace tailWord_2545954 prefixEnd_2545954 32278966079926843875713 := by
  unfold tailWord_2545954
  simp only [CollatzResearch.WordTrace]
  refine ⟨23214642754612736792743229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61905714012300631447315277 23214642754612736792743229)
  ·
    refine ⟨8705491032979776297278711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23214642754612736792743229 8705491032979776297278711)
    ·
      refine ⟨13058236549469664445918067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8705491032979776297278711 13058236549469664445918067)
      ·
        refine ⟨19587354824204496668877101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13058236549469664445918067 19587354824204496668877101)
        ·
          refine ⟨7345258059076686250828913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19587354824204496668877101 7345258059076686250828913)
          ·
            refine ⟨5508943544307514688121685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7345258059076686250828913 5508943544307514688121685)
            ·
              refine ⟨32278966079926843875713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5508943544307514688121685 32278966079926843875713)
              ·
                rfl

theorem cell22_2545954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 9].length) (baseStart_2545954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545954 prefixEnd_2545954 := by exact prefixLift 2545954
  have htrace : WordTrace (prefixWord ++ tailWord_2545954) baseStart_2545954 baseEnd_2545954 := by
    simpa [prefixWord, tailWord_2545954, baseEnd_2545954] using wordTrace_append hprefix tailTrace_2545954
  have hstable : (prefixWord ++ tailWord_2545954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545954).length < 2 ^ (prefixWord ++ tailWord_2545954).sum := by decide
  have hdescent : baseEnd_2545954 < baseStart_2545954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545967 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 1, 8]
def baseStart_2545967 : Nat := 118140960795 + 2545967 * 2 ^ 59
def prefixEnd_2545967 : Nat := 4983230072969 + 3 ^ 40 * 2545967 * 2
def baseEnd_2545967 : Nat := 871536534323697084069211

theorem tailTrace_2545967 : CollatzResearch.WordTrace tailWord_2545967 prefixEnd_2545967 871536534323697084069211 := by
  unfold tailWord_2545967
  simp only [CollatzResearch.WordTrace]
  refine ⟨92859045167403850391196155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61906030111602566927464103 92859045167403850391196155)
  ·
    refine ⟨139288567751105775586794233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92859045167403850391196155 139288567751105775586794233)
    ·
      refine ⟨104466425813329331690095675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139288567751105775586794233 104466425813329331690095675)
      ·
        refine ⟨156699638719993997535143513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104466425813329331690095675 156699638719993997535143513)
        ·
          refine ⟨117524729039995498151357635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156699638719993997535143513 117524729039995498151357635)
          ·
            refine ⟨176287093559993247227036453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117524729039995498151357635 176287093559993247227036453)
            ·
              refine ⟨33053830042498733855069335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176287093559993247227036453 33053830042498733855069335)
              ·
                refine ⟨49580745063748100782604003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33053830042498733855069335 49580745063748100782604003)
                ·
                  refine ⟨74371117595622151173906005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49580745063748100782604003 74371117595622151173906005)
                  ·
                    refine ⟨871536534323697084069211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74371117595622151173906005 871536534323697084069211)
                    ·
                      rfl

theorem cell22_2545967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_2545967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2545967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2545967 prefixEnd_2545967 := by exact prefixLift 2545967
  have htrace : WordTrace (prefixWord ++ tailWord_2545967) baseStart_2545967 baseEnd_2545967 := by
    simpa [prefixWord, tailWord_2545967, baseEnd_2545967] using wordTrace_append hprefix tailTrace_2545967
  have hstable : (prefixWord ++ tailWord_2545967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545967).length < 2 ^ (prefixWord ++ tailWord_2545967).sum := by decide
  have hdescent : baseEnd_2545967 < baseStart_2545967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546020 : List Nat := [2, 3, 1, 1, 3, 1, 5, 2, 1, 3]
def baseStart_2546020 : Nat := 118140960795 + 2546020 * 2 ^ 59
def prefixEnd_2546020 : Nat := 4983230072969 + 3 ^ 40 * 2546020 * 2
def baseEnd_2546020 : Nat := 871554677306822612494049

theorem tailTrace_2546020 : CollatzResearch.WordTrace tailWord_2546020 prefixEnd_2546020 871554677306822612494049 := by
  unfold tailWord_2546020
  simp only [CollatzResearch.WordTrace]
  refine ⟨46430489118105920221437757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61907318824141226961917009 46430489118105920221437757)
  ·
    refine ⟨17411433419289720083039159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46430489118105920221437757 17411433419289720083039159)
    ·
      refine ⟨26117150128934580124558739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17411433419289720083039159 26117150128934580124558739)
      ·
        refine ⟨39175725193401870186838109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26117150128934580124558739 39175725193401870186838109)
        ·
          refine ⟨14690896947525701320064291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39175725193401870186838109 14690896947525701320064291)
          ·
            refine ⟨22036345421288551980096437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14690896947525701320064291 22036345421288551980096437)
            ·
              refine ⟨2065907383245801748134041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22036345421288551980096437 2065907383245801748134041)
              ·
                refine ⟨1549430537434351311100531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2065907383245801748134041 1549430537434351311100531)
                ·
                  refine ⟨2324145806151526966650797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1549430537434351311100531 2324145806151526966650797)
                  ·
                    refine ⟨871554677306822612494049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2324145806151526966650797 871554677306822612494049)
                    ·
                      rfl

theorem cell22_2546020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_2546020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546020 prefixEnd_2546020 := by exact prefixLift 2546020
  have htrace : WordTrace (prefixWord ++ tailWord_2546020) baseStart_2546020 baseEnd_2546020 := by
    simpa [prefixWord, tailWord_2546020, baseEnd_2546020] using wordTrace_append hprefix tailTrace_2546020
  have hstable : (prefixWord ++ tailWord_2546020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546020).length < 2 ^ (prefixWord ++ tailWord_2546020).sum := by decide
  have hdescent : baseEnd_2546020 < baseStart_2546020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546059 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 3, 5]
def baseStart_2546059 : Nat := 118140960795 + 2546059 * 2 ^ 59
def prefixEnd_2546059 : Nat := 4983230072969 + 3 ^ 40 * 2546059 * 2
def baseEnd_2546059 : Nat := 871568027803839510768929

theorem tailTrace_2546059 : CollatzResearch.WordTrace tailWord_2546059 prefixEnd_2546059 871568027803839510768929 := by
  unfold tailWord_2546059
  simp only [CollatzResearch.WordTrace]
  refine ⟨92862400683070550103545231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61908267122047033402363487 92862400683070550103545231)
  ·
    refine ⟨139293601024605825155317847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92862400683070550103545231 139293601024605825155317847)
    ·
      refine ⟨208940401536908737732976771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139293601024605825155317847 208940401536908737732976771)
      ·
        refine ⟨313410602305363106599465157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208940401536908737732976771 313410602305363106599465157)
        ·
          refine ⟨58764487932255582487399717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313410602305363106599465157 58764487932255582487399717)
          ·
            refine ⟨11018341487297921716387447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58764487932255582487399717 11018341487297921716387447)
            ·
              refine ⟨16527512230946882574581171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11018341487297921716387447 16527512230946882574581171)
              ·
                refine ⟨24791268346420323861871757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16527512230946882574581171 24791268346420323861871757)
                ·
                  refine ⟨9296725629907621448201909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24791268346420323861871757 9296725629907621448201909)
                  ·
                    refine ⟨871568027803839510768929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9296725629907621448201909 871568027803839510768929)
                    ·
                      rfl

theorem cell22_2546059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 5].length) (baseStart_2546059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546059 prefixEnd_2546059 := by exact prefixLift 2546059
  have htrace : WordTrace (prefixWord ++ tailWord_2546059) baseStart_2546059 baseEnd_2546059 := by
    simpa [prefixWord, tailWord_2546059, baseEnd_2546059] using wordTrace_append hprefix tailTrace_2546059
  have hstable : (prefixWord ++ tailWord_2546059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546059).length < 2 ^ (prefixWord ++ tailWord_2546059).sum := by decide
  have hdescent : baseEnd_2546059 < baseStart_2546059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546108 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 2, 4]
def baseStart_2546108 : Nat := 118140960795 + 2546108 * 2 ^ 59
def prefixEnd_2546108 : Nat := 4983230072969 + 3 ^ 40 * 2546108 * 2
def baseEnd_2546108 : Nat := 871584801505219716293779

theorem tailTrace_2546108 : CollatzResearch.WordTrace tailWord_2546108 prefixEnd_2546108 871584801505219716293779 := by
  unfold tailWord_2546108
  simp only [CollatzResearch.WordTrace]
  refine ⟨46432093929946515736039489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61909458573262020981385985 46432093929946515736039489)
  ·
    refine ⟨34824070447459886802029617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46432093929946515736039489 34824070447459886802029617)
    ·
      refine ⟨26118052835594915101522213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34824070447459886802029617 26118052835594915101522213)
      ·
        refine ⟨4897134906674046581535415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26118052835594915101522213 4897134906674046581535415)
        ·
          refine ⟨7345702360011069872303123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4897134906674046581535415 7345702360011069872303123)
          ·
            refine ⟨11018553540016604808454685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7345702360011069872303123 11018553540016604808454685)
            ·
              refine ⟨4131957577506226803170507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11018553540016604808454685 4131957577506226803170507)
              ·
                refine ⟨6197936366259340204755761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4131957577506226803170507 6197936366259340204755761)
                ·
                  refine ⟨4648452274694505153566821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6197936366259340204755761 4648452274694505153566821)
                  ·
                    refine ⟨871584801505219716293779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4648452274694505153566821 871584801505219716293779)
                    ·
                      rfl

theorem cell22_2546108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_2546108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546108 prefixEnd_2546108 := by exact prefixLift 2546108
  have htrace : WordTrace (prefixWord ++ tailWord_2546108) baseStart_2546108 baseEnd_2546108 := by
    simpa [prefixWord, tailWord_2546108, baseEnd_2546108] using wordTrace_append hprefix tailTrace_2546108
  have hstable : (prefixWord ++ tailWord_2546108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546108).length < 2 ^ (prefixWord ++ tailWord_2546108).sum := by decide
  have hdescent : baseEnd_2546108 < baseStart_2546108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546138 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 3, 3]
def baseStart_2546138 : Nat := 118140960795 + 2546138 * 2 ^ 59
def prefixEnd_2546138 : Nat := 4983230072969 + 3 ^ 40 * 2546138 * 2
def baseEnd_2546138 : Nat := 871595071118309638043687

theorem tailTrace_2546138 : CollatzResearch.WordTrace tailWord_2546138 prefixEnd_2546138 871595071118309638043687 := by
  unfold tailWord_2546138
  simp only [CollatzResearch.WordTrace]
  refine ⟨23216320512446086648917767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61910188033189564397114045 23216320512446086648917767)
  ·
    refine ⟨34824480768669129973376651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23216320512446086648917767 34824480768669129973376651)
    ·
      refine ⟨52236721153003694960064977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34824480768669129973376651 52236721153003694960064977)
      ·
        refine ⟨39177540864752771220048733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52236721153003694960064977 39177540864752771220048733)
        ·
          refine ⟨14691577824282289207518275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39177540864752771220048733 14691577824282289207518275)
          ·
            refine ⟨22037366736423433811277413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14691577824282289207518275 22037366736423433811277413)
            ·
              refine ⟨4132006263079393839614515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22037366736423433811277413 4132006263079393839614515)
              ·
                refine ⟨6198009394619090759421773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4132006263079393839614515 6198009394619090759421773)
                ·
                  refine ⟨2324253522982159034783165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6198009394619090759421773 2324253522982159034783165)
                  ·
                    refine ⟨871595071118309638043687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2324253522982159034783165 871595071118309638043687)
                    ·
                      rfl

theorem cell22_2546138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_2546138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546138 prefixEnd_2546138 := by exact prefixLift 2546138
  have htrace : WordTrace (prefixWord ++ tailWord_2546138) baseStart_2546138 baseEnd_2546138 := by
    simpa [prefixWord, tailWord_2546138, baseEnd_2546138] using wordTrace_append hprefix tailTrace_2546138
  have hstable : (prefixWord ++ tailWord_2546138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546138).length < 2 ^ (prefixWord ++ tailWord_2546138).sum := by decide
  have hdescent : baseEnd_2546138 < baseStart_2546138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546189 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_2546189 : Nat := 118140960795 + 2546189 * 2 ^ 59
def prefixEnd_2546189 : Nat := 4983230072969 + 3 ^ 40 * 2546189 * 2
def baseEnd_2546189 : Nat := 871612529460562505018531

theorem tailTrace_2546189 : CollatzResearch.WordTrace tailWord_2546189 prefixEnd_2546189 871612529460562505018531 := by
  unfold tailWord_2546189
  simp only [CollatzResearch.WordTrace]
  refine ⟨92867142172599582305777621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61911428115066388203851747 92867142172599582305777621)
  ·
    refine ⟨2176573644670302710291663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 92867142172599582305777621 2176573644670302710291663)
    ·
      refine ⟨3264860467005454065437495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2176573644670302710291663 3264860467005454065437495)
      ·
        refine ⟨4897290700508181098156243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3264860467005454065437495 4897290700508181098156243)
        ·
          refine ⟨7345936050762271647234365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4897290700508181098156243 7345936050762271647234365)
          ·
            refine ⟨2754726019035851867712887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7345936050762271647234365 2754726019035851867712887)
            ·
              refine ⟨4132089028553777801569331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2754726019035851867712887 4132089028553777801569331)
              ·
                refine ⟨6198133542830666702353997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4132089028553777801569331 6198133542830666702353997)
                ·
                  refine ⟨2324300078561500013382749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6198133542830666702353997 2324300078561500013382749)
                  ·
                    refine ⟨871612529460562505018531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2324300078561500013382749 871612529460562505018531)
                    ·
                      rfl

theorem cell22_2546189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_2546189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546189 prefixEnd_2546189 := by exact prefixLift 2546189
  have htrace : WordTrace (prefixWord ++ tailWord_2546189) baseStart_2546189 baseEnd_2546189 := by
    simpa [prefixWord, tailWord_2546189, baseEnd_2546189] using wordTrace_append hprefix tailTrace_2546189
  have hstable : (prefixWord ++ tailWord_2546189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546189).length < 2 ^ (prefixWord ++ tailWord_2546189).sum := by decide
  have hdescent : baseEnd_2546189 < baseStart_2546189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546226 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_2546226 : Nat := 118140960795 + 2546226 * 2 ^ 59
def prefixEnd_2546226 : Nat := 4983230072969 + 3 ^ 40 * 2546226 * 2
def baseEnd_2546226 : Nat := 871625195316706741843417

theorem tailTrace_2546226 : CollatzResearch.WordTrace tailWord_2546226 prefixEnd_2546226 871625195316706741843417 := by
  unfold tailWord_2546226
  simp only [CollatzResearch.WordTrace]
  refine ⟨23217122918366384406218633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61912327782310358416583021 23217122918366384406218633)
  ·
    refine ⟨17412842188774788304663975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23217122918366384406218633 17412842188774788304663975)
    ·
      refine ⟨26119263283162182456995963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17412842188774788304663975 26119263283162182456995963)
      ·
        refine ⟨39178894924743273685493945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26119263283162182456995963 39178894924743273685493945)
        ·
          refine ⟨29384171193557455264120459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39178894924743273685493945 29384171193557455264120459)
          ·
            refine ⟨44076256790336182896180689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29384171193557455264120459 44076256790336182896180689)
            ·
              refine ⟨33057192592752137172135517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44076256790336182896180689 33057192592752137172135517)
              ·
                refine ⟨12396447222282051439550819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33057192592752137172135517 12396447222282051439550819)
                ·
                  refine ⟨18594670833423077159326229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12396447222282051439550819 18594670833423077159326229)
                  ·
                    refine ⟨871625195316706741843417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18594670833423077159326229 871625195316706741843417)
                    ·
                      rfl

theorem cell22_2546226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_2546226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546226 prefixEnd_2546226 := by exact prefixLift 2546226
  have htrace : WordTrace (prefixWord ++ tailWord_2546226) baseStart_2546226 baseEnd_2546226 := by
    simpa [prefixWord, tailWord_2546226, baseEnd_2546226] using wordTrace_append hprefix tailTrace_2546226
  have hstable : (prefixWord ++ tailWord_2546226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546226).length < 2 ^ (prefixWord ++ tailWord_2546226).sum := by decide
  have hdescent : baseEnd_2546226 < baseStart_2546226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546241 : List Nat := [1, 2, 5, 1, 1, 12]
def baseStart_2546241 : Nat := 118140960795 + 2546241 * 2 ^ 59
def prefixEnd_2546241 : Nat := 4983230072969 + 3 ^ 40 * 2546241 * 2
def baseEnd_2546241 : Nat := 10760868273126564231091

theorem tailTrace_2546241 : CollatzResearch.WordTrace tailWord_2546241 prefixEnd_2546241 10760868273126564231091 := by
  unfold tailWord_2546241
  simp only [CollatzResearch.WordTrace]
  refine ⟨92869038768411195186670577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61912692512274130124447051 92869038768411195186670577)
  ·
    refine ⟨69651779076308396390002933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92869038768411195186670577 69651779076308396390002933)
    ·
      refine ⟨6529854288403912161562775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69651779076308396390002933 6529854288403912161562775)
      ·
        refine ⟨9794781432605868242344163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6529854288403912161562775 9794781432605868242344163)
        ·
          refine ⟨14692172148908802363516245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9794781432605868242344163 14692172148908802363516245)
          ·
            refine ⟨10760868273126564231091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14692172148908802363516245 10760868273126564231091)
            ·
              rfl

theorem cell22_2546241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 12].length) (baseStart_2546241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546241 prefixEnd_2546241 := by exact prefixLift 2546241
  have htrace : WordTrace (prefixWord ++ tailWord_2546241) baseStart_2546241 baseEnd_2546241 := by
    simpa [prefixWord, tailWord_2546241, baseEnd_2546241] using wordTrace_append hprefix tailTrace_2546241
  have hstable : (prefixWord ++ tailWord_2546241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546241).length < 2 ^ (prefixWord ++ tailWord_2546241).sum := by decide
  have hdescent : baseEnd_2546241 < baseStart_2546241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546245 : List Nat := [1, 3, 1, 1, 1, 6, 2, 2, 2, 3]
def baseStart_2546245 : Nat := 118140960795 + 2546245 * 2 ^ 59
def prefixEnd_2546245 : Nat := 4983230072969 + 3 ^ 40 * 2546245 * 2
def baseEnd_2546245 : Nat := 871631699404997025618359

theorem tailTrace_2546245 : CollatzResearch.WordTrace tailWord_2546245 prefixEnd_2546245 871631699404997025618359 := by
  unfold tailWord_2546245
  simp only [CollatzResearch.WordTrace]
  refine ⟨92869184660396703869816189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61912789773597802579877459 92869184660396703869816189)
  ·
    refine ⟨34825944247648763951181071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92869184660396703869816189 34825944247648763951181071)
    ·
      refine ⟨52238916371473145926771607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34825944247648763951181071 52238916371473145926771607)
      ·
        refine ⟨78358374557209718890157411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52238916371473145926771607 78358374557209718890157411)
        ·
          refine ⟨117537561835814578335236117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78358374557209718890157411 117537561835814578335236117)
          ·
            refine ⟨5509573211053808359464193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117537561835814578335236117 5509573211053808359464193)
            ·
              refine ⟨4132179908290356269598145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5509573211053808359464193 4132179908290356269598145)
              ·
                refine ⟨3099134931217767202198609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4132179908290356269598145 3099134931217767202198609)
                ·
                  refine ⟨2324351198413325401648957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3099134931217767202198609 2324351198413325401648957)
                  ·
                    refine ⟨871631699404997025618359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2324351198413325401648957 871631699404997025618359)
                    ·
                      rfl

theorem cell22_2546245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_2546245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546245 prefixEnd_2546245 := by exact prefixLift 2546245
  have htrace : WordTrace (prefixWord ++ tailWord_2546245) baseStart_2546245 baseEnd_2546245 := by
    simpa [prefixWord, tailWord_2546245, baseEnd_2546245] using wordTrace_append hprefix tailTrace_2546245
  have hstable : (prefixWord ++ tailWord_2546245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546245).length < 2 ^ (prefixWord ++ tailWord_2546245).sum := by decide
  have hdescent : baseEnd_2546245 < baseStart_2546245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546247 : List Nat := [1, 1, 4, 1, 4, 3, 2, 2, 4]
def baseStart_2546247 : Nat := 118140960795 + 2546247 * 2 ^ 59
def prefixEnd_2546247 : Nat := 4983230072969 + 3 ^ 40 * 2546247 * 2
def baseEnd_2546247 : Nat := 290544128015289895689451

theorem tailTrace_2546247 : CollatzResearch.WordTrace tailWord_2546247 prefixEnd_2546247 290544128015289895689451 := by
  unfold tailWord_2546247
  simp only [CollatzResearch.WordTrace]
  refine ⟨92869257606389458211388995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61912838404259638807592663 92869257606389458211388995)
  ·
    refine ⟨139303886409584187317083493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92869257606389458211388995 139303886409584187317083493)
    ·
      refine ⟨26119478701797035121953155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139303886409584187317083493 26119478701797035121953155)
      ·
        refine ⟨39179218052695552682929733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26119478701797035121953155 39179218052695552682929733)
        ·
          refine ⟨7346103384880416128049325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39179218052695552682929733 7346103384880416128049325)
          ·
            refine ⟨2754788769330156048018497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7346103384880416128049325 2754788769330156048018497)
            ·
              refine ⟨2066091576997617036013873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2754788769330156048018497 2066091576997617036013873)
              ·
                refine ⟨1549568682748212777010405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2066091576997617036013873 1549568682748212777010405)
                ·
                  refine ⟨290544128015289895689451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1549568682748212777010405 290544128015289895689451)
                  ·
                    rfl

theorem cell22_2546247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 4].length) (baseStart_2546247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546247 prefixEnd_2546247 := by exact prefixLift 2546247
  have htrace : WordTrace (prefixWord ++ tailWord_2546247) baseStart_2546247 baseEnd_2546247 := by
    simpa [prefixWord, tailWord_2546247, baseEnd_2546247] using wordTrace_append hprefix tailTrace_2546247
  have hstable : (prefixWord ++ tailWord_2546247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546247).length < 2 ^ (prefixWord ++ tailWord_2546247).sum := by decide
  have hdescent : baseEnd_2546247 < baseStart_2546247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546273 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 5, 3]
def baseStart_2546273 : Nat := 118140960795 + 2546273 * 2 ^ 59
def prefixEnd_2546273 : Nat := 4983230072969 + 3 ^ 40 * 2546273 * 2
def baseEnd_2546273 : Nat := 871641284377214285918273

theorem tailTrace_2546273 : CollatzResearch.WordTrace tailWord_2546273 prefixEnd_2546273 871641284377214285918273 := by
  unfold tailWord_2546273
  simp only [CollatzResearch.WordTrace]
  refine ⟨92870205904295264651835473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61913470602863509767890315 92870205904295264651835473)
  ·
    refine ⟨69652654428221448488876605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92870205904295264651835473 69652654428221448488876605)
    ·
      refine ⟨26119745410583043183328727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69652654428221448488876605 26119745410583043183328727)
      ·
        refine ⟨39179618115874564774993091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26119745410583043183328727 39179618115874564774993091)
        ·
          refine ⟨58769427173811847162489637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39179618115874564774993091 58769427173811847162489637)
          ·
            refine ⟨11019267595089721342966807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58769427173811847162489637 11019267595089721342966807)
            ·
              refine ⟨16528901392634582014450211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11019267595089721342966807 16528901392634582014450211)
              ·
                refine ⟨24793352088951873021675317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16528901392634582014450211 24793352088951873021675317)
                ·
                  refine ⟨2324376758339238095782061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24793352088951873021675317 2324376758339238095782061)
                  ·
                    refine ⟨871641284377214285918273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2324376758339238095782061 871641284377214285918273)
                    ·
                      rfl

theorem cell22_2546273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_2546273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546273 prefixEnd_2546273 := by exact prefixLift 2546273
  have htrace : WordTrace (prefixWord ++ tailWord_2546273) baseStart_2546273 baseEnd_2546273 := by
    simpa [prefixWord, tailWord_2546273, baseEnd_2546273] using wordTrace_append hprefix tailTrace_2546273
  have hstable : (prefixWord ++ tailWord_2546273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546273).length < 2 ^ (prefixWord ++ tailWord_2546273).sum := by decide
  have hdescent : baseEnd_2546273 < baseStart_2546273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546277 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 2, 4]
def baseStart_2546277 : Nat := 118140960795 + 2546277 * 2 ^ 59
def prefixEnd_2546277 : Nat := 4983230072969 + 3 ^ 40 * 2546277 * 2
def baseEnd_2546277 : Nat := 871642653658959608818261

theorem tailTrace_2546277 : CollatzResearch.WordTrace tailWord_2546277 prefixEnd_2546277 871642653658959608818261 := by
  unfold tailWord_2546277
  simp only [CollatzResearch.WordTrace]
  refine ⟨92870351796280773334981085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61913567864187182223320723 92870351796280773334981085)
  ·
    refine ⟨34826381923605290000617907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92870351796280773334981085 34826381923605290000617907)
    ·
      refine ⟨52239572885407935000926861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34826381923605290000617907 52239572885407935000926861)
      ·
        refine ⟨19589839832027975625347573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52239572885407935000926861 19589839832027975625347573)
        ·
          refine ⟨1836547484252622714876335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19589839832027975625347573 1836547484252622714876335)
          ·
            refine ⟨2754821226378934072314503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1836547484252622714876335 2754821226378934072314503)
            ·
              refine ⟨4132231839568401108471755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2754821226378934072314503 4132231839568401108471755)
              ·
                refine ⟨6198347759352601662707633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4132231839568401108471755 6198347759352601662707633)
                ·
                  refine ⟨4648760819514451247030725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6198347759352601662707633 4648760819514451247030725)
                  ·
                    refine ⟨871642653658959608818261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4648760819514451247030725 871642653658959608818261)
                    ·
                      rfl

theorem cell22_2546277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_2546277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546277 prefixEnd_2546277 := by exact prefixLift 2546277
  have htrace : WordTrace (prefixWord ++ tailWord_2546277) baseStart_2546277 baseEnd_2546277 := by
    simpa [prefixWord, tailWord_2546277, baseEnd_2546277] using wordTrace_append hprefix tailTrace_2546277
  have hstable : (prefixWord ++ tailWord_2546277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546277).length < 2 ^ (prefixWord ++ tailWord_2546277).sum := by decide
  have hdescent : baseEnd_2546277 < baseStart_2546277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546316 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 2, 8]
def baseStart_2546316 : Nat := 118140960795 + 2546316 * 2 ^ 59
def prefixEnd_2546316 : Nat := 4983230072969 + 3 ^ 40 * 2546316 * 2
def baseEnd_2546316 : Nat := 871656004155976507093141

theorem tailTrace_2546316 : CollatzResearch.WordTrace tailWord_2546316 prefixEnd_2546316 871656004155976507093141 := by
  unfold tailWord_2546316
  simp only [CollatzResearch.WordTrace]
  refine ⟨46435887121569741497825401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61914516162092988663767201 46435887121569741497825401)
  ·
    refine ⟨34826915341177306123369051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46435887121569741497825401 34826915341177306123369051)
    ·
      refine ⟨52240373011765959185053577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34826915341177306123369051 52240373011765959185053577)
      ·
        refine ⟨39180279758824469388790183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52240373011765959185053577 39180279758824469388790183)
        ·
          refine ⟨58770419638236704083185275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39180279758824469388790183 58770419638236704083185275)
          ·
            refine ⟨88155629457355056124777913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58770419638236704083185275 88155629457355056124777913)
            ·
              refine ⟨66116722093016292093583435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88155629457355056124777913 66116722093016292093583435)
              ·
                refine ⟨99175083139524438140375153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66116722093016292093583435 99175083139524438140375153)
                ·
                  refine ⟨74381312354643328605281365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99175083139524438140375153 74381312354643328605281365)
                  ·
                    refine ⟨871656004155976507093141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74381312354643328605281365 871656004155976507093141)
                    ·
                      rfl

theorem cell22_2546316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_2546316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546316 prefixEnd_2546316 := by exact prefixLift 2546316
  have htrace : WordTrace (prefixWord ++ tailWord_2546316) baseStart_2546316 baseEnd_2546316 := by
    simpa [prefixWord, tailWord_2546316, baseEnd_2546316] using wordTrace_append hprefix tailTrace_2546316
  have hstable : (prefixWord ++ tailWord_2546316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546316).length < 2 ^ (prefixWord ++ tailWord_2546316).sum := by decide
  have hdescent : baseEnd_2546316 < baseStart_2546316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546318 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_2546318 : Nat := 118140960795 + 2546318 * 2 ^ 59
def prefixEnd_2546318 : Nat := 4983230072969 + 3 ^ 40 * 2546318 * 2
def baseEnd_2546318 : Nat := 871656688796849168543135

theorem tailTrace_2546318 : CollatzResearch.WordTrace tailWord_2546318 prefixEnd_2546318 871656688796849168543135 := by
  unfold tailWord_2546318
  simp only [CollatzResearch.WordTrace]
  refine ⟨11608980898641529667152951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61914564792754824891482405 11608980898641529667152951)
  ·
    refine ⟨17413471347962294500729427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11608980898641529667152951 17413471347962294500729427)
    ·
      refine ⟨26120207021943441751094141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17413471347962294500729427 26120207021943441751094141)
      ·
        refine ⟨9795077633228790656660303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26120207021943441751094141 9795077633228790656660303)
        ·
          refine ⟨14692616449843185984990455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9795077633228790656660303 14692616449843185984990455)
          ·
            refine ⟨22038924674764778977485683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14692616449843185984990455 22038924674764778977485683)
            ·
              refine ⟨33058387012147168466228525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22038924674764778977485683 33058387012147168466228525)
              ·
                refine ⟨12396895129555188174835697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33058387012147168466228525 12396895129555188174835697)
                ·
                  refine ⟨9297671347166391131126773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12396895129555188174835697 9297671347166391131126773)
                  ·
                    refine ⟨871656688796849168543135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9297671347166391131126773 871656688796849168543135)
                    ·
                      rfl

theorem cell22_2546318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_2546318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546318 prefixEnd_2546318 := by exact prefixLift 2546318
  have htrace : WordTrace (prefixWord ++ tailWord_2546318) baseStart_2546318 baseEnd_2546318 := by
    simpa [prefixWord, tailWord_2546318, baseEnd_2546318] using wordTrace_append hprefix tailTrace_2546318
  have hstable : (prefixWord ++ tailWord_2546318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546318).length < 2 ^ (prefixWord ++ tailWord_2546318).sum := by decide
  have hdescent : baseEnd_2546318 < baseStart_2546318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546333 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_2546333 : Nat := 118140960795 + 2546333 * 2 ^ 59
def prefixEnd_2546333 : Nat := 4983230072969 + 3 ^ 40 * 2546333 * 2
def baseEnd_2546333 : Nat := 871661823603394129418089

theorem tailTrace_2546333 : CollatzResearch.WordTrace tailWord_2546333 prefixEnd_2546333 871661823603394129418089 := by
  unfold tailWord_2546333
  simp only [CollatzResearch.WordTrace]
  refine ⟨92872394284077894899019653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61914929522718596599346435 92872394284077894899019653)
  ·
    refine ⟨17413573928264605293566185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92872394284077894899019653 17413573928264605293566185)
    ·
      refine ⟨13060180446198453970174639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17413573928264605293566185 13060180446198453970174639)
      ·
        refine ⟨19590270669297680955261959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13060180446198453970174639 19590270669297680955261959)
        ·
          refine ⟨29385406003946521432892939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19590270669297680955261959 29385406003946521432892939)
          ·
            refine ⟨44078109005919782149339409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29385406003946521432892939 44078109005919782149339409)
            ·
              refine ⟨33058581754439836612004557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44078109005919782149339409 33058581754439836612004557)
              ·
                refine ⟨12396968157914938729501709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33058581754439836612004557 12396968157914938729501709)
                ·
                  refine ⟨4648863059218102023563141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12396968157914938729501709 4648863059218102023563141)
                  ·
                    refine ⟨871661823603394129418089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4648863059218102023563141 871661823603394129418089)
                    ·
                      rfl

theorem cell22_2546333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_2546333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546333 prefixEnd_2546333 := by exact prefixLift 2546333
  have htrace : WordTrace (prefixWord ++ tailWord_2546333) baseStart_2546333 baseEnd_2546333 := by
    simpa [prefixWord, tailWord_2546333, baseEnd_2546333] using wordTrace_append hprefix tailTrace_2546333
  have hstable : (prefixWord ++ tailWord_2546333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546333).length < 2 ^ (prefixWord ++ tailWord_2546333).sum := by decide
  have hdescent : baseEnd_2546333 < baseStart_2546333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546358 : List Nat := [5, 1, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2546358 : Nat := 118140960795 + 2546358 * 2 ^ 59
def prefixEnd_2546358 : Nat := 4983230072969 + 3 ^ 40 * 2546358 * 2
def baseEnd_2546358 : Nat := 871670381614302397543013

theorem tailTrace_2546358 : CollatzResearch.WordTrace tailWord_2546358 prefixEnd_2546358 871670381614302397543013 := by
  unfold tailWord_2546358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5804581631811707760542483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61915537405991549445786485 5804581631811707760542483)
  ·
    refine ⟨8706872447717561640813725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5804581631811707760542483 8706872447717561640813725)
    ·
      refine ⟨3265077167894085615305147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8706872447717561640813725 3265077167894085615305147)
      ·
        refine ⟨4897615751841128422957721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3265077167894085615305147 4897615751841128422957721)
        ·
          refine ⟨3673211813880846317218291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4897615751841128422957721 3673211813880846317218291)
          ·
            refine ⟨5509817720821269475827437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3673211813880846317218291 5509817720821269475827437)
            ·
              refine ⟨2066181645307976053435289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5509817720821269475827437 2066181645307976053435289)
              ·
                refine ⟨1549636233980982040076467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2066181645307976053435289 1549636233980982040076467)
                ·
                  refine ⟨2324454350971473060114701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1549636233980982040076467 2324454350971473060114701)
                  ·
                    refine ⟨871670381614302397543013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2324454350971473060114701 871670381614302397543013)
                    ·
                      rfl

theorem cell22_2546358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2546358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546358 prefixEnd_2546358 := by exact prefixLift 2546358
  have htrace : WordTrace (prefixWord ++ tailWord_2546358) baseStart_2546358 baseEnd_2546358 := by
    simpa [prefixWord, tailWord_2546358, baseEnd_2546358] using wordTrace_append hprefix tailTrace_2546358
  have hstable : (prefixWord ++ tailWord_2546358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546358).length < 2 ^ (prefixWord ++ tailWord_2546358).sum := by decide
  have hdescent : baseEnd_2546358 < baseStart_2546358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546365 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 6]
def baseStart_2546365 : Nat := 118140960795 + 2546365 * 2 ^ 59
def prefixEnd_2546365 : Nat := 4983230072969 + 3 ^ 40 * 2546365 * 2
def baseEnd_2546365 : Nat := 290557592619118904205997

theorem tailTrace_2546365 : CollatzResearch.WordTrace tailWord_2546365 prefixEnd_2546365 290557592619118904205997 := by
  unfold tailWord_2546365
  simp only [CollatzResearch.WordTrace]
  refine ⟨92873561419961964364184549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61915707613307976242789699 92873561419961964364184549)
  ·
    refine ⟨17413792766242868318284603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92873561419961964364184549 17413792766242868318284603)
    ·
      refine ⟨26120689149364302477426905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17413792766242868318284603 26120689149364302477426905)
      ·
        refine ⟨19590516862023226858070179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26120689149364302477426905 19590516862023226858070179)
        ·
          refine ⟨29385775293034840287105269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19590516862023226858070179 29385775293034840287105269)
          ·
            refine ⟨2754916433722016276916119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29385775293034840287105269 2754916433722016276916119)
            ·
              refine ⟨4132374650583024415374179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2754916433722016276916119 4132374650583024415374179)
              ·
                refine ⟨6198561975874536623061269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4132374650583024415374179 6198561975874536623061269)
                ·
                  refine ⟨290557592619118904205997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6198561975874536623061269 290557592619118904205997)
                  ·
                    rfl

theorem cell22_2546365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_2546365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546365 prefixEnd_2546365 := by exact prefixLift 2546365
  have htrace : WordTrace (prefixWord ++ tailWord_2546365) baseStart_2546365 baseEnd_2546365 := by
    simpa [prefixWord, tailWord_2546365, baseEnd_2546365] using wordTrace_append hprefix tailTrace_2546365
  have hstable : (prefixWord ++ tailWord_2546365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546365).length < 2 ^ (prefixWord ++ tailWord_2546365).sum := by decide
  have hdescent : baseEnd_2546365 < baseStart_2546365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546453 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 1, 7]
def baseStart_2546453 : Nat := 118140960795 + 2546453 * 2 ^ 59
def prefixEnd_2546453 : Nat := 4983230072969 + 3 ^ 40 * 2546453 * 2
def baseEnd_2546453 : Nat := 871702902055753816417721

theorem tailTrace_2546453 : CollatzResearch.WordTrace tailWord_2546453 prefixEnd_2546453 871702902055753816417721 := by
  unfold tailWord_2546453
  simp only [CollatzResearch.WordTrace]
  refine ⟨92876771043643155393388013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61917847362428770262258675 92876771043643155393388013)
  ·
    refine ⟨34828789141366183272520505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92876771043643155393388013 34828789141366183272520505)
    ·
      refine ⟨26121591856024637454390379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34828789141366183272520505 26121591856024637454390379)
      ·
        refine ⟨39182387784036956181585569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26121591856024637454390379 39182387784036956181585569)
        ·
          refine ⟨29386790838027717136189177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39182387784036956181585569 29386790838027717136189177)
          ·
            refine ⟨22040093128520787852141883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29386790838027717136189177 22040093128520787852141883)
            ·
              refine ⟨33060139692781181778212825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22040093128520787852141883 33060139692781181778212825)
              ·
                refine ⟨24795104769585886333659619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33060139692781181778212825 24795104769585886333659619)
                ·
                  refine ⟨37192657154378829500489429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24795104769585886333659619 37192657154378829500489429)
                  ·
                    refine ⟨871702902055753816417721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37192657154378829500489429 871702902055753816417721)
                    ·
                      rfl

theorem cell22_2546453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_2546453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546453 prefixEnd_2546453 := by exact prefixLift 2546453
  have htrace : WordTrace (prefixWord ++ tailWord_2546453) baseStart_2546453 baseEnd_2546453 := by
    simpa [prefixWord, tailWord_2546453, baseEnd_2546453] using wordTrace_append hprefix tailTrace_2546453
  have hstable : (prefixWord ++ tailWord_2546453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546453).length < 2 ^ (prefixWord ++ tailWord_2546453).sum := by decide
  have hdescent : baseEnd_2546453 < baseStart_2546453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546532 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 4, 3]
def baseStart_2546532 : Nat := 118140960795 + 2546532 * 2 ^ 59
def prefixEnd_2546532 : Nat := 4983230072969 + 3 ^ 40 * 2546532 * 2
def baseEnd_2546532 : Nat := 871729945370223943692479

theorem tailTrace_2546532 : CollatzResearch.WordTrace tailWord_2546532 prefixEnd_2546532 871729945370223943692479 := by
  unfold tailWord_2546532
  simp only [CollatzResearch.WordTrace]
  refine ⟨46439826205178475942756925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61919768273571301257009233 46439826205178475942756925)
  ·
    refine ⟨17414934826941928478533847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46439826205178475942756925 17414934826941928478533847)
    ·
      refine ⟨26122402240412892717800771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17414934826941928478533847 26122402240412892717800771)
      ·
        refine ⟨39183603360619339076701157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26122402240412892717800771 39183603360619339076701157)
        ·
          refine ⟨7346925630116126076881467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39183603360619339076701157 7346925630116126076881467)
          ·
            refine ⟨11020388445174189115322201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7346925630116126076881467 11020388445174189115322201)
            ·
              refine ⟨8265291333880641836491651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11020388445174189115322201 8265291333880641836491651)
              ·
                refine ⟨12397937000820962754737477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8265291333880641836491651 12397937000820962754737477)
                ·
                  refine ⟨2324613187653930516513277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12397937000820962754737477 2324613187653930516513277)
                  ·
                    refine ⟨871729945370223943692479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2324613187653930516513277 871729945370223943692479)
                    ·
                      rfl

theorem cell22_2546532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_2546532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546532 prefixEnd_2546532 := by exact prefixLift 2546532
  have htrace : WordTrace (prefixWord ++ tailWord_2546532) baseStart_2546532 baseEnd_2546532 := by
    simpa [prefixWord, tailWord_2546532, baseEnd_2546532] using wordTrace_append hprefix tailTrace_2546532
  have hstable : (prefixWord ++ tailWord_2546532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546532).length < 2 ^ (prefixWord ++ tailWord_2546532).sum := by decide
  have hdescent : baseEnd_2546532 < baseStart_2546532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546545 : List Nat := [1, 2, 2, 2, 1, 5, 2, 7]
def baseStart_2546545 : Nat := 118140960795 + 2546545 * 2 ^ 59
def prefixEnd_2546545 : Nat := 4983230072969 + 3 ^ 40 * 2546545 * 2
def baseEnd_2546545 : Nat := 96859377281766249235271

theorem tailTrace_2546545 : CollatzResearch.WordTrace tailWord_2546545 prefixEnd_2546545 96859377281766249235271 := by
  unfold tailWord_2546545
  simp only [CollatzResearch.WordTrace]
  refine ⟨92880126559309855105737089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61920084372873236737158059 92880126559309855105737089)
  ·
    refine ⟨69660094919482391329302817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92880126559309855105737089 69660094919482391329302817)
    ·
      refine ⟨52245071189611793496977113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69660094919482391329302817 52245071189611793496977113)
      ·
        refine ⟨39183803392208845122732835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52245071189611793496977113 39183803392208845122732835)
        ·
          refine ⟨58775705088313267684099253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39183803392208845122732835 58775705088313267684099253)
          ·
            refine ⟨5510222352029368845384305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58775705088313267684099253 5510222352029368845384305)
            ·
              refine ⟨4132666764022026634038229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5510222352029368845384305 4132666764022026634038229)
              ·
                refine ⟨96859377281766249235271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4132666764022026634038229 96859377281766249235271)
                ·
                  rfl

theorem cell22_2546545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 7].length) (baseStart_2546545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546545 prefixEnd_2546545 := by exact prefixLift 2546545
  have htrace : WordTrace (prefixWord ++ tailWord_2546545) baseStart_2546545 baseEnd_2546545 := by
    simpa [prefixWord, tailWord_2546545, baseEnd_2546545] using wordTrace_append hprefix tailTrace_2546545
  have hstable : (prefixWord ++ tailWord_2546545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546545).length < 2 ^ (prefixWord ++ tailWord_2546545).sum := by decide
  have hdescent : baseEnd_2546545 < baseStart_2546545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546549 : List Nat := [1, 3, 4, 1, 1, 3, 1, 3, 2, 3]
def baseStart_2546549 : Nat := 118140960795 + 2546549 * 2 ^ 59
def prefixEnd_2546549 : Nat := 4983230072969 + 3 ^ 40 * 2546549 * 2
def baseEnd_2546549 : Nat := 871735764817641566017427

theorem tailTrace_2546549 : CollatzResearch.WordTrace tailWord_2546549 prefixEnd_2546549 871735764817641566017427 := by
  unfold tailWord_2546549
  simp only [CollatzResearch.WordTrace]
  refine ⟨92880272451295363788882701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61920181634196909192588467 92880272451295363788882701)
  ·
    refine ⟨34830102169235761420831013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92880272451295363788882701 34830102169235761420831013)
    ·
      refine ⟨6530644156731705266405815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34830102169235761420831013 6530644156731705266405815)
      ·
        refine ⟨9795966235097557899608723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6530644156731705266405815 9795966235097557899608723)
        ·
          refine ⟨14693949352646336849413085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9795966235097557899608723 14693949352646336849413085)
          ·
            refine ⟨5510231007242376318529907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14693949352646336849413085 5510231007242376318529907)
            ·
              refine ⟨8265346510863564477794861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5510231007242376318529907 8265346510863564477794861)
              ·
                refine ⟨3099504941573836679173073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8265346510863564477794861 3099504941573836679173073)
                ·
                  refine ⟨2324628706180377509379805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3099504941573836679173073 2324628706180377509379805)
                  ·
                    refine ⟨871735764817641566017427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2324628706180377509379805 871735764817641566017427)
                    ·
                      rfl

theorem cell22_2546549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_2546549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546549 prefixEnd_2546549 := by exact prefixLift 2546549
  have htrace : WordTrace (prefixWord ++ tailWord_2546549) baseStart_2546549 baseEnd_2546549 := by
    simpa [prefixWord, tailWord_2546549, baseEnd_2546549] using wordTrace_append hprefix tailTrace_2546549
  have hstable : (prefixWord ++ tailWord_2546549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546549).length < 2 ^ (prefixWord ++ tailWord_2546549).sum := by decide
  have hdescent : baseEnd_2546549 < baseStart_2546549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546759 : List Nat := [1, 1, 4, 1, 3, 3, 2, 2, 5]
def baseStart_2546759 : Nat := 118140960795 + 2546759 * 2 ^ 59
def prefixEnd_2546759 : Nat := 4983230072969 + 3 ^ 40 * 2546759 * 2
def baseEnd_2546759 : Nat := 290602550703090339422261

theorem tailTrace_2546759 : CollatzResearch.WordTrace tailWord_2546759 prefixEnd_2546759 290602550703090339422261 := by
  unfold tailWord_2546759
  simp only [CollatzResearch.WordTrace]
  refine ⟨92887931780534569654027331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61925287853689713102684887 92887931780534569654027331)
  ·
    refine ⟨139331897670801854481040997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92887931780534569654027331 139331897670801854481040997)
    ·
      refine ⟨26124730813275347715195187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139331897670801854481040997 26124730813275347715195187)
      ·
        refine ⟨39187096219913021572792781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26124730813275347715195187 39187096219913021572792781)
        ·
          refine ⟨14695161082467383089797293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39187096219913021572792781 14695161082467383089797293)
          ·
            refine ⟨5510685405925268658673985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14695161082467383089797293 5510685405925268658673985)
            ·
              refine ⟨4133014054443951494005489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5510685405925268658673985 4133014054443951494005489)
              ·
                refine ⟨3099760540832963620504117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4133014054443951494005489 3099760540832963620504117)
                ·
                  refine ⟨290602550703090339422261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3099760540832963620504117 290602550703090339422261)
                  ·
                    rfl

theorem cell22_2546759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 5].length) (baseStart_2546759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546759 prefixEnd_2546759 := by exact prefixLift 2546759
  have htrace : WordTrace (prefixWord ++ tailWord_2546759) baseStart_2546759 baseEnd_2546759 := by
    simpa [prefixWord, tailWord_2546759, baseEnd_2546759] using wordTrace_append hprefix tailTrace_2546759
  have hstable : (prefixWord ++ tailWord_2546759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546759).length < 2 ^ (prefixWord ++ tailWord_2546759).sum := by decide
  have hdescent : baseEnd_2546759 < baseStart_2546759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546789 : List Nat := [1, 3, 1, 3, 2, 1, 2, 4, 1, 4]
def baseStart_2546789 : Nat := 118140960795 + 2546789 * 2 ^ 59
def prefixEnd_2546789 : Nat := 4983230072969 + 3 ^ 40 * 2546789 * 2
def baseEnd_2546789 : Nat := 871817921722360940016691

theorem tailTrace_2546789 : CollatzResearch.WordTrace tailWord_2546789 prefixEnd_2546789 871817921722360940016691 := by
  unfold tailWord_2546789
  simp only [CollatzResearch.WordTrace]
  refine ⟨92889025970425884777619421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61926017313617256518412947 92889025970425884777619421)
  ·
    refine ⟨34833384738909706791607283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92889025970425884777619421 34833384738909706791607283)
    ·
      refine ⟨52250077108364560187410925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34833384738909706791607283 52250077108364560187410925)
      ·
        refine ⟨19593778915636710070279097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52250077108364560187410925 19593778915636710070279097)
        ·
          refine ⟨14695334186727532552709323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19593778915636710070279097 14695334186727532552709323)
          ·
            refine ⟨22043001280091298829063985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14695334186727532552709323 22043001280091298829063985)
            ·
              refine ⟨16532250960068474121797989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22043001280091298829063985 16532250960068474121797989)
              ·
                refine ⟨3099797055012838897837123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16532250960068474121797989 3099797055012838897837123)
                ·
                  refine ⟨4649695582519258346755685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099797055012838897837123 4649695582519258346755685)
                  ·
                    refine ⟨871817921722360940016691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4649695582519258346755685 871817921722360940016691)
                    ·
                      rfl

theorem cell22_2546789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_2546789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546789 prefixEnd_2546789 := by exact prefixLift 2546789
  have htrace : WordTrace (prefixWord ++ tailWord_2546789) baseStart_2546789 baseEnd_2546789 := by
    simpa [prefixWord, tailWord_2546789, baseEnd_2546789] using wordTrace_append hprefix tailTrace_2546789
  have hstable : (prefixWord ++ tailWord_2546789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546789).length < 2 ^ (prefixWord ++ tailWord_2546789).sum := by decide
  have hdescent : baseEnd_2546789 < baseStart_2546789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546806 : List Nat := [5, 1, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_2546806 : Nat := 118140960795 + 2546806 * 2 ^ 59
def prefixEnd_2546806 : Nat := 4983230072969 + 3 ^ 40 * 2546806 * 2
def baseEnd_2546806 : Nat := 871823741169778562341639

theorem tailTrace_2546806 : CollatzResearch.WordTrace tailWord_2546806 prefixEnd_2546806 871823741169778562341639 := by
  unfold tailWord_2546806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5805602875710268542561767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61926430674242864453992181 5805602875710268542561767)
  ·
    refine ⟨8708404313565402813842651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5805602875710268542561767 8708404313565402813842651)
    ·
      refine ⟨13062606470348104220763977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8708404313565402813842651 13062606470348104220763977)
      ·
        refine ⟨9796954852761078165572983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13062606470348104220763977 9796954852761078165572983)
        ·
          refine ⟨14695432279141617248359475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9796954852761078165572983 14695432279141617248359475)
          ·
            refine ⟨22043148418712425872539213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14695432279141617248359475 22043148418712425872539213)
            ·
              refine ⟨8266180657017159702202205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22043148418712425872539213 8266180657017159702202205)
              ·
                refine ⟨3099817746381434888325827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8266180657017159702202205 3099817746381434888325827)
                ·
                  refine ⟨4649726619572152332488741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099817746381434888325827 4649726619572152332488741)
                  ·
                    refine ⟨871823741169778562341639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4649726619572152332488741 871823741169778562341639)
                    ·
                      rfl

theorem cell22_2546806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_2546806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546806 prefixEnd_2546806 := by exact prefixLift 2546806
  have htrace : WordTrace (prefixWord ++ tailWord_2546806) baseStart_2546806 baseEnd_2546806 := by
    simpa [prefixWord, tailWord_2546806, baseEnd_2546806] using wordTrace_append hprefix tailTrace_2546806
  have hstable : (prefixWord ++ tailWord_2546806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546806).length < 2 ^ (prefixWord ++ tailWord_2546806).sum := by decide
  have hdescent : baseEnd_2546806 < baseStart_2546806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546819 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 4, 3]
def baseStart_2546819 : Nat := 118140960795 + 2546819 * 2 ^ 59
def prefixEnd_2546819 : Nat := 4983230072969 + 3 ^ 40 * 2546819 * 2
def baseEnd_2546819 : Nat := 871828191335450861766599

theorem tailTrace_2546819 : CollatzResearch.WordTrace tailWord_2546819 prefixEnd_2546819 871828191335450861766599 := by
  unfold tailWord_2546819
  simp only [CollatzResearch.WordTrace]
  refine ⟨92890120160317199901211511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61926746773544799934141007 92890120160317199901211511)
  ·
    refine ⟨139335180240475799851817267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92890120160317199901211511 139335180240475799851817267)
    ·
      refine ⟨209002770360713699777725901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139335180240475799851817267 209002770360713699777725901)
      ·
        refine ⟨78376038885267637416647213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209002770360713699777725901 78376038885267637416647213)
        ·
          refine ⟨29391014581975364031242705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78376038885267637416647213 29391014581975364031242705)
          ·
            refine ⟨22043260936481523023432029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29391014581975364031242705 22043260936481523023432029)
            ·
              refine ⟨8266222851180571133787011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22043260936481523023432029 8266222851180571133787011)
              ·
                refine ⟨12399334276770856700680517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8266222851180571133787011 12399334276770856700680517)
                ·
                  refine ⟨2324875176894535631377597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12399334276770856700680517 2324875176894535631377597)
                  ·
                    refine ⟨871828191335450861766599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2324875176894535631377597 871828191335450861766599)
                    ·
                      rfl

theorem cell22_2546819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 3].length) (baseStart_2546819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546819 prefixEnd_2546819 := by exact prefixLift 2546819
  have htrace : WordTrace (prefixWord ++ tailWord_2546819) baseStart_2546819 baseEnd_2546819 := by
    simpa [prefixWord, tailWord_2546819, baseEnd_2546819] using wordTrace_append hprefix tailTrace_2546819
  have hstable : (prefixWord ++ tailWord_2546819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546819).length < 2 ^ (prefixWord ++ tailWord_2546819).sum := by decide
  have hdescent : baseEnd_2546819 < baseStart_2546819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546834 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2546834 : Nat := 118140960795 + 2546834 * 2 ^ 59
def prefixEnd_2546834 : Nat := 4983230072969 + 3 ^ 40 * 2546834 * 2
def baseEnd_2546834 : Nat := 871833326141995822641553

theorem tailTrace_2546834 : CollatzResearch.WordTrace tailWord_2546834 prefixEnd_2546834 871833326141995822641553 := by
  unfold tailWord_2546834
  simp only [CollatzResearch.WordTrace]
  refine ⟨23222666813815714365751889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61927111503508571642005037 23222666813815714365751889)
  ·
    refine ⟨17417000110361785774313917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23222666813815714365751889 17417000110361785774313917)
    ·
      refine ⟨6531375041385669665367719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17417000110361785774313917 6531375041385669665367719)
      ·
        refine ⟨9797062562078504498051579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6531375041385669665367719 9797062562078504498051579)
        ·
          refine ⟨14695593843117756747077369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9797062562078504498051579 14695593843117756747077369)
          ·
            refine ⟨11021695382338317560308027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14695593843117756747077369 11021695382338317560308027)
            ·
              refine ⟨16532543073507476340462041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11021695382338317560308027 16532543073507476340462041)
              ·
                refine ⟨12399407305130607255346531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16532543073507476340462041 12399407305130607255346531)
                ·
                  refine ⟨18599110957695910883019797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12399407305130607255346531 18599110957695910883019797)
                  ·
                    refine ⟨871833326141995822641553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18599110957695910883019797 871833326141995822641553)
                    ·
                      rfl

theorem cell22_2546834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2546834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546834 prefixEnd_2546834 := by exact prefixLift 2546834
  have htrace : WordTrace (prefixWord ++ tailWord_2546834) baseStart_2546834 baseEnd_2546834 := by
    simpa [prefixWord, tailWord_2546834, baseEnd_2546834] using wordTrace_append hprefix tailTrace_2546834
  have hstable : (prefixWord ++ tailWord_2546834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546834).length < 2 ^ (prefixWord ++ tailWord_2546834).sum := by decide
  have hdescent : baseEnd_2546834 < baseStart_2546834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546973 : List Nat := [1, 4, 2, 3, 1, 1, 1, 5, 4]
def baseStart_2546973 : Nat := 118140960795 + 2546973 * 2 ^ 59
def prefixEnd_2546973 : Nat := 4983230072969 + 3 ^ 40 * 2546973 * 2
def baseEnd_2546973 : Nat := 290626969560881931138709

theorem tailTrace_2546973 : CollatzResearch.WordTrace tailWord_2546973 prefixEnd_2546973 290626969560881931138709 := by
  unfold tailWord_2546973
  simp only [CollatzResearch.WordTrace]
  refine ⟨92895737001759284202317573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61930491334506189468211715 92895737001759284202317573)
  ·
    refine ⟨17417950687829865787934545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92895737001759284202317573 17417950687829865787934545)
    ·
      refine ⟨13063463015872399340950909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17417950687829865787934545 13063463015872399340950909)
      ·
        refine ⟨4898798630952149752856591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13063463015872399340950909 4898798630952149752856591)
        ·
          refine ⟨7348197946428224629284887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4898798630952149752856591 7348197946428224629284887)
          ·
            refine ⟨11022296919642336943927331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7348197946428224629284887 11022296919642336943927331)
            ·
              refine ⟨16533445379463505415890997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11022296919642336943927331 16533445379463505415890997)
              ·
                refine ⟨1550010504324703632739781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16533445379463505415890997 1550010504324703632739781)
                ·
                  refine ⟨290626969560881931138709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550010504324703632739781 290626969560881931138709)
                  ·
                    rfl

theorem cell22_2546973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_2546973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546973 prefixEnd_2546973 := by exact prefixLift 2546973
  have htrace : WordTrace (prefixWord ++ tailWord_2546973) baseStart_2546973 baseEnd_2546973 := by
    simpa [prefixWord, tailWord_2546973, baseEnd_2546973] using wordTrace_append hprefix tailTrace_2546973
  have hstable : (prefixWord ++ tailWord_2546973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546973).length < 2 ^ (prefixWord ++ tailWord_2546973).sum := by decide
  have hdescent : baseEnd_2546973 < baseStart_2546973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546975 : List Nat := [1, 1, 2, 4, 4, 2, 2, 1, 1, 4]
def baseStart_2546975 : Nat := 118140960795 + 2546975 * 2 ^ 59
def prefixEnd_2546975 : Nat := 4983230072969 + 3 ^ 40 * 2546975 * 2
def baseEnd_2546975 : Nat := 871881593323518454866121

theorem tailTrace_2546975 : CollatzResearch.WordTrace tailWord_2546975 prefixEnd_2546975 871881593323518454866121 := by
  unfold tailWord_2546975
  simp only [CollatzResearch.WordTrace]
  refine ⟨92895809947752038543890379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61930539965168025695926919 92895809947752038543890379)
  ·
    refine ⟨139343714921628057815835569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92895809947752038543890379 139343714921628057815835569)
    ·
      refine ⟨104507786191221043361876677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139343714921628057815835569 104507786191221043361876677)
      ·
        refine ⟨19595209910853945630351877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104507786191221043361876677 19595209910853945630351877)
        ·
          refine ⟨3674101858285114805690977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19595209910853945630351877 3674101858285114805690977)
          ·
            refine ⟨2755576393713836104268233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3674101858285114805690977 2755576393713836104268233)
            ·
              refine ⟨2066682295285377078201175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2755576393713836104268233 2066682295285377078201175)
              ·
                refine ⟨3100023442928065617301763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066682295285377078201175 3100023442928065617301763)
                ·
                  refine ⟨4650035164392098425952645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100023442928065617301763 4650035164392098425952645)
                  ·
                    refine ⟨871881593323518454866121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4650035164392098425952645 871881593323518454866121)
                    ·
                      rfl

theorem cell22_2546975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 1, 4].length) (baseStart_2546975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2546975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2546975 prefixEnd_2546975 := by exact prefixLift 2546975
  have htrace : WordTrace (prefixWord ++ tailWord_2546975) baseStart_2546975 baseEnd_2546975 := by
    simpa [prefixWord, tailWord_2546975, baseEnd_2546975] using wordTrace_append hprefix tailTrace_2546975
  have hstable : (prefixWord ++ tailWord_2546975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546975).length < 2 ^ (prefixWord ++ tailWord_2546975).sum := by decide
  have hdescent : baseEnd_2546975 < baseStart_2546975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547005 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 1, 5]
def baseStart_2547005 : Nat := 118140960795 + 2547005 * 2 ^ 59
def prefixEnd_2547005 : Nat := 4983230072969 + 3 ^ 40 * 2547005 * 2
def baseEnd_2547005 : Nat := 871891862936608376616029

theorem tailTrace_2547005 : CollatzResearch.WordTrace tailWord_2547005 prefixEnd_2547005 871891862936608376616029 := by
  unfold tailWord_2547005
  simp only [CollatzResearch.WordTrace]
  refine ⟨92896904137643353667482469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61931269425095569111654979 92896904137643353667482469)
  ·
    refine ⟨17418169525808128812652963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92896904137643353667482469 17418169525808128812652963)
    ·
      refine ⟨26127254288712193218979445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17418169525808128812652963 26127254288712193218979445)
      ·
        refine ⟨2449430089566768114279323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26127254288712193218979445 2449430089566768114279323)
        ·
          refine ⟨3674145134350152171418985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2449430089566768114279323 3674145134350152171418985)
          ·
            refine ⟨2755608850762614128564239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3674145134350152171418985 2755608850762614128564239)
            ·
              refine ⟨4133413276143921192846359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2755608850762614128564239 4133413276143921192846359)
              ·
                refine ⟨6200119914215881789269539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4133413276143921192846359 6200119914215881789269539)
                ·
                  refine ⟨9300179871323822683904309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6200119914215881789269539 9300179871323822683904309)
                  ·
                    refine ⟨871891862936608376616029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9300179871323822683904309 871891862936608376616029)
                    ·
                      rfl

theorem cell22_2547005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_2547005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547005 prefixEnd_2547005 := by exact prefixLift 2547005
  have htrace : WordTrace (prefixWord ++ tailWord_2547005) baseStart_2547005 baseEnd_2547005 := by
    simpa [prefixWord, tailWord_2547005, baseEnd_2547005] using wordTrace_append hprefix tailTrace_2547005
  have hstable : (prefixWord ++ tailWord_2547005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547005).length < 2 ^ (prefixWord ++ tailWord_2547005).sum := by decide
  have hdescent : baseEnd_2547005 < baseStart_2547005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547037 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 2, 4]
def baseStart_2547037 : Nat := 118140960795 + 2547037 * 2 ^ 59
def prefixEnd_2547037 : Nat := 4983230072969 + 3 ^ 40 * 2547037 * 2
def baseEnd_2547037 : Nat := 871902817190570959815931

theorem tailTrace_2547037 : CollatzResearch.WordTrace tailWord_2547037 prefixEnd_2547037 871902817190570959815931 := by
  unfold tailWord_2547037
  simp only [CollatzResearch.WordTrace]
  refine ⟨92898071273527423132647365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61932047515684948755098243 92898071273527423132647365)
  ·
    refine ⟨17418388363786391837371381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92898071273527423132647365 17418388363786391837371381)
    ·
      refine ⟨1632973909104974234753567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17418388363786391837371381 1632973909104974234753567)
      ·
        refine ⟨2449460863657461352130351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1632973909104974234753567 2449460863657461352130351)
        ·
          refine ⟨3674191295486192028195527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2449460863657461352130351 3674191295486192028195527)
          ·
            refine ⟨5511286943229288042293291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674191295486192028195527 5511286943229288042293291)
            ·
              refine ⟨8266930414843932063439937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5511286943229288042293291 8266930414843932063439937)
              ·
                refine ⟨6200197811132949047579953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8266930414843932063439937 6200197811132949047579953)
                ·
                  refine ⟨4650148358349711785684965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6200197811132949047579953 4650148358349711785684965)
                  ·
                    refine ⟨871902817190570959815931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4650148358349711785684965 871902817190570959815931)
                    ·
                      rfl

theorem cell22_2547037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_2547037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547037 prefixEnd_2547037 := by exact prefixLift 2547037
  have htrace : WordTrace (prefixWord ++ tailWord_2547037) baseStart_2547037 baseEnd_2547037 := by
    simpa [prefixWord, tailWord_2547037, baseEnd_2547037] using wordTrace_append hprefix tailTrace_2547037
  have hstable : (prefixWord ++ tailWord_2547037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547037).length < 2 ^ (prefixWord ++ tailWord_2547037).sum := by decide
  have hdescent : baseEnd_2547037 < baseStart_2547037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547121 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 1, 6]
def baseStart_2547121 : Nat := 118140960795 + 2547121 * 2 ^ 59
def prefixEnd_2547121 : Nat := 4983230072969 + 3 ^ 40 * 2547121 * 2
def baseEnd_2547121 : Nat := 871931572107222740715673

theorem tailTrace_2547121 : CollatzResearch.WordTrace tailWord_2547121 prefixEnd_2547121 871931572107222740715673 := by
  unfold tailWord_2547121
  simp only [CollatzResearch.WordTrace]
  refine ⟨92901135005223105478705217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61934090003482070319136811 92901135005223105478705217)
  ·
    refine ⟨69675851253917329109028913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92901135005223105478705217 69675851253917329109028913)
    ·
      refine ⟨52256888440437996831771685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69675851253917329109028913 52256888440437996831771685)
      ·
        refine ⟨9798166582582124405957191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52256888440437996831771685 9798166582582124405957191)
        ·
          refine ⟨14697249873873186608935787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9798166582582124405957191 14697249873873186608935787)
          ·
            refine ⟨22045874810809779913403681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14697249873873186608935787 22045874810809779913403681)
            ·
              refine ⟨16534406108107334935052761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22045874810809779913403681 16534406108107334935052761)
              ·
                refine ⟨12400804581080501201289571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16534406108107334935052761 12400804581080501201289571)
                ·
                  refine ⟨18601206871620751801934357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12400804581080501201289571 18601206871620751801934357)
                  ·
                    refine ⟨871931572107222740715673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18601206871620751801934357 871931572107222740715673)
                    ·
                      rfl

theorem cell22_2547121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_2547121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547121 prefixEnd_2547121 := by exact prefixLift 2547121
  have htrace : WordTrace (prefixWord ++ tailWord_2547121) baseStart_2547121 baseEnd_2547121 := by
    simpa [prefixWord, tailWord_2547121, baseEnd_2547121] using wordTrace_append hprefix tailTrace_2547121
  have hstable : (prefixWord ++ tailWord_2547121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547121).length < 2 ^ (prefixWord ++ tailWord_2547121).sum := by decide
  have hdescent : baseEnd_2547121 < baseStart_2547121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547196 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 1, 7]
def baseStart_2547196 : Nat := 118140960795 + 2547196 * 2 ^ 59
def prefixEnd_2547196 : Nat := 4983230072969 + 3 ^ 40 * 2547196 * 2
def baseEnd_2547196 : Nat := 871957246139947545090443

theorem tailTrace_2547196 : CollatzResearch.WordTrace tailWord_2547196 prefixEnd_2547196 871957246139947545090443 := by
  unfold tailWord_2547196
  simp only [CollatzResearch.WordTrace]
  refine ⟨46451935239975696643842721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61935913653300928858456961 46451935239975696643842721)
  ·
    refine ⟨34838951429981772482882041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46451935239975696643842721 34838951429981772482882041)
    ·
      refine ⟨26129213572486329362161531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34838951429981772482882041 26129213572486329362161531)
      ·
        refine ⟨39193820358729494043242297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26129213572486329362161531 39193820358729494043242297)
        ·
          refine ⟨29395365269047120532431723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39193820358729494043242297 29395365269047120532431723)
          ·
            refine ⟨44093047903570680798647585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29395365269047120532431723 44093047903570680798647585)
            ·
              refine ⟨33069785927678010598985689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44093047903570680798647585 33069785927678010598985689)
              ·
                refine ⟨24802339445758507949239267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33069785927678010598985689 24802339445758507949239267)
                ·
                  refine ⟨37203509168637761923858901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24802339445758507949239267 37203509168637761923858901)
                  ·
                    refine ⟨871957246139947545090443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37203509168637761923858901 871957246139947545090443)
                    ·
                      rfl

theorem cell22_2547196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_2547196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547196 prefixEnd_2547196 := by exact prefixLift 2547196
  have htrace : WordTrace (prefixWord ++ tailWord_2547196) baseStart_2547196 baseEnd_2547196 := by
    simpa [prefixWord, tailWord_2547196, baseEnd_2547196] using wordTrace_append hprefix tailTrace_2547196
  have hstable : (prefixWord ++ tailWord_2547196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547196).length < 2 ^ (prefixWord ++ tailWord_2547196).sum := by decide
  have hdescent : baseEnd_2547196 < baseStart_2547196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547228 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 3, 4]
def baseStart_2547228 : Nat := 118140960795 + 2547228 * 2 ^ 59
def prefixEnd_2547228 : Nat := 4983230072969 + 3 ^ 40 * 2547228 * 2
def baseEnd_2547228 : Nat := 871968200393910128290345

theorem tailTrace_2547228 : CollatzResearch.WordTrace tailWord_2547228 prefixEnd_2547228 871968200393910128290345 := by
  unfold tailWord_2547228
  simp only [CollatzResearch.WordTrace]
  refine ⟨46452518807917731376425169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61936691743890308501900225 46452518807917731376425169)
  ·
    refine ⟨34839389105938298532318877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46452518807917731376425169 34839389105938298532318877)
    ·
      refine ⟨13064770914726861949619579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34839389105938298532318877 13064770914726861949619579)
      ·
        refine ⟨19597156372090292924429369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13064770914726861949619579 19597156372090292924429369)
        ·
          refine ⟨14697867279067719693322027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19597156372090292924429369 14697867279067719693322027)
          ·
            refine ⟨22046800918601579539983041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14697867279067719693322027 22046800918601579539983041)
            ·
              refine ⟨16535100688951184654987281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22046800918601579539983041 16535100688951184654987281)
              ·
                refine ⟨12401325516713388491240461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16535100688951184654987281 12401325516713388491240461)
                ·
                  refine ⟨4650497068767520684215173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12401325516713388491240461 4650497068767520684215173)
                  ·
                    refine ⟨871968200393910128290345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4650497068767520684215173 871968200393910128290345)
                    ·
                      rfl

theorem cell22_2547228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_2547228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547228 prefixEnd_2547228 := by exact prefixLift 2547228
  have htrace : WordTrace (prefixWord ++ tailWord_2547228) baseStart_2547228 baseEnd_2547228 := by
    simpa [prefixWord, tailWord_2547228, baseEnd_2547228] using wordTrace_append hprefix tailTrace_2547228
  have hstable : (prefixWord ++ tailWord_2547228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547228).length < 2 ^ (prefixWord ++ tailWord_2547228).sum := by decide
  have hdescent : baseEnd_2547228 < baseStart_2547228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547232 : List Nat := [2, 1, 1, 6, 1, 3, 2, 1, 5]
def baseStart_2547232 : Nat := 118140960795 + 2547232 * 2 ^ 59
def prefixEnd_2547232 : Nat := 4983230072969 + 3 ^ 40 * 2547232 * 2
def baseEnd_2547232 : Nat := 290656523225218483730111

theorem tailTrace_2547232 : CollatzResearch.WordTrace tailWord_2547232 prefixEnd_2547232 290656523225218483730111 := by
  unfold tailWord_2547232
  simp only [CollatzResearch.WordTrace]
  refine ⟨46452591753910485717997975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61936789005213980957330633 46452591753910485717997975)
  ·
    refine ⟨69678887630865728576996963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46452591753910485717997975 69678887630865728576996963)
    ·
      refine ⟨104518331446298592865495445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69678887630865728576996963 104518331446298592865495445)
      ·
        refine ⟨4899296786545246540570099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 104518331446298592865495445 4899296786545246540570099)
        ·
          refine ⟨7348945179817869810855149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4899296786545246540570099 7348945179817869810855149)
          ·
            refine ⟨2755854442431701179070681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7348945179817869810855149 2755854442431701179070681)
            ·
              refine ⟨2066890831823775884303011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2755854442431701179070681 2066890831823775884303011)
              ·
                refine ⟨3100336247735663826454517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066890831823775884303011 3100336247735663826454517)
                ·
                  refine ⟨290656523225218483730111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3100336247735663826454517 290656523225218483730111)
                  ·
                    rfl

theorem cell22_2547232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 5].length) (baseStart_2547232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547232 prefixEnd_2547232 := by exact prefixLift 2547232
  have htrace : WordTrace (prefixWord ++ tailWord_2547232) baseStart_2547232 baseEnd_2547232 := by
    simpa [prefixWord, tailWord_2547232, baseEnd_2547232] using wordTrace_append hprefix tailTrace_2547232
  have hstable : (prefixWord ++ tailWord_2547232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547232).length < 2 ^ (prefixWord ++ tailWord_2547232).sum := by decide
  have hdescent : baseEnd_2547232 < baseStart_2547232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547258 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 1, 5]
def baseStart_2547258 : Nat := 118140960795 + 2547258 * 2 ^ 59
def prefixEnd_2547258 : Nat := 4983230072969 + 3 ^ 40 * 2547258 * 2
def baseEnd_2547258 : Nat := 871978470007000050040253

theorem tailTrace_2547258 : CollatzResearch.WordTrace tailWord_2547258 prefixEnd_2547258 871978470007000050040253 := by
  unfold tailWord_2547258
  simp only [CollatzResearch.WordTrace]
  refine ⟨23226532951431694469110607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61937421203817851917628285 23226532951431694469110607)
  ·
    refine ⟨34839799427147541703665911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23226532951431694469110607 34839799427147541703665911)
    ·
      refine ⟨52259699140721312555498867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34839799427147541703665911 52259699140721312555498867)
      ·
        refine ⟨78389548711081968833248301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52259699140721312555498867 78389548711081968833248301)
        ·
          refine ⟨29396080766655738312468113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78389548711081968833248301 29396080766655738312468113)
          ·
            refine ⟨22047060574991803734351085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29396080766655738312468113 22047060574991803734351085)
            ·
              refine ⟨8267647715621926400381657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22047060574991803734351085 8267647715621926400381657)
              ·
                refine ⟨6200735786716444800286243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8267647715621926400381657 6200735786716444800286243)
                ·
                  refine ⟨9301103680074667200429365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6200735786716444800286243 9301103680074667200429365)
                  ·
                    refine ⟨871978470007000050040253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9301103680074667200429365 871978470007000050040253)
                    ·
                      rfl

theorem cell22_2547258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_2547258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547258 prefixEnd_2547258 := by exact prefixLift 2547258
  have htrace : WordTrace (prefixWord ++ tailWord_2547258) baseStart_2547258 baseEnd_2547258 := by
    simpa [prefixWord, tailWord_2547258, baseEnd_2547258] using wordTrace_append hprefix tailTrace_2547258
  have hstable : (prefixWord ++ tailWord_2547258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547258).length < 2 ^ (prefixWord ++ tailWord_2547258).sum := by decide
  have hdescent : baseEnd_2547258 < baseStart_2547258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547270 : List Nat := [6, 1, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_2547270 : Nat := 118140960795 + 2547270 * 2 ^ 59
def prefixEnd_2547270 : Nat := 4983230072969 + 3 ^ 40 * 2547270 * 2
def baseEnd_2547270 : Nat := 871982577852236018740217

theorem tailTrace_2547270 : CollatzResearch.WordTrace tailWord_2547270 prefixEnd_2547270 871982577852236018740217 := by
  unfold tailWord_2547270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2903330296302603247683727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61937712987788869283919509 2903330296302603247683727)
  ·
    refine ⟨4354995444453904871525591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2903330296302603247683727 4354995444453904871525591)
    ·
      refine ⟨6532493166680857307288387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4354995444453904871525591 6532493166680857307288387)
      ·
        refine ⟨9798739750021285960932581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6532493166680857307288387 9798739750021285960932581)
        ·
          refine ⟨1837263703128991117674859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9798739750021285960932581 1837263703128991117674859)
          ·
            refine ⟨2755895554693486676512289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837263703128991117674859 2755895554693486676512289)
            ·
              refine ⟨2066921666020115007384217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2755895554693486676512289 2066921666020115007384217)
              ·
                refine ⟨1550191249515086255538163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2066921666020115007384217 1550191249515086255538163)
                ·
                  refine ⟨2325286874272629383307245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550191249515086255538163 2325286874272629383307245)
                  ·
                    refine ⟨871982577852236018740217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2325286874272629383307245 871982577852236018740217)
                    ·
                      rfl

theorem cell22_2547270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_2547270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547270 prefixEnd_2547270 := by exact prefixLift 2547270
  have htrace : WordTrace (prefixWord ++ tailWord_2547270) baseStart_2547270 baseEnd_2547270 := by
    simpa [prefixWord, tailWord_2547270, baseEnd_2547270] using wordTrace_append hprefix tailTrace_2547270
  have hstable : (prefixWord ++ tailWord_2547270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547270).length < 2 ^ (prefixWord ++ tailWord_2547270).sum := by decide
  have hdescent : baseEnd_2547270 < baseStart_2547270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547271 : List Nat := [1, 1, 4, 1, 15]
def baseStart_2547271 : Nat := 118140960795 + 2547271 * 2 ^ 59
def prefixEnd_2547271 : Nat := 4983230072969 + 3 ^ 40 * 2547271 * 2
def baseEnd_2547271 : Nat := 3588407078899886211791

theorem tailTrace_2547271 : CollatzResearch.WordTrace tailWord_2547271 prefixEnd_2547271 3588407078899886211791 := by
  unfold tailWord_2547271
  simp only [CollatzResearch.WordTrace]
  refine ⟨92906605954679681096665667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61937737303119787397777111 92906605954679681096665667)
  ·
    refine ⟨139359908932019521644998501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92906605954679681096665667 139359908932019521644998501)
    ·
      refine ⟨26129982924753660308437219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139359908932019521644998501 26129982924753660308437219)
      ·
        refine ⟨39194974387130490462655829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26129982924753660308437219 39194974387130490462655829)
        ·
          refine ⟨3588407078899886211791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 39194974387130490462655829 3588407078899886211791)
          ·
            rfl

theorem cell22_2547271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 15].length) (baseStart_2547271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547271 prefixEnd_2547271 := by exact prefixLift 2547271
  have htrace : WordTrace (prefixWord ++ tailWord_2547271) baseStart_2547271 baseEnd_2547271 := by
    simpa [prefixWord, tailWord_2547271, baseEnd_2547271] using wordTrace_append hprefix tailTrace_2547271
  have hstable : (prefixWord ++ tailWord_2547271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547271).length < 2 ^ (prefixWord ++ tailWord_2547271).sum := by decide
  have hdescent : baseEnd_2547271 < baseStart_2547271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547292 : List Nat := [2, 2, 4, 1, 2, 1, 2, 3, 2, 3]
def baseStart_2547292 : Nat := 118140960795 + 2547292 * 2 ^ 59
def prefixEnd_2547292 : Nat := 4983230072969 + 3 ^ 40 * 2547292 * 2
def baseEnd_2547292 : Nat := 871990108901835294690149

theorem tailTrace_2547292 : CollatzResearch.WordTrace tailWord_2547292 prefixEnd_2547292 871990108901835294690149 := by
  unfold tailWord_2547292
  simp only [CollatzResearch.WordTrace]
  refine ⟨46453685943801800841590065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61938247925069067788786753 46453685943801800841590065)
  ·
    refine ⟨34840264457851350631192549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46453685943801800841590065 34840264457851350631192549)
    ·
      refine ⟨6532549585847128243348603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34840264457851350631192549 6532549585847128243348603)
      ·
        refine ⟨9798824378770692365022905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6532549585847128243348603 9798824378770692365022905)
        ·
          refine ⟨7349118284078019273767179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9798824378770692365022905 7349118284078019273767179)
          ·
            refine ⟨11023677426117028910650769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7349118284078019273767179 11023677426117028910650769)
            ·
              refine ⟨8267758069587771682988077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11023677426117028910650769 8267758069587771682988077)
              ·
                refine ⟨3100409276095414381120529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8267758069587771682988077 3100409276095414381120529)
                ·
                  refine ⟨2325306957071560785840397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3100409276095414381120529 2325306957071560785840397)
                  ·
                    refine ⟨871990108901835294690149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2325306957071560785840397 871990108901835294690149)
                    ·
                      rfl

theorem cell22_2547292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_2547292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547292 prefixEnd_2547292 := by exact prefixLift 2547292
  have htrace : WordTrace (prefixWord ++ tailWord_2547292) baseStart_2547292 baseEnd_2547292 := by
    simpa [prefixWord, tailWord_2547292, baseEnd_2547292] using wordTrace_append hprefix tailTrace_2547292
  have hstable : (prefixWord ++ tailWord_2547292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547292).length < 2 ^ (prefixWord ++ tailWord_2547292).sum := by decide
  have hdescent : baseEnd_2547292 < baseStart_2547292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547333 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 7]
def baseStart_2547333 : Nat := 118140960795 + 2547333 * 2 ^ 59
def prefixEnd_2547333 : Nat := 4983230072969 + 3 ^ 40 * 2547333 * 2
def baseEnd_2547333 : Nat := 290668048013241618138341

theorem tailTrace_2547333 : CollatzResearch.WordTrace tailWord_2547333 prefixEnd_2547333 290668048013241618138341 := by
  unfold tailWord_2547333
  simp only [CollatzResearch.WordTrace]
  refine ⟨92908867280455065685422653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61939244853636710456948435 92908867280455065685422653)
  ·
    refine ⟨34840825230170649632033495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92908867280455065685422653 34840825230170649632033495)
    ·
      refine ⟨52261237845255974448050243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34840825230170649632033495 52261237845255974448050243)
      ·
        refine ⟨78391856767883961672075365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52261237845255974448050243 78391856767883961672075365)
        ·
          refine ⟨14698473143978242813514131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78391856767883961672075365 14698473143978242813514131)
          ·
            refine ⟨22047709715967364220271197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14698473143978242813514131 22047709715967364220271197)
            ·
              refine ⟨8267891143487761582601699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22047709715967364220271197 8267891143487761582601699)
              ·
                refine ⟨12401836715231642373902549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8267891143487761582601699 12401836715231642373902549)
                ·
                  refine ⟨290668048013241618138341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12401836715231642373902549 290668048013241618138341)
                  ·
                    rfl

theorem cell22_2547333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_2547333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547333 prefixEnd_2547333 := by exact prefixLift 2547333
  have htrace : WordTrace (prefixWord ++ tailWord_2547333) baseStart_2547333 baseEnd_2547333 := by
    simpa [prefixWord, tailWord_2547333, baseEnd_2547333] using wordTrace_append hprefix tailTrace_2547333
  have hstable : (prefixWord ++ tailWord_2547333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547333).length < 2 ^ (prefixWord ++ tailWord_2547333).sum := by decide
  have hdescent : baseEnd_2547333 < baseStart_2547333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547337 : List Nat := [1, 2, 1, 1, 4, 1, 4, 4, 1, 3]
def baseStart_2547337 : Nat := 118140960795 + 2547337 * 2 ^ 59
def prefixEnd_2547337 : Nat := 4983230072969 + 3 ^ 40 * 2547337 * 2
def baseEnd_2547337 : Nat := 872005513321470177315011

theorem tailTrace_2547337 : CollatzResearch.WordTrace tailWord_2547337 prefixEnd_2547337 872005513321470177315011 := by
  unfold tailWord_2547337
  simp only [CollatzResearch.WordTrace]
  refine ⟨92909013172440574368568265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61939342114960382912378843 92909013172440574368568265)
  ·
    refine ⟨69681759879330430776426199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92909013172440574368568265 69681759879330430776426199)
    ·
      refine ⟨104522639818995646164639299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69681759879330430776426199 104522639818995646164639299)
      ·
        refine ⟨156783959728493469246958949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104522639818995646164639299 156783959728493469246958949)
        ·
          refine ⟨29396992449092525483804803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156783959728493469246958949 29396992449092525483804803)
          ·
            refine ⟨44095488673638788225707205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29396992449092525483804803 44095488673638788225707205)
            ·
              refine ⟨8267904126307272792320101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44095488673638788225707205 8267904126307272792320101)
              ·
                refine ⟨1550232023682613648560019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8267904126307272792320101 1550232023682613648560019)
                ·
                  refine ⟨2325348035523920472840029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550232023682613648560019 2325348035523920472840029)
                  ·
                    refine ⟨872005513321470177315011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2325348035523920472840029 872005513321470177315011)
                    ·
                      rfl

theorem cell22_2547337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 1, 3].length) (baseStart_2547337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547337 prefixEnd_2547337 := by exact prefixLift 2547337
  have htrace : WordTrace (prefixWord ++ tailWord_2547337) baseStart_2547337 baseEnd_2547337 := by
    simpa [prefixWord, tailWord_2547337, baseEnd_2547337] using wordTrace_append hprefix tailTrace_2547337
  have hstable : (prefixWord ++ tailWord_2547337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547337).length < 2 ^ (prefixWord ++ tailWord_2547337).sum := by decide
  have hdescent : baseEnd_2547337 < baseStart_2547337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547378 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 8]
def baseStart_2547378 : Nat := 118140960795 + 2547378 * 2 ^ 59
def prefixEnd_2547378 : Nat := 4983230072969 + 3 ^ 40 * 2547378 * 2
def baseEnd_2547378 : Nat := 290673182819786579013295

theorem tailTrace_2547378 : CollatzResearch.WordTrace tailWord_2547378 prefixEnd_2547378 290673182819786579013295 := by
  unfold tailWord_2547378
  simp only [CollatzResearch.WordTrace]
  refine ⟨23227627141323009592702697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61940339043528025580540525 23227627141323009592702697)
  ·
    refine ⟨17420720355992257194527023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23227627141323009592702697 17420720355992257194527023)
    ·
      refine ⟨26131080533988385791790535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17420720355992257194527023 26131080533988385791790535)
      ·
        refine ⟨39196620800982578687685803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26131080533988385791790535 39196620800982578687685803)
        ·
          refine ⟨58794931201473868031528705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39196620800982578687685803 58794931201473868031528705)
          ·
            refine ⟨44096198401105401023646529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58794931201473868031528705 44096198401105401023646529)
            ·
              refine ⟨33072148800829050767734897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44096198401105401023646529 33072148800829050767734897)
              ·
                refine ⟨24804111600621788075801173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33072148800829050767734897 24804111600621788075801173)
                ·
                  refine ⟨290673182819786579013295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24804111600621788075801173 290673182819786579013295)
                  ·
                    rfl

theorem cell22_2547378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_2547378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547378 prefixEnd_2547378 := by exact prefixLift 2547378
  have htrace : WordTrace (prefixWord ++ tailWord_2547378) baseStart_2547378 baseEnd_2547378 := by
    simpa [prefixWord, tailWord_2547378, baseEnd_2547378] using wordTrace_append hprefix tailTrace_2547378
  have hstable : (prefixWord ++ tailWord_2547378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547378).length < 2 ^ (prefixWord ++ tailWord_2547378).sum := by decide
  have hdescent : baseEnd_2547378 < baseStart_2547378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547408 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 1, 6]
def baseStart_2547408 : Nat := 118140960795 + 2547408 * 2 ^ 59
def prefixEnd_2547408 : Nat := 4983230072969 + 3 ^ 40 * 2547408 * 2
def baseEnd_2547408 : Nat := 872029818072449658789793

theorem tailTrace_2547408 : CollatzResearch.WordTrace tailWord_2547408 prefixEnd_2547408 872029818072449658789793 := by
  unfold tailWord_2547408
  simp only [CollatzResearch.WordTrace]
  refine ⟨46455801377591676747201439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61941068503455568996268585 46455801377591676747201439)
  ·
    refine ⟨69683702066387515120802159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46455801377591676747201439 69683702066387515120802159)
    ·
      refine ⟨104525553099581272681203239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69683702066387515120802159 104525553099581272681203239)
      ·
        refine ⟨156788329649371909021804859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104525553099581272681203239 156788329649371909021804859)
        ·
          refine ⟨235182494474057863532707289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156788329649371909021804859 235182494474057863532707289)
          ·
            refine ⟨176386870855543397649530467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235182494474057863532707289 176386870855543397649530467)
            ·
              refine ⟨264580306283315096474295701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176386870855543397649530467 264580306283315096474295701)
              ·
                refine ⟨12402201857030395147232611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 264580306283315096474295701 12402201857030395147232611)
                ·
                  refine ⟨18603302785545592720848917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12402201857030395147232611 18603302785545592720848917)
                  ·
                    refine ⟨872029818072449658789793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18603302785545592720848917 872029818072449658789793)
                    ·
                      rfl

theorem cell22_2547408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_2547408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547408 prefixEnd_2547408 := by exact prefixLift 2547408
  have htrace : WordTrace (prefixWord ++ tailWord_2547408) baseStart_2547408 baseEnd_2547408 := by
    simpa [prefixWord, tailWord_2547408, baseEnd_2547408] using wordTrace_append hprefix tailTrace_2547408
  have hstable : (prefixWord ++ tailWord_2547408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547408).length < 2 ^ (prefixWord ++ tailWord_2547408).sum := by decide
  have hdescent : baseEnd_2547408 < baseStart_2547408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547423 : List Nat := [1, 1, 2, 3, 2, 2, 1, 10]
def baseStart_2547423 : Nat := 118140960795 + 2547423 * 2 ^ 59
def prefixEnd_2547423 : Nat := 4983230072969 + 3 ^ 40 * 2547423 * 2
def baseEnd_2547423 : Nat := 96892772542110513296083

theorem tailTrace_2547423 : CollatzResearch.WordTrace tailWord_2547423 prefixEnd_2547423 96892772542110513296083 := by
  unfold tailWord_2547423
  simp only [CollatzResearch.WordTrace]
  refine ⟨92912149850129011056198923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61941433233419340704132615 92912149850129011056198923)
  ·
    refine ⟨139368224775193516584298385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92912149850129011056198923 139368224775193516584298385)
    ·
      refine ⟨104526168581395137438223789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139368224775193516584298385 104526168581395137438223789)
      ·
        refine ⟨39197313218023176539333921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104526168581395137438223789 39197313218023176539333921)
        ·
          refine ⟨29397984913517382404500441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39197313218023176539333921 29397984913517382404500441)
          ·
            refine ⟨22048488685138036803375331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29397984913517382404500441 22048488685138036803375331)
            ·
              refine ⟨33072733027707055205062997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22048488685138036803375331 33072733027707055205062997)
              ·
                refine ⟨96892772542110513296083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33072733027707055205062997 96892772542110513296083)
                ·
                  rfl

theorem cell22_2547423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 10].length) (baseStart_2547423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547423 prefixEnd_2547423 := by exact prefixLift 2547423
  have htrace : WordTrace (prefixWord ++ tailWord_2547423) baseStart_2547423 baseEnd_2547423 := by
    simpa [prefixWord, tailWord_2547423, baseEnd_2547423] using wordTrace_append hprefix tailTrace_2547423
  have hstable : (prefixWord ++ tailWord_2547423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547423).length < 2 ^ (prefixWord ++ tailWord_2547423).sum := by decide
  have hdescent : baseEnd_2547423 < baseStart_2547423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547427 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 1, 5]
def baseStart_2547427 : Nat := 118140960795 + 2547427 * 2 ^ 59
def prefixEnd_2547427 : Nat := 4983230072969 + 3 ^ 40 * 2547427 * 2
def baseEnd_2547427 : Nat := 872036322160739942564735

theorem tailTrace_2547427 : CollatzResearch.WordTrace tailWord_2547427 prefixEnd_2547427 872036322160739942564735 := by
  unfold tailWord_2547427
  simp only [CollatzResearch.WordTrace]
  refine ⟨92912295742114519739344535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61941530494743013159563023 92912295742114519739344535)
  ·
    refine ⟨139368443613171779609016803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92912295742114519739344535 139368443613171779609016803)
    ·
      refine ⟨209052665419757669413525205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139368443613171779609016803 209052665419757669413525205)
      ·
        refine ⟨4899671845775570376879497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 209052665419757669413525205 4899671845775570376879497)
        ·
          refine ⟨3674753884331677782659623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4899671845775570376879497 3674753884331677782659623)
          ·
            refine ⟨5512130826497516673989435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674753884331677782659623 5512130826497516673989435)
            ·
              refine ⟨8268196239746275010984153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5512130826497516673989435 8268196239746275010984153)
              ·
                refine ⟨6201147179809706258238115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8268196239746275010984153 6201147179809706258238115)
                ·
                  refine ⟨9301720769714559387357173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6201147179809706258238115 9301720769714559387357173)
                  ·
                    refine ⟨872036322160739942564735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9301720769714559387357173 872036322160739942564735)
                    ·
                      rfl

theorem cell22_2547427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 5].length) (baseStart_2547427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547427 prefixEnd_2547427 := by exact prefixLift 2547427
  have htrace : WordTrace (prefixWord ++ tailWord_2547427) baseStart_2547427 baseEnd_2547427 := by
    simpa [prefixWord, tailWord_2547427, baseEnd_2547427] using wordTrace_append hprefix tailTrace_2547427
  have hstable : (prefixWord ++ tailWord_2547427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547427).length < 2 ^ (prefixWord ++ tailWord_2547427).sum := by decide
  have hdescent : baseEnd_2547427 < baseStart_2547427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547431 : List Nat := [1, 1, 5, 4, 1, 1, 3, 1, 1, 4]
def baseStart_2547431 : Nat := 118140960795 + 2547431 * 2 ^ 59
def prefixEnd_2547431 : Nat := 4983230072969 + 3 ^ 40 * 2547431 * 2
def baseEnd_2547431 : Nat := 872037691442485265464723

theorem tailTrace_2547431 : CollatzResearch.WordTrace tailWord_2547431 prefixEnd_2547431 872037691442485265464723 := by
  unfold tailWord_2547431
  simp only [CollatzResearch.WordTrace]
  refine ⟨92912441634100028422490147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61941627756066685614993431 92912441634100028422490147)
  ·
    refine ⟨139368662451150042633735221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92912441634100028422490147 139368662451150042633735221)
    ·
      refine ⟨13065812104795316496912677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139368662451150042633735221 13065812104795316496912677)
      ·
        refine ⟨2449839769649121843171127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13065812104795316496912677 2449839769649121843171127)
        ·
          refine ⟨3674759654473682764756691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2449839769649121843171127 3674759654473682764756691)
          ·
            refine ⟨5512139481710524147135037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674759654473682764756691 5512139481710524147135037)
            ·
              refine ⟨2067052305641446555175639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5512139481710524147135037 2067052305641446555175639)
              ·
                refine ⟨3100578458462169832763459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2067052305641446555175639 3100578458462169832763459)
                ·
                  refine ⟨4650867687693254749145189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100578458462169832763459 4650867687693254749145189)
                  ·
                    refine ⟨872037691442485265464723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4650867687693254749145189 872037691442485265464723)
                    ·
                      rfl

theorem cell22_2547431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_2547431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547431 prefixEnd_2547431 := by exact prefixLift 2547431
  have htrace : WordTrace (prefixWord ++ tailWord_2547431) baseStart_2547431 baseEnd_2547431 := by
    simpa [prefixWord, tailWord_2547431, baseEnd_2547431] using wordTrace_append hprefix tailTrace_2547431
  have hstable : (prefixWord ++ tailWord_2547431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547431).length < 2 ^ (prefixWord ++ tailWord_2547431).sum := by decide
  have hdescent : baseEnd_2547431 < baseStart_2547431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547446 : List Nat := [5, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_2547446 : Nat := 118140960795 + 2547446 * 2 ^ 59
def prefixEnd_2547446 : Nat := 4983230072969 + 3 ^ 40 * 2547446 * 2
def baseEnd_2547446 : Nat := 290680942083010075446559

theorem tailTrace_2547446 : CollatzResearch.WordTrace tailWord_2547446 prefixEnd_2547446 290680942083010075446559 := by
  unfold tailWord_2547446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5807061795565355374017887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61941992486030457322857461 5807061795565355374017887)
  ·
    refine ⟨8710592693348033061026831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5807061795565355374017887 8710592693348033061026831)
    ·
      refine ⟨13065889040022049591540247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8710592693348033061026831 13065889040022049591540247)
      ·
        refine ⟨19598833560033074387310371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13065889040022049591540247 19598833560033074387310371)
        ·
          refine ⟨29398250340049611580965557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19598833560033074387310371 29398250340049611580965557)
          ·
            refine ⟨2756085969379651085715521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29398250340049611580965557 2756085969379651085715521)
            ·
              refine ⟨2067064477034738314286641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2756085969379651085715521 2067064477034738314286641)
              ·
                refine ⟨1550298357776053735714981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067064477034738314286641 1550298357776053735714981)
                ·
                  refine ⟨290680942083010075446559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550298357776053735714981 290680942083010075446559)
                  ·
                    rfl

theorem cell22_2547446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_2547446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547446 prefixEnd_2547446 := by exact prefixLift 2547446
  have htrace : WordTrace (prefixWord ++ tailWord_2547446) baseStart_2547446 baseEnd_2547446 := by
    simpa [prefixWord, tailWord_2547446, baseEnd_2547446] using wordTrace_append hprefix tailTrace_2547446
  have hstable : (prefixWord ++ tailWord_2547446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547446).length < 2 ^ (prefixWord ++ tailWord_2547446).sum := by decide
  have hdescent : baseEnd_2547446 < baseStart_2547446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547474 : List Nat := [3, 2, 4, 1, 1, 2, 3, 6]
def baseStart_2547474 : Nat := 118140960795 + 2547474 * 2 ^ 59
def prefixEnd_2547474 : Nat := 4983230072969 + 3 ^ 40 * 2547474 * 2
def baseEnd_2547474 : Nat := 96894712357916387404399

theorem tailTrace_2547474 : CollatzResearch.WordTrace tailWord_2547474 prefixEnd_2547474 96894712357916387404399 := by
  unfold tailWord_2547474
  simp only [CollatzResearch.WordTrace]
  refine ⟨23228502493236061691576369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61942673315296164510870317 23228502493236061691576369)
  ·
    refine ⟨17421376869927046268682277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23228502493236061691576369 17421376869927046268682277)
    ·
      refine ⟨3266508163111321175377927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17421376869927046268682277 3266508163111321175377927)
      ·
        refine ⟨4899762244666981763066891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3266508163111321175377927 4899762244666981763066891)
        ·
          refine ⟨7349643367000472644600337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4899762244666981763066891 7349643367000472644600337)
          ·
            refine ⟨5512232525250354483450253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7349643367000472644600337 5512232525250354483450253)
            ·
              refine ⟨2067087196968882931293845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5512232525250354483450253 2067087196968882931293845)
              ·
                refine ⟨96894712357916387404399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2067087196968882931293845 96894712357916387404399)
                ·
                  rfl

theorem cell22_2547474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 6].length) (baseStart_2547474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547474 prefixEnd_2547474 := by exact prefixLift 2547474
  have htrace : WordTrace (prefixWord ++ tailWord_2547474) baseStart_2547474 baseEnd_2547474 := by
    simpa [prefixWord, tailWord_2547474, baseEnd_2547474] using wordTrace_append hprefix tailTrace_2547474
  have hstable : (prefixWord ++ tailWord_2547474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547474).length < 2 ^ (prefixWord ++ tailWord_2547474).sum := by decide
  have hdescent : baseEnd_2547474 < baseStart_2547474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547476 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2547476 : Nat := 118140960795 + 2547476 * 2 ^ 59
def prefixEnd_2547476 : Nat := 4983230072969 + 3 ^ 40 * 2547476 * 2
def baseEnd_2547476 : Nat := 872053095862120148089585

theorem tailTrace_2547476 : CollatzResearch.WordTrace tailWord_2547476 prefixEnd_2547476 872053095862120148089585 := by
  unfold tailWord_2547476
  simp only [CollatzResearch.WordTrace]
  refine ⟨46457041459468500553939141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61942721945958000738585521 46457041459468500553939141)
  ·
    refine ⟨8710695273650343853863589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46457041459468500553939141 8710695273650343853863589)
    ·
      refine ⟨1633255363809439472599423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8710695273650343853863589 1633255363809439472599423)
      ·
        refine ⟨2449883045714159208899135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1633255363809439472599423 2449883045714159208899135)
        ·
          refine ⟨3674824568571238813348703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2449883045714159208899135 3674824568571238813348703)
          ·
            refine ⟨5512236852856858220023055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674824568571238813348703 5512236852856858220023055)
            ·
              refine ⟨8268355279285287330034583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5512236852856858220023055 8268355279285287330034583)
              ·
                refine ⟨12402532918927930995051875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8268355279285287330034583 12402532918927930995051875)
                ·
                  refine ⟨18603799378391896492577813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12402532918927930995051875 18603799378391896492577813)
                  ·
                    refine ⟨872053095862120148089585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18603799378391896492577813 872053095862120148089585)
                    ·
                      rfl

theorem cell22_2547476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2547476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547476 prefixEnd_2547476 := by exact prefixLift 2547476
  have htrace : WordTrace (prefixWord ++ tailWord_2547476) baseStart_2547476 baseEnd_2547476 := by
    simpa [prefixWord, tailWord_2547476, baseEnd_2547476] using wordTrace_append hprefix tailTrace_2547476
  have hstable : (prefixWord ++ tailWord_2547476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547476).length < 2 ^ (prefixWord ++ tailWord_2547476).sum := by decide
  have hdescent : baseEnd_2547476 < baseStart_2547476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547489 : List Nat := [1, 2, 3, 2, 1, 3, 1, 5, 1, 3]
def baseStart_2547489 : Nat := 118140960795 + 2547489 * 2 ^ 59
def prefixEnd_2547489 : Nat := 4983230072969 + 3 ^ 40 * 2547489 * 2
def baseEnd_2547489 : Nat := 872057546027792447514545

theorem tailTrace_2547489 : CollatzResearch.WordTrace tailWord_2547489 prefixEnd_2547489 872057546027792447514545 := by
  unfold tailWord_2547489
  simp only [CollatzResearch.WordTrace]
  refine ⟨92914557067889904328101521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61943038045259936218734347 92914557067889904328101521)
  ·
    refine ⟨69685917800917428246076141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92914557067889904328101521 69685917800917428246076141)
    ·
      refine ⟨26132219175344035592278553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69685917800917428246076141 26132219175344035592278553)
      ·
        refine ⟨19599164381508026694208915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26132219175344035592278553 19599164381508026694208915)
        ·
          refine ⟨29398746572262040041313373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19599164381508026694208915 29398746572262040041313373)
          ·
            refine ⟨11024529964598265015492515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29398746572262040041313373 11024529964598265015492515)
            ·
              refine ⟨16536794946897397523238773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11024529964598265015492515 16536794946897397523238773)
              ·
                refine ⟨1550324526271631017803635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16536794946897397523238773 1550324526271631017803635)
                ·
                  refine ⟨2325486789407446526705453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550324526271631017803635 2325486789407446526705453)
                  ·
                    refine ⟨872057546027792447514545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2325486789407446526705453 872057546027792447514545)
                    ·
                      rfl

theorem cell22_2547489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_2547489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547489 prefixEnd_2547489 := by exact prefixLift 2547489
  have htrace : WordTrace (prefixWord ++ tailWord_2547489) baseStart_2547489 baseEnd_2547489 := by
    simpa [prefixWord, tailWord_2547489, baseEnd_2547489] using wordTrace_append hprefix tailTrace_2547489
  have hstable : (prefixWord ++ tailWord_2547489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547489).length < 2 ^ (prefixWord ++ tailWord_2547489).sum := by decide
  have hdescent : baseEnd_2547489 < baseStart_2547489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547500 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 2, 5]
def baseStart_2547500 : Nat := 118140960795 + 2547500 * 2 ^ 59
def prefixEnd_2547500 : Nat := 4983230072969 + 3 ^ 40 * 2547500 * 2
def baseEnd_2547500 : Nat := 872061311552592085489511

theorem tailTrace_2547500 : CollatzResearch.WordTrace tailWord_2547500 prefixEnd_2547500 872061311552592085489511 := by
  unfold tailWord_2547500
  simp only [CollatzResearch.WordTrace]
  refine ⟨46457479135425026603375977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61943305513900035471167969 46457479135425026603375977)
  ·
    refine ⟨34843109351568769952531983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46457479135425026603375977 34843109351568769952531983)
    ·
      refine ⟨52264664027353154928797975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34843109351568769952531983 52264664027353154928797975)
      ·
        refine ⟨78396996041029732393196963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52264664027353154928797975 78396996041029732393196963)
        ·
          refine ⟨117595494061544598589795445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78396996041029732393196963 117595494061544598589795445)
          ·
            refine ⟨11024577568269806117793323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117595494061544598589795445 11024577568269806117793323)
            ·
              refine ⟨16536866352404709176689985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11024577568269806117793323 16536866352404709176689985)
              ·
                refine ⟨12402649764303531882517489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16536866352404709176689985 12402649764303531882517489)
                ·
                  refine ⟨9301987323227648911888117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12402649764303531882517489 9301987323227648911888117)
                  ·
                    refine ⟨872061311552592085489511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9301987323227648911888117 872061311552592085489511)
                    ·
                      rfl

theorem cell22_2547500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_2547500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547500 prefixEnd_2547500 := by exact prefixLift 2547500
  have htrace : WordTrace (prefixWord ++ tailWord_2547500) baseStart_2547500 baseEnd_2547500 := by
    simpa [prefixWord, tailWord_2547500, baseEnd_2547500] using wordTrace_append hprefix tailTrace_2547500
  have hstable : (prefixWord ++ tailWord_2547500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547500).length < 2 ^ (prefixWord ++ tailWord_2547500).sum := by decide
  have hdescent : baseEnd_2547500 < baseStart_2547500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547517 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_2547517 : Nat := 118140960795 + 2547517 * 2 ^ 59
def prefixEnd_2547517 : Nat := 4983230072969 + 3 ^ 40 * 2547517 * 2
def baseEnd_2547517 : Nat := 872067131000009707814459

theorem tailTrace_2547517 : CollatzResearch.WordTrace tailWord_2547517 prefixEnd_2547517 872067131000009707814459 := by
  unfold tailWord_2547517
  simp only [CollatzResearch.WordTrace]
  refine ⟨92915578311788465110120805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61943718874525643406747203 92915578311788465110120805)
  ·
    refine ⟨17421670933460337208147651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92915578311788465110120805 17421670933460337208147651)
    ·
      refine ⟨26132506400190505812221477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17421670933460337208147651 26132506400190505812221477)
      ·
        refine ⟨4899844950035719839791527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26132506400190505812221477 4899844950035719839791527)
        ·
          refine ⟨7349767425053579759687291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4899844950035719839791527 7349767425053579759687291)
          ·
            refine ⟨11024651137580369639530937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7349767425053579759687291 11024651137580369639530937)
            ·
              refine ⟨8268488353185277229648203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11024651137580369639530937 8268488353185277229648203)
              ·
                refine ⟨12402732529777915844472305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8268488353185277229648203 12402732529777915844472305)
                ·
                  refine ⟨9302049397333436883354229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12402732529777915844472305 9302049397333436883354229)
                  ·
                    refine ⟨872067131000009707814459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9302049397333436883354229 872067131000009707814459)
                    ·
                      rfl

theorem cell22_2547517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_2547517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547517 prefixEnd_2547517 := by exact prefixLift 2547517
  have htrace : WordTrace (prefixWord ++ tailWord_2547517) baseStart_2547517 baseEnd_2547517 := by
    simpa [prefixWord, tailWord_2547517, baseEnd_2547517] using wordTrace_append hprefix tailTrace_2547517
  have hstable : (prefixWord ++ tailWord_2547517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547517).length < 2 ^ (prefixWord ++ tailWord_2547517).sum := by decide
  have hdescent : baseEnd_2547517 < baseStart_2547517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547519 : List Nat := [1, 1, 2, 2, 6, 1, 3, 1, 5]
def baseStart_2547519 : Nat := 118140960795 + 2547519 * 2 ^ 59
def prefixEnd_2547519 : Nat := 4983230072969 + 3 ^ 40 * 2547519 * 2
def baseEnd_2547519 : Nat := 290689271880294123088151

theorem tailTrace_2547519 : CollatzResearch.WordTrace tailWord_2547519 prefixEnd_2547519 290689271880294123088151 := by
  unfold tailWord_2547519
  simp only [CollatzResearch.WordTrace]
  refine ⟨92915651257781219451693611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61943767505187479634462407 92915651257781219451693611)
  ·
    refine ⟨139373476886671829177540417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92915651257781219451693611 139373476886671829177540417)
    ·
      refine ⟨104530107665003871883155313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139373476886671829177540417 104530107665003871883155313)
      ·
        refine ⟨78397580748752903912366485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104530107665003871883155313 78397580748752903912366485)
        ·
          refine ⟨3674886597597792370892179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78397580748752903912366485 3674886597597792370892179)
          ·
            refine ⟨5512329896396688556338269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674886597597792370892179 5512329896396688556338269)
            ·
              refine ⟨2067123711148758208626851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5512329896396688556338269 2067123711148758208626851)
              ·
                refine ⟨3100685566723137312940277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2067123711148758208626851 3100685566723137312940277)
                ·
                  refine ⟨290689271880294123088151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3100685566723137312940277 290689271880294123088151)
                  ·
                    rfl

theorem cell22_2547519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 5].length) (baseStart_2547519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547519 prefixEnd_2547519 := by exact prefixLift 2547519
  have htrace : WordTrace (prefixWord ++ tailWord_2547519) baseStart_2547519 baseEnd_2547519 := by
    simpa [prefixWord, tailWord_2547519, baseEnd_2547519] using wordTrace_append hprefix tailTrace_2547519
  have hstable : (prefixWord ++ tailWord_2547519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547519).length < 2 ^ (prefixWord ++ tailWord_2547519).sum := by decide
  have hdescent : baseEnd_2547519 < baseStart_2547519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547530 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 6]
def baseStart_2547530 : Nat := 118140960795 + 2547530 * 2 ^ 59
def prefixEnd_2547530 : Nat := 4983230072969 + 3 ^ 40 * 2547530 * 2
def baseEnd_2547530 : Nat := 290690527055227335746473

theorem tailTrace_2547530 : CollatzResearch.WordTrace tailWord_2547530 prefixEnd_2547530 290690527055227335746473 := by
  unfold tailWord_2547530
  simp only [CollatzResearch.WordTrace]
  refine ⟨23229013115185342082586011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61944034973827578886896029 23229013115185342082586011)
  ·
    refine ⟨34843519672778013123879017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23229013115185342082586011 34843519672778013123879017)
    ·
      refine ⟨26132639754583509842909263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34843519672778013123879017 26132639754583509842909263)
      ·
        refine ⟨39198959631875264764363895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26132639754583509842909263 39198959631875264764363895)
        ·
          refine ⟨58798439447812897146545843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39198959631875264764363895 58798439447812897146545843)
          ·
            refine ⟨88197659171719345719818765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58798439447812897146545843 88197659171719345719818765)
            ·
              refine ⟨33074122189394754644932037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88197659171719345719818765 33074122189394754644932037)
              ·
                refine ⟨6201397910511516495924757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33074122189394754644932037 6201397910511516495924757)
                ·
                  refine ⟨290690527055227335746473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6201397910511516495924757 290690527055227335746473)
                  ·
                    rfl

theorem cell22_2547530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_2547530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547530 prefixEnd_2547530 := by exact prefixLift 2547530
  have htrace : WordTrace (prefixWord ++ tailWord_2547530) baseStart_2547530 baseEnd_2547530 := by
    simpa [prefixWord, tailWord_2547530, baseEnd_2547530] using wordTrace_append hprefix tailTrace_2547530
  have hstable : (prefixWord ++ tailWord_2547530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547530).length < 2 ^ (prefixWord ++ tailWord_2547530).sum := by decide
  have hdescent : baseEnd_2547530 < baseStart_2547530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547545 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 3, 5]
def baseStart_2547545 : Nat := 118140960795 + 2547545 * 2 ^ 59
def prefixEnd_2547545 : Nat := 4983230072969 + 3 ^ 40 * 2547545 * 2
def baseEnd_2547545 : Nat := 872076715972226968114373

theorem tailTrace_2547545 : CollatzResearch.WordTrace tailWord_2547545 prefixEnd_2547545 872076715972226968114373 := by
  unfold tailWord_2547545
  simp only [CollatzResearch.WordTrace]
  refine ⟨92916599555687025892140089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61944399703791350594760059 92916599555687025892140089)
  ·
    refine ⟨69687449666765269419105067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92916599555687025892140089 69687449666765269419105067)
    ·
      refine ⟨104531174500147904128657601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69687449666765269419105067 104531174500147904128657601)
      ·
        refine ⟨78398380875110928096493201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104531174500147904128657601 78398380875110928096493201)
        ·
          refine ⟨58798785656333196072369901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78398380875110928096493201 58798785656333196072369901)
          ·
            refine ⟨22049544621124948527138713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58798785656333196072369901 22049544621124948527138713)
            ·
              refine ⟨16537158465843711395354035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22049544621124948527138713 16537158465843711395354035)
              ·
                refine ⟨24805737698765567093031053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16537158465843711395354035 24805737698765567093031053)
                ·
                  refine ⟨9302151637037087659886645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24805737698765567093031053 9302151637037087659886645)
                  ·
                    refine ⟨872076715972226968114373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9302151637037087659886645 872076715972226968114373)
                    ·
                      rfl

theorem cell22_2547545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_2547545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547545 prefixEnd_2547545 := by exact prefixLift 2547545
  have htrace : WordTrace (prefixWord ++ tailWord_2547545) baseStart_2547545 baseEnd_2547545 := by
    simpa [prefixWord, tailWord_2547545, baseEnd_2547545] using wordTrace_append hprefix tailTrace_2547545
  have hstable : (prefixWord ++ tailWord_2547545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547545).length < 2 ^ (prefixWord ++ tailWord_2547545).sum := by decide
  have hdescent : baseEnd_2547545 < baseStart_2547545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547733 : List Nat := [1, 3, 2, 1, 5, 1, 3, 2, 4]
def baseStart_2547733 : Nat := 118140960795 + 2547733 * 2 ^ 59
def prefixEnd_2547733 : Nat := 4983230072969 + 3 ^ 40 * 2547733 * 2
def baseEnd_2547733 : Nat := 290713690738085714804599

theorem tailTrace_2547733 : CollatzResearch.WordTrace tailWord_2547733 prefixEnd_2547733 290713690738085714804599 := by
  unfold tailWord_2547733
  simp only [CollatzResearch.WordTrace]
  refine ⟨92923456479005933999983853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61948970986003955999989235 92923456479005933999983853)
  ·
    refine ⟨34846296179627225249993945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92923456479005933999983853 34846296179627225249993945)
    ·
      refine ⟨26134722134720418937495459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34846296179627225249993945 26134722134720418937495459)
      ·
        refine ⟨39202083202080628406243189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26134722134720418937495459 39202083202080628406243189)
        ·
          refine ⟨3675195300195058913085299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39202083202080628406243189 3675195300195058913085299)
          ·
            refine ⟨5512792950292588369627949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3675195300195058913085299 5512792950292588369627949)
            ·
              refine ⟨2067297356359720638610481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5512792950292588369627949 2067297356359720638610481)
              ·
                refine ⟨1550473017269790478957861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067297356359720638610481 1550473017269790478957861)
                ·
                  refine ⟨290713690738085714804599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550473017269790478957861 290713690738085714804599)
                  ·
                    rfl

theorem cell22_2547733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_2547733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547733 prefixEnd_2547733 := by exact prefixLift 2547733
  have htrace : WordTrace (prefixWord ++ tailWord_2547733) baseStart_2547733 baseEnd_2547733 := by
    simpa [prefixWord, tailWord_2547733, baseEnd_2547733] using wordTrace_append hprefix tailTrace_2547733
  have hstable : (prefixWord ++ tailWord_2547733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547733).length < 2 ^ (prefixWord ++ tailWord_2547733).sum := by decide
  have hdescent : baseEnd_2547733 < baseStart_2547733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547748 : List Nat := [2, 3, 1, 4, 2, 1, 1, 3, 2, 3]
def baseStart_2547748 : Nat := 118140960795 + 2547748 * 2 ^ 59
def prefixEnd_2547748 : Nat := 4983230072969 + 3 ^ 40 * 2547748 * 2
def baseEnd_2547748 : Nat := 872146207020802105288751

theorem tailTrace_2547748 : CollatzResearch.WordTrace tailWord_2547748 prefixEnd_2547748 872146207020802105288751 := by
  unfold tailWord_2547748
  simp only [CollatzResearch.WordTrace]
  refine ⟨46462001786975795780889949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61949335715967727707853265 46462001786975795780889949)
  ·
    refine ⟨17423250670115923417833731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46462001786975795780889949 17423250670115923417833731)
    ·
      refine ⟨26134876005173885126750597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17423250670115923417833731 26134876005173885126750597)
      ·
        refine ⟨4900289250970103461265737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26134876005173885126750597 4900289250970103461265737)
        ·
          refine ⟨3675216938227577595949303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4900289250970103461265737 3675216938227577595949303)
          ·
            refine ⟨5512825407341366393923955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3675216938227577595949303 5512825407341366393923955)
            ·
              refine ⟨8269238111012049590885933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5512825407341366393923955 8269238111012049590885933)
              ·
                refine ⟨3100964291629518596582225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8269238111012049590885933 3100964291629518596582225)
                ·
                  refine ⟨2325723218722138947436669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3100964291629518596582225 2325723218722138947436669)
                  ·
                    refine ⟨872146207020802105288751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2325723218722138947436669 872146207020802105288751)
                    ·
                      rfl

theorem cell22_2547748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_2547748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547748 prefixEnd_2547748 := by exact prefixLift 2547748
  have htrace : WordTrace (prefixWord ++ tailWord_2547748) baseStart_2547748 baseEnd_2547748 := by
    simpa [prefixWord, tailWord_2547748, baseEnd_2547748] using wordTrace_append hprefix tailTrace_2547748
  have hstable : (prefixWord ++ tailWord_2547748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547748).length < 2 ^ (prefixWord ++ tailWord_2547748).sum := by decide
  have hdescent : baseEnd_2547748 < baseStart_2547748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547787 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 4, 5]
def baseStart_2547787 : Nat := 118140960795 + 2547787 * 2 ^ 59
def prefixEnd_2547787 : Nat := 4983230072969 + 3 ^ 40 * 2547787 * 2
def baseEnd_2547787 : Nat := 872159557517819003563631

theorem tailTrace_2547787 : CollatzResearch.WordTrace tailWord_2547787 prefixEnd_2547787 872159557517819003563631 := by
  unfold tailWord_2547787
  simp only [CollatzResearch.WordTrace]
  refine ⟨92925426020810301222449615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61950284013873534148299743 92925426020810301222449615)
  ·
    refine ⟨139388139031215451833674423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92925426020810301222449615 139388139031215451833674423)
    ·
      refine ⟨209082208546823177750511635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139388139031215451833674423 209082208546823177750511635)
      ·
        refine ⟨313623312820234766625767453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209082208546823177750511635 313623312820234766625767453)
        ·
          refine ⟨117608742307588037484662795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313623312820234766625767453 117608742307588037484662795)
          ·
            refine ⟨176413113461382056226994193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117608742307588037484662795 176413113461382056226994193)
            ·
              refine ⟨132309835096036542170245645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176413113461382056226994193 132309835096036542170245645)
              ·
                refine ⟨49616188161013703313842117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132309835096036542170245645 49616188161013703313842117)
                ·
                  refine ⟨9303035280190069371345397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49616188161013703313842117 9303035280190069371345397)
                  ·
                    refine ⟨872159557517819003563631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9303035280190069371345397 872159557517819003563631)
                    ·
                      rfl

theorem cell22_2547787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 5].length) (baseStart_2547787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547787 prefixEnd_2547787 := by exact prefixLift 2547787
  have htrace : WordTrace (prefixWord ++ tailWord_2547787) baseStart_2547787 baseEnd_2547787 := by
    simpa [prefixWord, tailWord_2547787, baseEnd_2547787] using wordTrace_append hprefix tailTrace_2547787
  have hstable : (prefixWord ++ tailWord_2547787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547787).length < 2 ^ (prefixWord ++ tailWord_2547787).sum := by decide
  have hdescent : baseEnd_2547787 < baseStart_2547787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547804 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 1, 7]
def baseStart_2547804 : Nat := 118140960795 + 2547804 * 2 ^ 59
def prefixEnd_2547804 : Nat := 4983230072969 + 3 ^ 40 * 2547804 * 2
def baseEnd_2547804 : Nat := 872165376965236625888579

theorem tailTrace_2547804 : CollatzResearch.WordTrace tailWord_2547804 prefixEnd_2547804 872165376965236625888579 := by
  unfold tailWord_2547804
  simp only [CollatzResearch.WordTrace]
  refine ⟨46463023030874356562909233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61950697374499142083878977 46463023030874356562909233)
  ·
    refine ⟨34847267273155767422181925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46463023030874356562909233 34847267273155767422181925)
    ·
      refine ⟨6533862613716706391659111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34847267273155767422181925 6533862613716706391659111)
      ·
        refine ⟨9800793920575059587488667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6533862613716706391659111 9800793920575059587488667)
        ·
          refine ⟨14701190880862589381233001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9800793920575059587488667 14701190880862589381233001)
          ·
            refine ⟨11025893160646942035924751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14701190880862589381233001 11025893160646942035924751)
            ·
              refine ⟨16538839740970413053887127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11025893160646942035924751 16538839740970413053887127)
              ·
                refine ⟨24808259611455619580830691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16538839740970413053887127 24808259611455619580830691)
                ·
                  refine ⟨37212389417183429371246037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24808259611455619580830691 37212389417183429371246037)
                  ·
                    refine ⟨872165376965236625888579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37212389417183429371246037 872165376965236625888579)
                    ·
                      rfl

theorem cell22_2547804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_2547804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547804 prefixEnd_2547804 := by exact prefixLift 2547804
  have htrace : WordTrace (prefixWord ++ tailWord_2547804) baseStart_2547804 baseEnd_2547804 := by
    simpa [prefixWord, tailWord_2547804, baseEnd_2547804] using wordTrace_append hprefix tailTrace_2547804
  have hstable : (prefixWord ++ tailWord_2547804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547804).length < 2 ^ (prefixWord ++ tailWord_2547804).sum := by decide
  have hdescent : baseEnd_2547804 < baseStart_2547804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547836 : List Nat := [2, 2, 2, 1, 1, 5, 1, 3, 1, 4]
def baseStart_2547836 : Nat := 118140960795 + 2547836 * 2 ^ 59
def prefixEnd_2547836 : Nat := 4983230072969 + 3 ^ 40 * 2547836 * 2
def baseEnd_2547836 : Nat := 872176331219199209088481

theorem tailTrace_2547836 : CollatzResearch.WordTrace tailWord_2547836 prefixEnd_2547836 872176331219199209088481 := by
  unfold tailWord_2547836
  simp only [CollatzResearch.WordTrace]
  refine ⟨46463606598816391295491681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61951475465088521727322241 46463606598816391295491681)
  ·
    refine ⟨34847704949112293471618761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46463606598816391295491681 34847704949112293471618761)
    ·
      refine ⟨26135778711834220103714071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34847704949112293471618761 26135778711834220103714071)
      ·
        refine ⟨39203668067751330155571107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26135778711834220103714071 39203668067751330155571107)
        ·
          refine ⟨58805502101626995233356661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39203668067751330155571107 58805502101626995233356661)
          ·
            refine ⟨5513015822027530803127187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58805502101626995233356661 5513015822027530803127187)
            ·
              refine ⟨8269523733041296204690781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5513015822027530803127187 8269523733041296204690781)
              ·
                refine ⟨3101071399890486076759043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8269523733041296204690781 3101071399890486076759043)
                ·
                  refine ⟨4651607099835729115138565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3101071399890486076759043 4651607099835729115138565)
                  ·
                    refine ⟨872176331219199209088481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4651607099835729115138565 872176331219199209088481)
                    ·
                      rfl

theorem cell22_2547836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_2547836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547836 prefixEnd_2547836 := by exact prefixLift 2547836
  have htrace : WordTrace (prefixWord ++ tailWord_2547836) baseStart_2547836 baseEnd_2547836 := by
    simpa [prefixWord, tailWord_2547836, baseEnd_2547836] using wordTrace_append hprefix tailTrace_2547836
  have hstable : (prefixWord ++ tailWord_2547836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547836).length < 2 ^ (prefixWord ++ tailWord_2547836).sum := by decide
  have hdescent : baseEnd_2547836 < baseStart_2547836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547870 : List Nat := [4, 3, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_2547870 : Nat := 118140960795 + 2547870 * 2 ^ 59
def prefixEnd_2547870 : Nat := 4983230072969 + 3 ^ 40 * 2547870 * 2
def baseEnd_2547870 : Nat := 872187970114034453738377

theorem tailTrace_2547870 : CollatzResearch.WordTrace tailWord_2547870 prefixEnd_2547870 872187970114034453738377 := by
  unfold tailWord_2547870
  simp only [CollatzResearch.WordTrace]
  refine ⟨11616056659938700799715133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61952302186339737598480709 11616056659938700799715133)
  ·
    refine ⟨4356021247477012799893175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11616056659938700799715133 4356021247477012799893175)
    ·
      refine ⟨6534031871215519199839763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4356021247477012799893175 6534031871215519199839763)
      ·
        refine ⟨9801047806823278799759645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6534031871215519199839763 9801047806823278799759645)
        ·
          refine ⟨3675392927558729549909867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9801047806823278799759645 3675392927558729549909867)
          ·
            refine ⟨5513089391338094324864801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3675392927558729549909867 5513089391338094324864801)
            ·
              refine ⟨4134817043503570743648601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5513089391338094324864801 4134817043503570743648601)
              ·
                refine ⟨3101112782627678057736451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4134817043503570743648601 3101112782627678057736451)
                ·
                  refine ⟨4651669173941517086604677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3101112782627678057736451 4651669173941517086604677)
                  ·
                    refine ⟨872187970114034453738377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4651669173941517086604677 872187970114034453738377)
                    ·
                      rfl

theorem cell22_2547870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_2547870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547870 prefixEnd_2547870 := by exact prefixLift 2547870
  have htrace : WordTrace (prefixWord ++ tailWord_2547870) baseStart_2547870 baseEnd_2547870 := by
    simpa [prefixWord, tailWord_2547870, baseEnd_2547870] using wordTrace_append hprefix tailTrace_2547870
  have hstable : (prefixWord ++ tailWord_2547870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547870).length < 2 ^ (prefixWord ++ tailWord_2547870).sum := by decide
  have hdescent : baseEnd_2547870 < baseStart_2547870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547885 : List Nat := [1, 5, 2, 1, 2, 3, 1, 3, 4]
def baseStart_2547885 : Nat := 118140960795 + 2547885 * 2 ^ 59
def prefixEnd_2547885 : Nat := 4983230072969 + 3 ^ 40 * 2547885 * 2
def baseEnd_2547885 : Nat := 290731034973526471537777

theorem tailTrace_2547885 : CollatzResearch.WordTrace tailWord_2547885 prefixEnd_2547885 290731034973526471537777 := by
  unfold tailWord_2547885
  simp only [CollatzResearch.WordTrace]
  refine ⟨92929000374455263959517109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61952666916303509306344739 92929000374455263959517109)
  ·
    refine ⟨8712093785105180996204729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92929000374455263959517109 8712093785105180996204729)
    ·
      refine ⟨6534070338828885747153547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8712093785105180996204729 6534070338828885747153547)
      ·
        refine ⟨9801105508243328620730321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6534070338828885747153547 9801105508243328620730321)
        ·
          refine ⟨7350829131182496465547741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9801105508243328620730321 7350829131182496465547741)
          ·
            refine ⟨2756560924193436174580403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7350829131182496465547741 2756560924193436174580403)
            ·
              refine ⟨4134841386290154261870605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2756560924193436174580403 4134841386290154261870605)
              ·
                refine ⟨1550565519858807848201477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4134841386290154261870605 1550565519858807848201477)
                ·
                  refine ⟨290731034973526471537777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550565519858807848201477 290731034973526471537777)
                  ·
                    rfl

theorem cell22_2547885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_2547885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547885 prefixEnd_2547885 := by exact prefixLift 2547885
  have htrace : WordTrace (prefixWord ++ tailWord_2547885) baseStart_2547885 baseEnd_2547885 := by
    simpa [prefixWord, tailWord_2547885, baseEnd_2547885] using wordTrace_append hprefix tailTrace_2547885
  have hstable : (prefixWord ++ tailWord_2547885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547885).length < 2 ^ (prefixWord ++ tailWord_2547885).sum := by decide
  have hdescent : baseEnd_2547885 < baseStart_2547885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547962 : List Nat := [3, 1, 1, 1, 1, 7, 2, 2, 1, 3]
def baseStart_2547962 : Nat := 118140960795 + 2547962 * 2 ^ 59
def prefixEnd_2547962 : Nat := 4983230072969 + 3 ^ 40 * 2547962 * 2
def baseEnd_2547962 : Nat := 872219463594176880438095

theorem tailTrace_2547962 : CollatzResearch.WordTrace tailWord_2547962 prefixEnd_2547962 872219463594176880438095 := by
  unfold tailWord_2547962
  simp only [CollatzResearch.WordTrace]
  refine ⟨23232952198794076527517535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61954539196784204073380093 23232952198794076527517535)
  ·
    refine ⟨34849428298191114791276303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23232952198794076527517535 34849428298191114791276303)
    ·
      refine ⟨52274142447286672186914455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34849428298191114791276303 52274142447286672186914455)
      ·
        refine ⟨78411213670930008280371683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52274142447286672186914455 78411213670930008280371683)
        ·
          refine ⟨117616820506395012420557525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78411213670930008280371683 117616820506395012420557525)
          ·
            refine ⟨2756644230618633103606817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 117616820506395012420557525 2756644230618633103606817)
            ·
              refine ⟨2067483172963974827705113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2756644230618633103606817 2067483172963974827705113)
              ·
                refine ⟨1550612379722981120778835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067483172963974827705113 1550612379722981120778835)
                ·
                  refine ⟨2325918569584471681168253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550612379722981120778835 2325918569584471681168253)
                  ·
                    refine ⟨872219463594176880438095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2325918569584471681168253 872219463594176880438095)
                    ·
                      rfl

theorem cell22_2547962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_2547962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2547962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2547962 prefixEnd_2547962 := by exact prefixLift 2547962
  have htrace : WordTrace (prefixWord ++ tailWord_2547962) baseStart_2547962 baseEnd_2547962 := by
    simpa [prefixWord, tailWord_2547962, baseEnd_2547962] using wordTrace_append hprefix tailTrace_2547962
  have hstable : (prefixWord ++ tailWord_2547962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547962).length < 2 ^ (prefixWord ++ tailWord_2547962).sum := by decide
  have hdescent : baseEnd_2547962 < baseStart_2547962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548001 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 1, 5]
def baseStart_2548001 : Nat := 118140960795 + 2548001 * 2 ^ 59
def prefixEnd_2548001 : Nat := 4983230072969 + 3 ^ 40 * 2548001 * 2
def baseEnd_2548001 : Nat := 872232814091193778712975

theorem tailTrace_2548001 : CollatzResearch.WordTrace tailWord_2548001 prefixEnd_2548001 872232814091193778712975 := by
  unfold tailWord_2548001
  simp only [CollatzResearch.WordTrace]
  refine ⟨92933231242035015770739857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61955487494690010513826571 92933231242035015770739857)
  ·
    refine ⟨69699923431526261828054893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92933231242035015770739857 69699923431526261828054893)
    ·
      refine ⟨26137471286822348185520585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69699923431526261828054893 26137471286822348185520585)
      ·
        refine ⟨19603103465116761139140439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26137471286822348185520585 19603103465116761139140439)
        ·
          refine ⟨29404655197675141708710659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19603103465116761139140439 29404655197675141708710659)
          ·
            refine ⟨44106982796512712563065989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29404655197675141708710659 44106982796512712563065989)
            ·
              refine ⟨8270059274346133605574873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44106982796512712563065989 8270059274346133605574873)
              ·
                refine ⟨6202544455759600204181155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8270059274346133605574873 6202544455759600204181155)
                ·
                  refine ⟨9303816683639400306271733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6202544455759600204181155 9303816683639400306271733)
                  ·
                    refine ⟨872232814091193778712975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9303816683639400306271733 872232814091193778712975)
                    ·
                      rfl

theorem cell22_2548001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_2548001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548001 prefixEnd_2548001 := by exact prefixLift 2548001
  have htrace : WordTrace (prefixWord ++ tailWord_2548001) baseStart_2548001 baseEnd_2548001 := by
    simpa [prefixWord, tailWord_2548001, baseEnd_2548001] using wordTrace_append hprefix tailTrace_2548001
  have hstable : (prefixWord ++ tailWord_2548001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548001).length < 2 ^ (prefixWord ++ tailWord_2548001).sum := by decide
  have hdescent : baseEnd_2548001 < baseStart_2548001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548003 : List Nat := [1, 1, 1, 4, 2, 2, 4, 3, 4]
def baseStart_2548003 : Nat := 118140960795 + 2548003 * 2 ^ 59
def prefixEnd_2548003 : Nat := 4983230072969 + 3 ^ 40 * 2548003 * 2
def baseEnd_2548003 : Nat := 290744499577355480054323

theorem tailTrace_2548003 : CollatzResearch.WordTrace tailWord_2548003 prefixEnd_2548003 290744499577355480054323 := by
  unfold tailWord_2548003
  simp only [CollatzResearch.WordTrace]
  refine ⟨92933304188027770112312663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61955536125351846741541775 92933304188027770112312663)
  ·
    refine ⟨139399956282041655168468995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92933304188027770112312663 139399956282041655168468995)
    ·
      refine ⟨209099934423062482752703493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139399956282041655168468995 209099934423062482752703493)
      ·
        refine ⟨39206237704324215516131905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209099934423062482752703493 39206237704324215516131905)
        ·
          refine ⟨29404678278243161637098929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39206237704324215516131905 29404678278243161637098929)
          ·
            refine ⟨22053508708682371227824197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29404678278243161637098929 22053508708682371227824197)
            ·
              refine ⟨4135032882877944605217037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22053508708682371227824197 4135032882877944605217037)
              ·
                refine ⟨1550637331079229226956389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4135032882877944605217037 1550637331079229226956389)
                ·
                  refine ⟨290744499577355480054323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550637331079229226956389 290744499577355480054323)
                  ·
                    rfl

theorem cell22_2548003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 4].length) (baseStart_2548003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548003 prefixEnd_2548003 := by exact prefixLift 2548003
  have htrace : WordTrace (prefixWord ++ tailWord_2548003) baseStart_2548003 baseEnd_2548003 := by
    simpa [prefixWord, tailWord_2548003, baseEnd_2548003] using wordTrace_append hprefix tailTrace_2548003
  have hstable : (prefixWord ++ tailWord_2548003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548003).length < 2 ^ (prefixWord ++ tailWord_2548003).sum := by decide
  have hdescent : baseEnd_2548003 < baseStart_2548003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548020 : List Nat := [2, 5, 1, 1, 1, 2, 2, 4, 4]
def baseStart_2548020 : Nat := 118140960795 + 2548020 * 2 ^ 59
def prefixEnd_2548020 : Nat := 4983230072969 + 3 ^ 40 * 2548020 * 2
def baseEnd_2548020 : Nat := 290746439393161354162639

theorem tailTrace_2548020 : CollatzResearch.WordTrace tailWord_2548020 prefixEnd_2548020 290746439393161354162639 := by
  unfold tailWord_2548020
  simp only [CollatzResearch.WordTrace]
  refine ⟨46466962114483091007840757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61955949485977454677121009 46466962114483091007840757)
  ·
    refine ⟨4356277698232789781985071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46466962114483091007840757 4356277698232789781985071)
    ·
      refine ⟨6534416547349184672977607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4356277698232789781985071 6534416547349184672977607)
      ·
        refine ⟨9801624821023777009466411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6534416547349184672977607 9801624821023777009466411)
        ·
          refine ⟨14702437231535665514199617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9801624821023777009466411 14702437231535665514199617)
          ·
            refine ⟨11026827923651749135649713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14702437231535665514199617 11026827923651749135649713)
            ·
              refine ⟨8270120942738811851737285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11026827923651749135649713 8270120942738811851737285)
              ·
                refine ⟨1550647676763527222200741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8270120942738811851737285 1550647676763527222200741)
                ·
                  refine ⟨290746439393161354162639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550647676763527222200741 290746439393161354162639)
                  ·
                    rfl

theorem cell22_2548020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_2548020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548020 prefixEnd_2548020 := by exact prefixLift 2548020
  have htrace : WordTrace (prefixWord ++ tailWord_2548020) baseStart_2548020 baseEnd_2548020 := by
    simpa [prefixWord, tailWord_2548020, baseEnd_2548020] using wordTrace_append hprefix tailTrace_2548020
  have hstable : (prefixWord ++ tailWord_2548020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548020).length < 2 ^ (prefixWord ++ tailWord_2548020).sum := by decide
  have hdescent : baseEnd_2548020 < baseStart_2548020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548048 : List Nat := [2, 1, 1, 1, 1, 8, 2, 6]
def baseStart_2548048 : Nat := 118140960795 + 2548048 * 2 ^ 59
def prefixEnd_2548048 : Nat := 4983230072969 + 3 ^ 40 * 2548048 * 2
def baseEnd_2548048 : Nat := 96916544794633480309759

theorem tailTrace_2548048 : CollatzResearch.WordTrace tailWord_2548048 prefixEnd_2548048 96916544794633480309759 := by
  unfold tailWord_2548048
  simp only [CollatzResearch.WordTrace]
  refine ⟨46467472736432371398850399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61956630315243161865133865 46467472736432371398850399)
  ·
    refine ⟨69701209104648557098275599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46467472736432371398850399 69701209104648557098275599)
    ·
      refine ⟨104551813656972835647413399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69701209104648557098275599 104551813656972835647413399)
      ·
        refine ⟨156827720485459253471120099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104551813656972835647413399 156827720485459253471120099)
        ·
          refine ⟨235241580728188880206680149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156827720485459253471120099 235241580728188880206680149)
          ·
            refine ⟨2756737274158463439922033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 235241580728188880206680149 2756737274158463439922033)
            ·
              refine ⟨2067552955618847579941525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2756737274158463439922033 2067552955618847579941525)
              ·
                refine ⟨96916544794633480309759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2067552955618847579941525 96916544794633480309759)
                ·
                  rfl

theorem cell22_2548048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 6].length) (baseStart_2548048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548048 prefixEnd_2548048 := by exact prefixLift 2548048
  have htrace : WordTrace (prefixWord ++ tailWord_2548048) baseStart_2548048 baseEnd_2548048 := by
    simpa [prefixWord, tailWord_2548048, baseEnd_2548048] using wordTrace_append hprefix tailTrace_2548048
  have hstable : (prefixWord ++ tailWord_2548048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548048).length < 2 ^ (prefixWord ++ tailWord_2548048).sum := by decide
  have hdescent : baseEnd_2548048 < baseStart_2548048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548080 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 3, 3]
def baseStart_2548080 : Nat := 118140960795 + 2548080 * 2 ^ 59
def prefixEnd_2548080 : Nat := 4983230072969 + 3 ^ 40 * 2548080 * 2
def baseEnd_2548080 : Nat := 872259857405663905987733

theorem tailTrace_2548080 : CollatzResearch.WordTrace tailWord_2548080 prefixEnd_2548080 872259857405663905987733 := by
  unfold tailWord_2548080
  simp only [CollatzResearch.WordTrace]
  refine ⟨46468056304374406131432847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61957408405832541508577129 46468056304374406131432847)
  ·
    refine ⟨69702084456561609197149271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46468056304374406131432847 69702084456561609197149271)
    ·
      refine ⟨104553126684842413795723907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69702084456561609197149271 104553126684842413795723907)
      ·
        refine ⟨156829690027263620693585861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104553126684842413795723907 156829690027263620693585861)
        ·
          refine ⟨29405566880111928880047349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156829690027263620693585861 29405566880111928880047349)
          ·
            refine ⟨2756771895010493332504439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29405566880111928880047349 2756771895010493332504439)
            ·
              refine ⟨4135157842515739998756659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2756771895010493332504439 4135157842515739998756659)
              ·
                refine ⟨6202736763773609998134989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4135157842515739998756659 6202736763773609998134989)
                ·
                  refine ⟨2326026286415103749300621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6202736763773609998134989 2326026286415103749300621)
                  ·
                    refine ⟨872259857405663905987733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2326026286415103749300621 872259857405663905987733)
                    ·
                      rfl

theorem cell22_2548080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 3, 3].length) (baseStart_2548080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548080 prefixEnd_2548080 := by exact prefixLift 2548080
  have htrace : WordTrace (prefixWord ++ tailWord_2548080) baseStart_2548080 baseEnd_2548080 := by
    simpa [prefixWord, tailWord_2548080, baseEnd_2548080] using wordTrace_append hprefix tailTrace_2548080
  have hstable : (prefixWord ++ tailWord_2548080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548080).length < 2 ^ (prefixWord ++ tailWord_2548080).sum := by decide
  have hdescent : baseEnd_2548080 < baseStart_2548080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548086 : List Nat := [5, 1, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_2548086 : Nat := 118140960795 + 2548086 * 2 ^ 59
def prefixEnd_2548086 : Nat := 4983230072969 + 3 ^ 40 * 2548086 * 2
def baseEnd_2548086 : Nat := 872261911328281890337715

theorem tailTrace_2548086 : CollatzResearch.WordTrace tailWord_2548086 prefixEnd_2548086 872261911328281890337715 := by
  unfold tailWord_2548086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5808520715420442205474007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61957554297818050191722741 5808520715420442205474007)
  ·
    refine ⟨8712781073130663308211011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5808520715420442205474007 8712781073130663308211011)
    ·
      refine ⟨13069171609695994962316517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8712781073130663308211011 13069171609695994962316517)
      ·
        refine ⟨2450469676817999055434347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13069171609695994962316517 2450469676817999055434347)
        ·
          refine ⟨3675704515226998583151521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2450469676817999055434347 3675704515226998583151521)
          ·
            refine ⟨2756778386420248937363641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3675704515226998583151521 2756778386420248937363641)
            ·
              refine ⟨2067583789815186703022731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2756778386420248937363641 2067583789815186703022731)
              ·
                refine ⟨3101375684722780054534097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2067583789815186703022731 3101375684722780054534097)
                ·
                  refine ⟨2326031763542085040900573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3101375684722780054534097 2326031763542085040900573)
                  ·
                    refine ⟨872261911328281890337715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2326031763542085040900573 872261911328281890337715)
                    ·
                      rfl

theorem cell22_2548086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_2548086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548086 prefixEnd_2548086 := by exact prefixLift 2548086
  have htrace : WordTrace (prefixWord ++ tailWord_2548086) baseStart_2548086 baseEnd_2548086 := by
    simpa [prefixWord, tailWord_2548086, baseEnd_2548086] using wordTrace_append hprefix tailTrace_2548086
  have hstable : (prefixWord ++ tailWord_2548086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548086).length < 2 ^ (prefixWord ++ tailWord_2548086).sum := by decide
  have hdescent : baseEnd_2548086 < baseStart_2548086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548093 : List Nat := [1, 4, 1, 1, 2, 4, 1, 3, 5]
def baseStart_2548093 : Nat := 118140960795 + 2548093 * 2 ^ 59
def prefixEnd_2548093 : Nat := 4983230072969 + 3 ^ 40 * 2548093 * 2
def baseEnd_2548093 : Nat := 290754769190445401804231

theorem tailTrace_2548093 : CollatzResearch.WordTrace tailWord_2548093 prefixEnd_2548093 290754769190445401804231 := by
  unfold tailWord_2548093
  simp only [CollatzResearch.WordTrace]
  refine ⟨92936586757701715483088933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61957724505134476988725955 92936586757701715483088933)
  ·
    refine ⟨17425610017069071653079175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92936586757701715483088933 17425610017069071653079175)
    ·
      refine ⟨26138415025603607479618763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17425610017069071653079175 26138415025603607479618763)
      ·
        refine ⟨39207622538405411219428145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26138415025603607479618763 39207622538405411219428145)
        ·
          refine ⟨29405716903804058414571109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39207622538405411219428145 29405716903804058414571109)
          ·
            refine ⟨5513571919463260952732083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29405716903804058414571109 5513571919463260952732083)
            ·
              refine ⟨8270357879194891429098125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5513571919463260952732083 8270357879194891429098125)
              ·
                refine ⟨3101384204698084285911797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8270357879194891429098125 3101384204698084285911797)
                ·
                  refine ⟨290754769190445401804231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3101384204698084285911797 290754769190445401804231)
                  ·
                    rfl

theorem cell22_2548093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_2548093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548093 prefixEnd_2548093 := by exact prefixLift 2548093
  have htrace : WordTrace (prefixWord ++ tailWord_2548093) baseStart_2548093 baseEnd_2548093 := by
    simpa [prefixWord, tailWord_2548093, baseEnd_2548093] using wordTrace_append hprefix tailTrace_2548093
  have hstable : (prefixWord ++ tailWord_2548093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548093).length < 2 ^ (prefixWord ++ tailWord_2548093).sum := by decide
  have hdescent : baseEnd_2548093 < baseStart_2548093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548153 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 1, 5]
def baseStart_2548153 : Nat := 118140960795 + 2548153 * 2 ^ 59
def prefixEnd_2548153 : Nat := 4983230072969 + 3 ^ 40 * 2548153 * 2
def baseEnd_2548153 : Nat := 872284846797516048912509

theorem tailTrace_2548153 : CollatzResearch.WordTrace tailWord_2548153 prefixEnd_2548153 872284846797516048912509 := by
  unfold tailWord_2548153
  simp only [CollatzResearch.WordTrace]
  refine ⟨92938775137484345730273113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61959183424989563820182075 92938775137484345730273113)
  ·
    refine ⟨69704081353113259297704835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92938775137484345730273113 69704081353113259297704835)
    ·
      refine ⟨104556122029669888946557253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69704081353113259297704835 104556122029669888946557253)
      ·
        refine ⟨19604272880563104177479485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104556122029669888946557253 19604272880563104177479485)
        ·
          refine ⟨7351602330211164066554807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19604272880563104177479485 7351602330211164066554807)
          ·
            refine ⟨11027403495316746099832211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7351602330211164066554807 11027403495316746099832211)
            ·
              refine ⟨16541105242975119149748317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11027403495316746099832211 16541105242975119149748317)
              ·
                refine ⟨6202914466115669681155619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16541105242975119149748317 6202914466115669681155619)
                ·
                  refine ⟨9304371699173504521733429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6202914466115669681155619 9304371699173504521733429)
                  ·
                    refine ⟨872284846797516048912509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9304371699173504521733429 872284846797516048912509)
                    ·
                      rfl

theorem cell22_2548153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_2548153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548153 prefixEnd_2548153 := by exact prefixLift 2548153
  have htrace : WordTrace (prefixWord ++ tailWord_2548153) baseStart_2548153 baseEnd_2548153 := by
    simpa [prefixWord, tailWord_2548153, baseEnd_2548153] using wordTrace_append hprefix tailTrace_2548153
  have hstable : (prefixWord ++ tailWord_2548153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548153).length < 2 ^ (prefixWord ++ tailWord_2548153).sum := by decide
  have hdescent : baseEnd_2548153 < baseStart_2548153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548168 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 1, 6]
def baseStart_2548168 : Nat := 118140960795 + 2548168 * 2 ^ 59
def prefixEnd_2548168 : Nat := 4983230072969 + 3 ^ 40 * 2548168 * 2
def baseEnd_2548168 : Nat := 872289981604061009787463

theorem tailTrace_2548168 : CollatzResearch.WordTrace tailWord_2548168 prefixEnd_2548168 872289981604061009787463 := by
  unfold tailWord_2548168
  simp only [CollatzResearch.WordTrace]
  refine ⟨46469661116215001646034579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61959548154953335528046105 46469661116215001646034579)
  ·
    refine ⟨69704491674322502469051869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46469661116215001646034579 69704491674322502469051869)
    ·
      refine ⟨26139184377870938425894451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69704491674322502469051869 26139184377870938425894451)
      ·
        refine ⟨39208776566806407638841677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26139184377870938425894451 39208776566806407638841677)
        ·
          refine ⟨14703291212552402864565629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39208776566806407638841677 14703291212552402864565629)
          ·
            refine ⟨5513734204707151074212111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14703291212552402864565629 5513734204707151074212111)
            ·
              refine ⟨8270601307060726611318167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5513734204707151074212111 8270601307060726611318167)
              ·
                refine ⟨12405901960591089916977251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8270601307060726611318167 12405901960591089916977251)
                ·
                  refine ⟨18608852940886634875465877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12405901960591089916977251 18608852940886634875465877)
                  ·
                    refine ⟨872289981604061009787463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18608852940886634875465877 872289981604061009787463)
                    ·
                      rfl

theorem cell22_2548168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_2548168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548168 prefixEnd_2548168 := by exact prefixLift 2548168
  have htrace : WordTrace (prefixWord ++ tailWord_2548168) baseStart_2548168 baseEnd_2548168 := by
    simpa [prefixWord, tailWord_2548168, baseEnd_2548168] using wordTrace_append hprefix tailTrace_2548168
  have hstable : (prefixWord ++ tailWord_2548168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548168).length < 2 ^ (prefixWord ++ tailWord_2548168).sum := by decide
  have hdescent : baseEnd_2548168 < baseStart_2548168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548172 : List Nat := [2, 2, 1, 4, 3, 1, 2, 3, 4]
def baseStart_2548172 : Nat := 118140960795 + 2548172 * 2 ^ 59
def prefixEnd_2548172 : Nat := 4983230072969 + 3 ^ 40 * 2548172 * 2
def baseEnd_2548172 : Nat := 290763783628602110895817

theorem tailTrace_2548172 : CollatzResearch.WordTrace tailWord_2548172 prefixEnd_2548172 290763783628602110895817 := by
  unfold tailWord_2548172
  simp only [CollatzResearch.WordTrace]
  refine ⟨46469734062207755987607385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61959645416277007983476513 46469734062207755987607385)
  ·
    refine ⟨34852300546655816990705539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46469734062207755987607385 34852300546655816990705539)
    ·
      refine ⟨52278450819983725486058309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34852300546655816990705539 52278450819983725486058309)
      ·
        refine ⟨9802209528746948528635933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52278450819983725486058309 9802209528746948528635933)
        ·
          refine ⟨3675828573280105698238475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9802209528746948528635933 3675828573280105698238475)
          ·
            refine ⟨5513742859920158547357713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3675828573280105698238475 5513742859920158547357713)
            ·
              refine ⟨4135307144940118910518285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5513742859920158547357713 4135307144940118910518285)
              ·
                refine ⟨1550740179352544591444357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4135307144940118910518285 1550740179352544591444357)
                ·
                  refine ⟨290763783628602110895817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550740179352544591444357 290763783628602110895817)
                  ·
                    rfl

theorem cell22_2548172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_2548172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548172 prefixEnd_2548172 := by exact prefixLift 2548172
  have htrace : WordTrace (prefixWord ++ tailWord_2548172) baseStart_2548172 baseEnd_2548172 := by
    simpa [prefixWord, tailWord_2548172, baseEnd_2548172] using wordTrace_append hprefix tailTrace_2548172
  have hstable : (prefixWord ++ tailWord_2548172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548172).length < 2 ^ (prefixWord ++ tailWord_2548172).sum := by decide
  have hdescent : baseEnd_2548172 < baseStart_2548172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548258 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_2548258 : Nat := 118140960795 + 2548258 * 2 ^ 59
def prefixEnd_2548258 : Nat := 4983230072969 + 3 ^ 40 * 2548258 * 2
def baseEnd_2548258 : Nat := 872320790443330775037187

theorem tailTrace_2548258 : CollatzResearch.WordTrace tailWord_2548258 prefixEnd_2548258 872320790443330775037187 := by
  unfold tailWord_2548258
  simp only [CollatzResearch.WordTrace]
  refine ⟨23235651200525987165711357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61961736534735965775230285 23235651200525987165711357)
  ·
    refine ⟨8713369200197245187141759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23235651200525987165711357 8713369200197245187141759)
    ·
      refine ⟨13070053800295867780712639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8713369200197245187141759 13070053800295867780712639)
      ·
        refine ⟨19605080700443801671068959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13070053800295867780712639 19605080700443801671068959)
        ·
          refine ⟨29407621050665702506603439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19605080700443801671068959 29407621050665702506603439)
          ·
            refine ⟨44111431575998553759905159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29407621050665702506603439 44111431575998553759905159)
            ·
              refine ⟨66167147363997830639857739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44111431575998553759905159 66167147363997830639857739)
              ·
                refine ⟨99250721045996745959786609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66167147363997830639857739 99250721045996745959786609)
                ·
                  refine ⟨74438040784497559469839957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99250721045996745959786609 74438040784497559469839957)
                  ·
                    refine ⟨872320790443330775037187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74438040784497559469839957 872320790443330775037187)
                    ·
                      rfl

theorem cell22_2548258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_2548258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548258 prefixEnd_2548258 := by exact prefixLift 2548258
  have htrace : WordTrace (prefixWord ++ tailWord_2548258) baseStart_2548258 baseEnd_2548258 := by
    simpa [prefixWord, tailWord_2548258, baseEnd_2548258] using wordTrace_append hprefix tailTrace_2548258
  have hstable : (prefixWord ++ tailWord_2548258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548258).length < 2 ^ (prefixWord ++ tailWord_2548258).sum := by decide
  have hdescent : baseEnd_2548258 < baseStart_2548258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548273 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 6]
def baseStart_2548273 : Nat := 118140960795 + 2548273 * 2 ^ 59
def prefixEnd_2548273 : Nat := 4983230072969 + 3 ^ 40 * 2548273 * 2
def baseEnd_2548273 : Nat := 290775308416625245304047

theorem tailTrace_2548273 : CollatzResearch.WordTrace tailWord_2548273 prefixEnd_2548273 290775308416625245304047 := by
  unfold tailWord_2548273
  simp only [CollatzResearch.WordTrace]
  refine ⟨92943151897049606224641473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61962101264699737483094315 92943151897049606224641473)
  ·
    refine ⟨69707363922787204668481105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92943151897049606224641473 69707363922787204668481105)
    ·
      refine ⟨52280522942090403501360829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69707363922787204668481105 52280522942090403501360829)
      ·
        refine ⟨19605196103283901313010311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52280522942090403501360829 19605196103283901313010311)
        ·
          refine ⟨29407794154925851969515467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19605196103283901313010311 29407794154925851969515467)
          ·
            refine ⟨44111691232388777954273201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29407794154925851969515467 44111691232388777954273201)
            ·
              refine ⟨33083768424291583465704901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44111691232388777954273201 33083768424291583465704901)
              ·
                refine ⟨6203206579554671899819669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33083768424291583465704901 6203206579554671899819669)
                ·
                  refine ⟨290775308416625245304047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6203206579554671899819669 290775308416625245304047)
                  ·
                    rfl

theorem cell22_2548273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 6].length) (baseStart_2548273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548273 prefixEnd_2548273 := by exact prefixLift 2548273
  have htrace : WordTrace (prefixWord ++ tailWord_2548273) baseStart_2548273 baseEnd_2548273 := by
    simpa [prefixWord, tailWord_2548273, baseEnd_2548273] using wordTrace_append hprefix tailTrace_2548273
  have hstable : (prefixWord ++ tailWord_2548273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548273).length < 2 ^ (prefixWord ++ tailWord_2548273).sum := by decide
  have hdescent : baseEnd_2548273 < baseStart_2548273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548288 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 3, 5]
def baseStart_2548288 : Nat := 118140960795 + 2548288 * 2 ^ 59
def prefixEnd_2548288 : Nat := 4983230072969 + 3 ^ 40 * 2548288 * 2
def baseEnd_2548288 : Nat := 872331060056420696787095

theorem tailTrace_2548288 : CollatzResearch.WordTrace tailWord_2548288 prefixEnd_2548288 872331060056420696787095 := by
  unfold tailWord_2548288
  simp only [CollatzResearch.WordTrace]
  refine ⟨46471849495997631893218759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61962465994663509190958345 46471849495997631893218759)
  ·
    refine ⟨69707774243996447839828139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46471849495997631893218759 69707774243996447839828139)
    ·
      refine ⟨104561661365994671759742209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69707774243996447839828139 104561661365994671759742209)
      ·
        refine ⟨78421246024496003819806657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104561661365994671759742209 78421246024496003819806657)
        ·
          refine ⟨58815934518372002864854993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78421246024496003819806657 58815934518372002864854993)
          ·
            refine ⟨44111950888779002148641245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58815934518372002864854993 44111950888779002148641245)
            ·
              refine ⟨16541981583292125805740467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44111950888779002148641245 16541981583292125805740467)
              ·
                refine ⟨24812972374938188708610701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16541981583292125805740467 24812972374938188708610701)
                ·
                  refine ⟨9304864640601820765729013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24812972374938188708610701 9304864640601820765729013)
                  ·
                    refine ⟨872331060056420696787095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9304864640601820765729013 872331060056420696787095)
                    ·
                      rfl

theorem cell22_2548288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_2548288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548288 prefixEnd_2548288 := by exact prefixLift 2548288
  have htrace : WordTrace (prefixWord ++ tailWord_2548288) baseStart_2548288 baseEnd_2548288 := by
    simpa [prefixWord, tailWord_2548288, baseEnd_2548288] using wordTrace_append hprefix tailTrace_2548288
  have hstable : (prefixWord ++ tailWord_2548288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548288).length < 2 ^ (prefixWord ++ tailWord_2548288).sum := by decide
  have hdescent : baseEnd_2548288 < baseStart_2548288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548444 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2548444 : Nat := 118140960795 + 2548444 * 2 ^ 59
def prefixEnd_2548444 : Nat := 4983230072969 + 3 ^ 40 * 2548444 * 2
def baseEnd_2548444 : Nat := 872384462044488289886617

theorem tailTrace_2548444 : CollatzResearch.WordTrace tailWord_2548444 prefixEnd_2548444 872384462044488289886617 := by
  unfold tailWord_2548444
  simp only [CollatzResearch.WordTrace]
  refine ⟨46474694389715051214558193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61966259186286734952744257 46474694389715051214558193)
  ·
    refine ⟨34856020792286288410918645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46474694389715051214558193 34856020792286288410918645)
    ·
      refine ⟨3267751949276839538523623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34856020792286288410918645 3267751949276839538523623)
      ·
        refine ⟨4901627923915259307785435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3267751949276839538523623 4901627923915259307785435)
        ·
          refine ⟨7352441885872888961678153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4901627923915259307785435 7352441885872888961678153)
          ·
            refine ⟨5514331414404666721258615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7352441885872888961678153 5514331414404666721258615)
            ·
              refine ⟨8271497121607000081887923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5514331414404666721258615 8271497121607000081887923)
              ·
                refine ⟨12407245682410500122831885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8271497121607000081887923 12407245682410500122831885)
                ·
                  refine ⟨4652717130903937546061957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12407245682410500122831885 4652717130903937546061957)
                  ·
                    refine ⟨872384462044488289886617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4652717130903937546061957 872384462044488289886617)
                    ·
                      rfl

theorem cell22_2548444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2548444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548444 prefixEnd_2548444 := by exact prefixLift 2548444
  have htrace : WordTrace (prefixWord ++ tailWord_2548444) baseStart_2548444 baseEnd_2548444 := by
    simpa [prefixWord, tailWord_2548444, baseEnd_2548444] using wordTrace_append hprefix tailTrace_2548444
  have hstable : (prefixWord ++ tailWord_2548444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548444).length < 2 ^ (prefixWord ++ tailWord_2548444).sum := by decide
  have hdescent : baseEnd_2548444 < baseStart_2548444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548469 : List Nat := [1, 3, 6, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2548469 : Nat := 118140960795 + 2548469 * 2 ^ 59
def prefixEnd_2548469 : Nat := 4983230072969 + 3 ^ 40 * 2548469 * 2
def baseEnd_2548469 : Nat := 872393020055396558011541

theorem tailTrace_2548469 : CollatzResearch.WordTrace tailWord_2548469 prefixEnd_2548469 872393020055396558011541 := by
  unfold tailWord_2548469
  simp only [CollatzResearch.WordTrace]
  refine ⟨92950300604339531698776461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61966867069559687799184307 92950300604339531698776461)
  ·
    refine ⟨34856362726627324387041173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92950300604339531698776461 34856362726627324387041173)
    ·
      refine ⟨1633892002810655830642555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34856362726627324387041173 1633892002810655830642555)
      ·
        refine ⟨2450838004215983745963833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1633892002810655830642555 2450838004215983745963833)
        ·
          refine ⟨1838128503161987809472875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2450838004215983745963833 1838128503161987809472875)
          ·
            refine ⟨2757192754742981714209313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838128503161987809472875 2757192754742981714209313)
            ·
              refine ⟨2067894566057236285656985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2757192754742981714209313 2067894566057236285656985)
              ·
                refine ⟨1550920924542927214242739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067894566057236285656985 1550920924542927214242739)
                ·
                  refine ⟨2326381386814390821364109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550920924542927214242739 2326381386814390821364109)
                  ·
                    refine ⟨872393020055396558011541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2326381386814390821364109 872393020055396558011541)
                    ·
                      rfl

theorem cell22_2548469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2548469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548469 prefixEnd_2548469 := by exact prefixLift 2548469
  have htrace : WordTrace (prefixWord ++ tailWord_2548469) baseStart_2548469 baseEnd_2548469 := by
    simpa [prefixWord, tailWord_2548469, baseEnd_2548469] using wordTrace_append hprefix tailTrace_2548469
  have hstable : (prefixWord ++ tailWord_2548469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548469).length < 2 ^ (prefixWord ++ tailWord_2548469).sum := by decide
  have hdescent : baseEnd_2548469 < baseStart_2548469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548476 : List Nat := [2, 2, 2, 1, 3, 4, 2, 2, 4]
def baseStart_2548476 : Nat := 118140960795 + 2548476 * 2 ^ 59
def prefixEnd_2548476 : Nat := 4983230072969 + 3 ^ 40 * 2548476 * 2
def baseEnd_2548476 : Nat := 290798472099483624362173

theorem tailTrace_2548476 : CollatzResearch.WordTrace tailWord_2548476 prefixEnd_2548476 290798472099483624362173 := by
  unfold tailWord_2548476
  simp only [CollatzResearch.WordTrace]
  refine ⟨46475277957657085947140641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61967037276876114596187521 46475277957657085947140641)
  ·
    refine ⟨34856458468242814460355481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46475277957657085947140641 34856458468242814460355481)
    ·
      refine ⟨26142343851182110845266611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34856458468242814460355481 26142343851182110845266611)
      ·
        refine ⟨39213515776773166267899917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26142343851182110845266611 39213515776773166267899917)
        ·
          refine ⟨14705068416289937350462469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39213515776773166267899917 14705068416289937350462469)
          ·
            refine ⟨2757200328054363253211713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14705068416289937350462469 2757200328054363253211713)
            ·
              refine ⟨2067900246040772439908785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2757200328054363253211713 2067900246040772439908785)
              ·
                refine ⟨1550925184530579329931589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067900246040772439908785 1550925184530579329931589)
                ·
                  refine ⟨290798472099483624362173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550925184530579329931589 290798472099483624362173)
                  ·
                    rfl

theorem cell22_2548476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_2548476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548476 prefixEnd_2548476 := by exact prefixLift 2548476
  have htrace : WordTrace (prefixWord ++ tailWord_2548476) baseStart_2548476 baseEnd_2548476 := by
    simpa [prefixWord, tailWord_2548476, baseEnd_2548476] using wordTrace_append hprefix tailTrace_2548476
  have hstable : (prefixWord ++ tailWord_2548476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548476).length < 2 ^ (prefixWord ++ tailWord_2548476).sum := by decide
  have hdescent : baseEnd_2548476 < baseStart_2548476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548487 : List Nat := [1, 1, 4, 4, 1, 1, 3, 7]
def baseStart_2548487 : Nat := 118140960795 + 2548487 * 2 ^ 59
def prefixEnd_2548487 : Nat := 4983230072969 + 3 ^ 40 * 2548487 * 2
def baseEnd_2548487 : Nat := 96933242424805612340165

theorem tailTrace_2548487 : CollatzResearch.WordTrace tailWord_2548487 prefixEnd_2548487 96933242424805612340165 := by
  unfold tailWord_2548487
  simp only [CollatzResearch.WordTrace]
  refine ⟨92950957118274320772931715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61967304745516213848621143 92950957118274320772931715)
  ·
    refine ⟨139426435677411481159397573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92950957118274320772931715 139426435677411481159397573)
    ·
      refine ⟨26142456689514652717387045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139426435677411481159397573 26142456689514652717387045)
      ·
        refine ⟨4901710629283997384510071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26142456689514652717387045 4901710629283997384510071)
        ·
          refine ⟨7352565943925996076765107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4901710629283997384510071 7352565943925996076765107)
          ·
            refine ⟨11028848915888994115147661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7352565943925996076765107 11028848915888994115147661)
            ·
              refine ⟨4135818343458372793180373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11028848915888994115147661 4135818343458372793180373)
              ·
                refine ⟨96933242424805612340165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4135818343458372793180373 96933242424805612340165)
                ·
                  rfl

theorem cell22_2548487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 7].length) (baseStart_2548487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548487 prefixEnd_2548487 := by exact prefixLift 2548487
  have htrace : WordTrace (prefixWord ++ tailWord_2548487) baseStart_2548487 baseEnd_2548487 := by
    simpa [prefixWord, tailWord_2548487, baseEnd_2548487] using wordTrace_append hprefix tailTrace_2548487
  have hstable : (prefixWord ++ tailWord_2548487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548487).length < 2 ^ (prefixWord ++ tailWord_2548487).sum := by decide
  have hdescent : baseEnd_2548487 < baseStart_2548487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548515 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 7]
def baseStart_2548515 : Nat := 118140960795 + 2548515 * 2 ^ 59
def prefixEnd_2548515 : Nat := 4983230072969 + 3 ^ 40 * 2548515 * 2
def baseEnd_2548515 : Nat := 290802922265155923787133

theorem tailTrace_2548515 : CollatzResearch.WordTrace tailWord_2548515 prefixEnd_2548515 290802922265155923787133 := by
  unfold tailWord_2548515
  simp only [CollatzResearch.WordTrace]
  refine ⟨92951978362172881554950999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61967985574781921036633999 92951978362172881554950999)
  ·
    refine ⟨139427967543259322332426499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92951978362172881554950999 139427967543259322332426499)
    ·
      refine ⟨209141951314888983498639749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139427967543259322332426499 209141951314888983498639749)
      ·
        refine ⟨39214115871541684405994953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209141951314888983498639749 39214115871541684405994953)
        ·
          refine ⟨29410586903656263304496215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39214115871541684405994953 29410586903656263304496215)
          ·
            refine ⟨44115880355484394956744323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29410586903656263304496215 44115880355484394956744323)
            ·
              refine ⟨66173820533226592435116485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44115880355484394956744323 66173820533226592435116485)
              ·
                refine ⟨12407591349979986081584341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66173820533226592435116485 12407591349979986081584341)
                ·
                  refine ⟨290802922265155923787133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12407591349979986081584341 290802922265155923787133)
                  ·
                    rfl

theorem cell22_2548515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 7].length) (baseStart_2548515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548515 prefixEnd_2548515 := by exact prefixLift 2548515
  have htrace : WordTrace (prefixWord ++ tailWord_2548515) baseStart_2548515 baseEnd_2548515 := by
    simpa [prefixWord, tailWord_2548515, baseEnd_2548515] using wordTrace_append hprefix tailTrace_2548515
  have hstable : (prefixWord ++ tailWord_2548515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548515).length < 2 ^ (prefixWord ++ tailWord_2548515).sum := by decide
  have hdescent : baseEnd_2548515 < baseStart_2548515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548525 : List Nat := [1, 5, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2548525 : Nat := 118140960795 + 2548525 * 2 ^ 59
def prefixEnd_2548525 : Nat := 4983230072969 + 3 ^ 40 * 2548525 * 2
def baseEnd_2548525 : Nat := 872412189999831078611369

theorem tailTrace_2548525 : CollatzResearch.WordTrace tailWord_2548525 prefixEnd_2548525 872412189999831078611369 := by
  unfold tailWord_2548525
  simp only [CollatzResearch.WordTrace]
  refine ⟨92952343092136653262815029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61968228728091102175210019 92952343092136653262815029)
  ·
    refine ⟨8714282164887811243388909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92952343092136653262815029 8714282164887811243388909)
    ·
      refine ⟨3267855811832929216270841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8714282164887811243388909 3267855811832929216270841)
      ·
        refine ⟨2450891858874696912203131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3267855811832929216270841 2450891858874696912203131)
        ·
          refine ⟨3676337788312045368304697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2450891858874696912203131 3676337788312045368304697)
          ·
            refine ⟨2757253341234034026228523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3676337788312045368304697 2757253341234034026228523)
            ·
              refine ⟨4135880011851051039342785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2757253341234034026228523 4135880011851051039342785)
              ·
                refine ⟨3101910008888288279507089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4135880011851051039342785 3101910008888288279507089)
                ·
                  refine ⟨2326432506666216209630317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3101910008888288279507089 2326432506666216209630317)
                  ·
                    refine ⟨872412189999831078611369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2326432506666216209630317 872412189999831078611369)
                    ·
                      rfl

theorem cell22_2548525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2548525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548525 prefixEnd_2548525 := by exact prefixLift 2548525
  have htrace : WordTrace (prefixWord ++ tailWord_2548525) baseStart_2548525 baseEnd_2548525 := by
    simpa [prefixWord, tailWord_2548525, baseEnd_2548525] using wordTrace_append hprefix tailTrace_2548525
  have hstable : (prefixWord ++ tailWord_2548525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548525).length < 2 ^ (prefixWord ++ tailWord_2548525).sum := by decide
  have hdescent : baseEnd_2548525 < baseStart_2548525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548579 : List Nat := [1, 1, 1, 5, 3, 1, 2, 3, 1, 4]
def baseStart_2548579 : Nat := 118140960795 + 2548579 * 2 ^ 59
def prefixEnd_2548579 : Nat := 4983230072969 + 3 ^ 40 * 2548579 * 2
def baseEnd_2548579 : Nat := 872430675303392937761203

theorem tailTrace_2548579 : CollatzResearch.WordTrace tailWord_2548579 prefixEnd_2548579 872430675303392937761203 := by
  unfold tailWord_2548579
  simp only [CollatzResearch.WordTrace]
  refine ⟨92954312633941020485280791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61969541755960680323520527 92954312633941020485280791)
  ·
    refine ⟨139431468950911530727921187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92954312633941020485280791 139431468950911530727921187)
    ·
      refine ⟨209147203426367296091881781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139431468950911530727921187 209147203426367296091881781)
      ·
        refine ⟨19607550321221934008613917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 209147203426367296091881781 19607550321221934008613917)
        ·
          refine ⟨7352831370458225253230219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19607550321221934008613917 7352831370458225253230219)
          ·
            refine ⟨11029247055687337879845329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7352831370458225253230219 11029247055687337879845329)
            ·
              refine ⟨8271935291765503409883997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11029247055687337879845329 8271935291765503409883997)
              ·
                refine ⟨3101975734412063778706499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8271935291765503409883997 3101975734412063778706499)
                ·
                  refine ⟨4652963601618095668059749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3101975734412063778706499 4652963601618095668059749)
                  ·
                    refine ⟨872430675303392937761203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4652963601618095668059749 872430675303392937761203)
                    ·
                      rfl

theorem cell22_2548579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 4].length) (baseStart_2548579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548579 prefixEnd_2548579 := by exact prefixLift 2548579
  have htrace : WordTrace (prefixWord ++ tailWord_2548579) baseStart_2548579 baseEnd_2548579 := by
    simpa [prefixWord, tailWord_2548579, baseEnd_2548579] using wordTrace_append hprefix tailTrace_2548579
  have hstable : (prefixWord ++ tailWord_2548579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548579).length < 2 ^ (prefixWord ++ tailWord_2548579).sum := by decide
  have hdescent : baseEnd_2548579 < baseStart_2548579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548594 : List Nat := [3, 2, 1, 2, 1, 1, 2, 6, 4]
def baseStart_2548594 : Nat := 118140960795 + 2548594 * 2 ^ 59
def prefixEnd_2548594 : Nat := 4983230072969 + 3 ^ 40 * 2548594 * 2
def baseEnd_2548594 : Nat := 290811936703312632878719

theorem tailTrace_2548594 : CollatzResearch.WordTrace tailWord_2548594 prefixEnd_2548594 290811936703312632878719 := by
  unfold tailWord_2548594
  simp only [CollatzResearch.WordTrace]
  refine ⟨23238714932221669511769209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61969906485924452031384557 23238714932221669511769209)
  ·
    refine ⟨17429036199166252133826907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23238714932221669511769209 17429036199166252133826907)
    ·
      refine ⟨26143554298749378200740361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17429036199166252133826907 26143554298749378200740361)
      ·
        refine ⟨19607665724062033650555271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26143554298749378200740361 19607665724062033650555271)
        ·
          refine ⟨29411498586093050475832907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19607665724062033650555271 29411498586093050475832907)
          ·
            refine ⟨44117247879139575713749361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29411498586093050475832907 44117247879139575713749361)
            ·
              refine ⟨33087935909354681785312021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44117247879139575713749361 33087935909354681785312021)
              ·
                refine ⟨1550996995751000708686501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33087935909354681785312021 1550996995751000708686501)
                ·
                  refine ⟨290811936703312632878719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1550996995751000708686501 290811936703312632878719)
                  ·
                    rfl

theorem cell22_2548594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_2548594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548594 prefixEnd_2548594 := by exact prefixLift 2548594
  have htrace : WordTrace (prefixWord ++ tailWord_2548594) baseStart_2548594 baseEnd_2548594 := by
    simpa [prefixWord, tailWord_2548594, baseEnd_2548594] using wordTrace_append hprefix tailTrace_2548594
  have hstable : (prefixWord ++ tailWord_2548594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548594).length < 2 ^ (prefixWord ++ tailWord_2548594).sum := by decide
  have hdescent : baseEnd_2548594 < baseStart_2548594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548626 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_2548626 : Nat := 118140960795 + 2548626 * 2 ^ 59
def prefixEnd_2548626 : Nat := 4983230072969 + 3 ^ 40 * 2548626 * 2
def baseEnd_2548626 : Nat := 872446764363900481836059

theorem tailTrace_2548626 : CollatzResearch.WordTrace tailWord_2548626 prefixEnd_2548626 872446764363900481836059 := by
  unfold tailWord_2548626
  simp only [CollatzResearch.WordTrace]
  refine ⟨23239006716192686878060433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61970684576513831674827821 23239006716192686878060433)
  ·
    refine ⟨17429255037144515158545325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23239006716192686878060433 17429255037144515158545325)
    ·
      refine ⟨6535970638929193184454497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17429255037144515158545325 6535970638929193184454497)
      ·
        refine ⟨4901977979196894888340873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6535970638929193184454497 4901977979196894888340873)
        ·
          refine ⟨3676483484397671166255655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4901977979196894888340873 3676483484397671166255655)
          ·
            refine ⟨5514725226596506749383483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3676483484397671166255655 5514725226596506749383483)
            ·
              refine ⟨8272087839894760124075225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5514725226596506749383483 8272087839894760124075225)
              ·
                refine ⟨6204065879921070093056419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8272087839894760124075225 6204065879921070093056419)
                ·
                  refine ⟨9306098819881605139584629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6204065879921070093056419 9306098819881605139584629)
                  ·
                    refine ⟨872446764363900481836059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9306098819881605139584629 872446764363900481836059)
                    ·
                      rfl

theorem cell22_2548626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_2548626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548626 prefixEnd_2548626 := by exact prefixLift 2548626
  have htrace : WordTrace (prefixWord ++ tailWord_2548626) baseStart_2548626 baseEnd_2548626 := by
    simpa [prefixWord, tailWord_2548626, baseEnd_2548626] using wordTrace_append hprefix tailTrace_2548626
  have hstable : (prefixWord ++ tailWord_2548626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548626).length < 2 ^ (prefixWord ++ tailWord_2548626).sum := by decide
  have hdescent : baseEnd_2548626 < baseStart_2548626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548682 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 3, 7]
def baseStart_2548682 : Nat := 118140960795 + 2548682 * 2 ^ 59
def prefixEnd_2548682 : Nat := 4983230072969 + 3 ^ 40 * 2548682 * 2
def baseEnd_2548682 : Nat := 872465934308335002435887

theorem tailTrace_2548682 : CollatzResearch.WordTrace tailWord_2548682 prefixEnd_2548682 872465934308335002435887 := by
  unfold tailWord_2548682
  simp only [CollatzResearch.WordTrace]
  refine ⟨23239517338141967269070075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61972046235045246050853533 23239517338141967269070075)
  ·
    refine ⟨34859276007212950903605113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23239517338141967269070075 34859276007212950903605113)
    ·
      refine ⟨26144457005409713177703835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34859276007212950903605113 26144457005409713177703835)
      ·
        refine ⟨39216685508114569766555753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26144457005409713177703835 39216685508114569766555753)
        ·
          refine ⟨29412514131085927324916815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39216685508114569766555753 29412514131085927324916815)
          ·
            refine ⟨44118771196628890987375223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29412514131085927324916815 44118771196628890987375223)
            ·
              refine ⟨66178156794943336481062835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44118771196628890987375223 66178156794943336481062835)
              ·
                refine ⟨99267235192415004721594253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66178156794943336481062835 99267235192415004721594253)
                ·
                  refine ⟨37225213197155626770597845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99267235192415004721594253 37225213197155626770597845)
                  ·
                    refine ⟨872465934308335002435887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37225213197155626770597845 872465934308335002435887)
                    ·
                      rfl

theorem cell22_2548682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_2548682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548682 prefixEnd_2548682 := by exact prefixLift 2548682
  have htrace : WordTrace (prefixWord ++ tailWord_2548682) baseStart_2548682 baseEnd_2548682 := by
    simpa [prefixWord, tailWord_2548682, baseEnd_2548682] using wordTrace_append hprefix tailTrace_2548682
  have hstable : (prefixWord ++ tailWord_2548682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548682).length < 2 ^ (prefixWord ++ tailWord_2548682).sum := by decide
  have hdescent : baseEnd_2548682 < baseStart_2548682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548701 : List Nat := [1, 4, 3, 1, 2, 1, 3, 2, 5]
def baseStart_2548701 : Nat := 118140960795 + 2548701 * 2 ^ 59
def prefixEnd_2548701 : Nat := 4983230072969 + 3 ^ 40 * 2548701 * 2
def baseEnd_2548701 : Nat := 290824146132208428736943

theorem tailTrace_2548701 : CollatzResearch.WordTrace tailWord_2548701 prefixEnd_2548701 290824146132208428736943 := by
  unfold tailWord_2548701
  simp only [CollatzResearch.WordTrace]
  refine ⟨92958762339499035321221957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61972508226332690214147971 92958762339499035321221957)
  ·
    refine ⟨17429767938656069122729117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92958762339499035321221957 17429767938656069122729117)
    ·
      refine ⟨6536162976996025921023419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17429767938656069122729117 6536162976996025921023419)
      ·
        refine ⟨9804244465494038881535129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6536162976996025921023419 9804244465494038881535129)
        ·
          refine ⟨7353183349120529161151347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9804244465494038881535129 7353183349120529161151347)
          ·
            refine ⟨11029775023680793741727021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7353183349120529161151347 11029775023680793741727021)
            ·
              refine ⟨4136165633880297653147633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11029775023680793741727021 4136165633880297653147633)
              ·
                refine ⟨3102124225410223239860725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4136165633880297653147633 3102124225410223239860725)
                ·
                  refine ⟨290824146132208428736943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3102124225410223239860725 290824146132208428736943)
                  ·
                    rfl

theorem cell22_2548701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_2548701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548701 prefixEnd_2548701 := by exact prefixLift 2548701
  have htrace : WordTrace (prefixWord ++ tailWord_2548701) baseStart_2548701 baseEnd_2548701 := by
    simpa [prefixWord, tailWord_2548701, baseEnd_2548701] using wordTrace_append hprefix tailTrace_2548701
  have hstable : (prefixWord ++ tailWord_2548701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548701).length < 2 ^ (prefixWord ++ tailWord_2548701).sum := by decide
  have hdescent : baseEnd_2548701 < baseStart_2548701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548718 : List Nat := [4, 1, 2, 1, 4, 1, 3, 1, 5]
def baseStart_2548718 : Nat := 118140960795 + 2548718 * 2 ^ 59
def prefixEnd_2548718 : Nat := 4983230072969 + 3 ^ 40 * 2548718 * 2
def baseEnd_2548718 : Nat := 290826085948014302845259

theorem tailTrace_2548718 : CollatzResearch.WordTrace tailWord_2548718 prefixEnd_2548718 290826085948014302845259 := by
  unfold tailWord_2548718
  simp only [CollatzResearch.WordTrace]
  refine ⟨11619922797554680903073851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61972921586958298149727205 11619922797554680903073851)
  ·
    refine ⟨17429884196332021354610777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11619922797554680903073851 17429884196332021354610777)
    ·
      refine ⟨13072413147249016015958083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17429884196332021354610777 13072413147249016015958083)
      ·
        refine ⟨19608619720873524023937125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13072413147249016015958083 19608619720873524023937125)
        ·
          refine ⟨3676616197663785754488211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19608619720873524023937125 3676616197663785754488211)
          ·
            refine ⟨5514924296495678631732317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3676616197663785754488211 5514924296495678631732317)
            ·
              refine ⟨2068096611185879486899619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5514924296495678631732317 2068096611185879486899619)
              ·
                refine ⟨3102144916778819230349429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2068096611185879486899619 3102144916778819230349429)
                ·
                  refine ⟨290826085948014302845259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3102144916778819230349429 290826085948014302845259)
                  ·
                    rfl

theorem cell22_2548718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_2548718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548718 prefixEnd_2548718 := by exact prefixLift 2548718
  have htrace : WordTrace (prefixWord ++ tailWord_2548718) baseStart_2548718 baseEnd_2548718 := by
    simpa [prefixWord, tailWord_2548718, baseEnd_2548718] using wordTrace_append hprefix tailTrace_2548718
  have hstable : (prefixWord ++ tailWord_2548718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548718).length < 2 ^ (prefixWord ++ tailWord_2548718).sum := by decide
  have hdescent : baseEnd_2548718 < baseStart_2548718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548724 : List Nat := [2, 6, 2, 1, 2, 1, 2, 6]
def baseStart_2548724 : Nat := 118140960795 + 2548724 * 2 ^ 59
def prefixEnd_2548724 : Nat := 4983230072969 + 3 ^ 40 * 2548724 * 2
def baseEnd_2548724 : Nat := 96942256862962321431751

theorem tailTrace_2548724 : CollatzResearch.WordTrace tailWord_2548724 prefixEnd_2548724 96942256862962321431751 := by
  unfold tailWord_2548724
  simp only [CollatzResearch.WordTrace]
  refine ⟨46479800609207855124654613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61973067478943806832872817 46479800609207855124654613)
  ·
    refine ⟨2178740653556618208968185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46479800609207855124654613 2178740653556618208968185)
    ·
      refine ⟨1634055490167463656726139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2178740653556618208968185 1634055490167463656726139)
      ·
        refine ⟨2451083235251195485089209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1634055490167463656726139 2451083235251195485089209)
        ·
          refine ⟨1838312426438396613816907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2451083235251195485089209 1838312426438396613816907)
          ·
            refine ⟨2757468639657594920725361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838312426438396613816907 2757468639657594920725361)
            ·
              refine ⟨2068101479743196190544021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2757468639657594920725361 2068101479743196190544021)
              ·
                refine ⟨96942256862962321431751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2068101479743196190544021 96942256862962321431751)
                ·
                  rfl

theorem cell22_2548724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 6].length) (baseStart_2548724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548724 prefixEnd_2548724 := by exact prefixLift 2548724
  have htrace : WordTrace (prefixWord ++ tailWord_2548724) baseStart_2548724 baseEnd_2548724 := by
    simpa [prefixWord, tailWord_2548724, baseEnd_2548724] using wordTrace_append hprefix tailTrace_2548724
  have hstable : (prefixWord ++ tailWord_2548724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548724).length < 2 ^ (prefixWord ++ tailWord_2548724).sum := by decide
  have hdescent : baseEnd_2548724 < baseStart_2548724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548819 : List Nat := [1, 1, 1, 2, 1, 1, 2, 8, 5]
def baseStart_2548819 : Nat := 118140960795 + 2548819 * 2 ^ 59
def prefixEnd_2548819 : Nat := 4983230072969 + 3 ^ 40 * 2548819 * 2
def baseEnd_2548819 : Nat := 290837610736037437253489

theorem tailTrace_2548819 : CollatzResearch.WordTrace tailWord_2548819 prefixEnd_2548819 290837610736037437253489 := by
  unfold tailWord_2548819
  simp only [CollatzResearch.WordTrace]
  refine ⟨92963066153071541474017511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61975377435381027649345007 92963066153071541474017511)
  ·
    refine ⟨139444599229607312211026267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92963066153071541474017511 139444599229607312211026267)
    ·
      refine ⟨209166898844410968316539401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139444599229607312211026267 209166898844410968316539401)
      ·
        refine ⟨156875174133308226237404551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209166898844410968316539401 156875174133308226237404551)
        ·
          refine ⟨235312761199962339356106827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156875174133308226237404551 235312761199962339356106827)
          ·
            refine ⟨352969141799943509034160241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235312761199962339356106827 352969141799943509034160241)
            ·
              refine ⟨264726856349957631775620181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352969141799943509034160241 264726856349957631775620181)
              ·
                refine ⟨3102267847851065997370549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 264726856349957631775620181 3102267847851065997370549)
                ·
                  refine ⟨290837610736037437253489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3102267847851065997370549 290837610736037437253489)
                  ·
                    rfl

theorem cell22_2548819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 5].length) (baseStart_2548819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548819 prefixEnd_2548819 := by exact prefixLift 2548819
  have htrace : WordTrace (prefixWord ++ tailWord_2548819) baseStart_2548819 baseEnd_2548819 := by
    simpa [prefixWord, tailWord_2548819, baseEnd_2548819] using wordTrace_append hprefix tailTrace_2548819
  have hstable : (prefixWord ++ tailWord_2548819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548819).length < 2 ^ (prefixWord ++ tailWord_2548819).sum := by decide
  have hdescent : baseEnd_2548819 < baseStart_2548819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548840 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 3, 3]
def baseStart_2548840 : Nat := 118140960795 + 2548840 * 2 ^ 59
def prefixEnd_2548840 : Nat := 4983230072969 + 3 ^ 40 * 2548840 * 2
def baseEnd_2548840 : Nat := 872520020937275256985403

theorem tailTrace_2548840 : CollatzResearch.WordTrace tailWord_2548840 prefixEnd_2548840 872520020937275256985403 := by
  unfold tailWord_2548840
  simp only [CollatzResearch.WordTrace]
  refine ⟨46481916042997731030265987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61975888057330308040354649 46481916042997731030265987)
  ·
    refine ⟨69722874064496596545398981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46481916042997731030265987 69722874064496596545398981)
    ·
      refine ⟨13073038887093111852262309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69722874064496596545398981 13073038887093111852262309)
      ·
        refine ⟨2451194791329958472299183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13073038887093111852262309 2451194791329958472299183)
        ·
          refine ⟨3676792186994937708448775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451194791329958472299183 3676792186994937708448775)
          ·
            refine ⟨5515188280492406562673163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3676792186994937708448775 5515188280492406562673163)
            ·
              refine ⟨8272782420738609844009745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5515188280492406562673163 8272782420738609844009745)
              ·
                refine ⟨6204586815553957383007309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8272782420738609844009745 6204586815553957383007309)
                ·
                  refine ⟨2326720055832734018627741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6204586815553957383007309 2326720055832734018627741)
                  ·
                    refine ⟨872520020937275256985403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2326720055832734018627741 872520020937275256985403)
                    ·
                      rfl

theorem cell22_2548840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_2548840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548840 prefixEnd_2548840 := by exact prefixLift 2548840
  have htrace : WordTrace (prefixWord ++ tailWord_2548840) baseStart_2548840 baseEnd_2548840 := by
    simpa [prefixWord, tailWord_2548840, baseEnd_2548840] using wordTrace_append hprefix tailTrace_2548840
  have hstable : (prefixWord ++ tailWord_2548840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548840).length < 2 ^ (prefixWord ++ tailWord_2548840).sum := by decide
  have hdescent : baseEnd_2548840 < baseStart_2548840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548913 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 4, 3]
def baseStart_2548913 : Nat := 118140960795 + 2548913 * 2 ^ 59
def prefixEnd_2548913 : Nat := 4983230072969 + 3 ^ 40 * 2548913 * 2
def baseEnd_2548913 : Nat := 872545010329127399910179

theorem tailTrace_2548913 : CollatzResearch.WordTrace tailWord_2548913 prefixEnd_2548913 872545010329127399910179 := by
  unfold tailWord_2548913
  simp only [CollatzResearch.WordTrace]
  refine ⟨92966494614730995527939393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61977663076487330351959595 92966494614730995527939393)
  ·
    refine ⟨69724870961048246645954545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92966494614730995527939393 69724870961048246645954545)
    ·
      refine ⟨52293653220786184984465909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69724870961048246645954545 52293653220786184984465909)
      ·
        refine ⟨4902529989448704842293679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52293653220786184984465909 4902529989448704842293679)
        ·
          refine ⟨7353794984173057263440519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4902529989448704842293679 7353794984173057263440519)
          ·
            refine ⟨11030692476259585895160779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7353794984173057263440519 11030692476259585895160779)
            ·
              refine ⟨16546038714389378842741169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11030692476259585895160779 16546038714389378842741169)
              ·
                refine ⟨12409529035792034132055877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16546038714389378842741169 12409529035792034132055877)
                ·
                  refine ⟨2326786694211006399760477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12409529035792034132055877 2326786694211006399760477)
                  ·
                    refine ⟨872545010329127399910179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2326786694211006399760477 872545010329127399910179)
                    ·
                      rfl

theorem cell22_2548913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_2548913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548913 prefixEnd_2548913 := by exact prefixLift 2548913
  have htrace : WordTrace (prefixWord ++ tailWord_2548913) baseStart_2548913 baseEnd_2548913 := by
    simpa [prefixWord, tailWord_2548913, baseEnd_2548913] using wordTrace_append hprefix tailTrace_2548913
  have hstable : (prefixWord ++ tailWord_2548913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548913).length < 2 ^ (prefixWord ++ tailWord_2548913).sum := by decide
  have hdescent : baseEnd_2548913 < baseStart_2548913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548926 : List Nat := [4, 2, 1, 1, 3, 1, 10]
def baseStart_2548926 : Nat := 118140960795 + 2548926 * 2 ^ 59
def prefixEnd_2548926 : Nat := 4983230072969 + 3 ^ 40 * 2548926 * 2
def baseEnd_2548926 : Nat := 32316646684992581456857

theorem tailTrace_2548926 : CollatzResearch.WordTrace tailWord_2548926 prefixEnd_2548926 32316646684992581456857 := by
  unfold tailWord_2548926
  simp only [CollatzResearch.WordTrace]
  refine ⟨11620871095460487343520329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61977979175789265832108421 11620871095460487343520329)
  ·
    refine ⟨8715653321595365507640247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11620871095460487343520329 8715653321595365507640247)
    ·
      refine ⟨13073479982393048261460371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8715653321595365507640247 13073479982393048261460371)
      ·
        refine ⟨19610219973589572392190557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13073479982393048261460371 19610219973589572392190557)
        ·
          refine ⟨7353832490096089647071459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19610219973589572392190557 7353832490096089647071459)
          ·
            refine ⟨11030748735144134470607189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7353832490096089647071459 11030748735144134470607189)
            ·
              refine ⟨32316646684992581456857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11030748735144134470607189 32316646684992581456857)
              ·
                rfl

theorem cell22_2548926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 10].length) (baseStart_2548926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548926 prefixEnd_2548926 := by exact prefixLift 2548926
  have htrace : WordTrace (prefixWord ++ tailWord_2548926) baseStart_2548926 baseEnd_2548926 := by
    simpa [prefixWord, tailWord_2548926, baseEnd_2548926] using wordTrace_append hprefix tailTrace_2548926
  have hstable : (prefixWord ++ tailWord_2548926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548926).length < 2 ^ (prefixWord ++ tailWord_2548926).sum := by decide
  have hdescent : baseEnd_2548926 < baseStart_2548926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548928 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 2, 4]
def baseStart_2548928 : Nat := 118140960795 + 2548928 * 2 ^ 59
def prefixEnd_2548928 : Nat := 4983230072969 + 3 ^ 40 * 2548928 * 2
def baseEnd_2548928 : Nat := 872550145135672360785133

theorem tailTrace_2548928 : CollatzResearch.WordTrace tailWord_2548928 prefixEnd_2548928 872550145135672360785133 := by
  unfold tailWord_2548928
  simp only [CollatzResearch.WordTrace]
  refine ⟨46483520854838326544867719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61978027806451102059823625 46483520854838326544867719)
  ·
    refine ⟨69725281282257489817301579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46483520854838326544867719 69725281282257489817301579)
    ·
      refine ⟨104587921923386234725952369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69725281282257489817301579 104587921923386234725952369)
      ·
        refine ⟨78440941442539676044464277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104587921923386234725952369 78440941442539676044464277)
        ·
          refine ⟨3676919130119047314584263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78440941442539676044464277 3676919130119047314584263)
          ·
            refine ⟨5515378695178570971876395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3676919130119047314584263 5515378695178570971876395)
            ·
              refine ⟨8273068042767856457814593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5515378695178570971876395 8273068042767856457814593)
              ·
                refine ⟨6204801032075892343360945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8273068042767856457814593 6204801032075892343360945)
                ·
                  refine ⟨4653600774056919257520709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6204801032075892343360945 4653600774056919257520709)
                  ·
                    refine ⟨872550145135672360785133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4653600774056919257520709 872550145135672360785133)
                    ·
                      rfl

theorem cell22_2548928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_2548928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548928 prefixEnd_2548928 := by exact prefixLift 2548928
  have htrace : WordTrace (prefixWord ++ tailWord_2548928) baseStart_2548928 baseEnd_2548928 := by
    simpa [prefixWord, tailWord_2548928, baseEnd_2548928] using wordTrace_append hprefix tailTrace_2548928
  have hstable : (prefixWord ++ tailWord_2548928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548928).length < 2 ^ (prefixWord ++ tailWord_2548928).sum := by decide
  have hdescent : baseEnd_2548928 < baseStart_2548928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548932 : List Nat := [2, 3, 3, 1, 3, 1, 3, 2, 4]
def baseStart_2548932 : Nat := 118140960795 + 2548932 * 2 ^ 59
def prefixEnd_2548932 : Nat := 4983230072969 + 3 ^ 40 * 2548932 * 2
def baseEnd_2548932 : Nat := 290850504805805894561707

theorem tailTrace_2548932 : CollatzResearch.WordTrace tailWord_2548932 prefixEnd_2548932 290850504805805894561707 := by
  unfold tailWord_2548932
  simp only [CollatzResearch.WordTrace]
  refine ⟨46483593800831080886440525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61978125067774774515254033 46483593800831080886440525)
  ·
    refine ⟨17431347675311655332415197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46483593800831080886440525 17431347675311655332415197)
    ·
      refine ⟨6536755378241870749655699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17431347675311655332415197 6536755378241870749655699)
      ·
        refine ⟨9805133067362806124483549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6536755378241870749655699 9805133067362806124483549)
        ·
          refine ⟨3676924900261052296681331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9805133067362806124483549 3676924900261052296681331)
          ·
            refine ⟨5515387350391578445021997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3676924900261052296681331 5515387350391578445021997)
            ·
              refine ⟨2068270256396841916883249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5515387350391578445021997 2068270256396841916883249)
              ·
                refine ⟨1551202692297631437662437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2068270256396841916883249 1551202692297631437662437)
                ·
                  refine ⟨290850504805805894561707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1551202692297631437662437 290850504805805894561707)
                  ·
                    rfl

theorem cell22_2548932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_2548932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548932 prefixEnd_2548932 := by exact prefixLift 2548932
  have htrace : WordTrace (prefixWord ++ tailWord_2548932) baseStart_2548932 baseEnd_2548932 := by
    simpa [prefixWord, tailWord_2548932, baseEnd_2548932] using wordTrace_append hprefix tailTrace_2548932
  have hstable : (prefixWord ++ tailWord_2548932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548932).length < 2 ^ (prefixWord ++ tailWord_2548932).sum := by decide
  have hdescent : baseEnd_2548932 < baseStart_2548932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548986 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 2, 5]
def baseStart_2548986 : Nat := 118140960795 + 2548986 * 2 ^ 59
def prefixEnd_2548986 : Nat := 4983230072969 + 3 ^ 40 * 2548986 * 2
def baseEnd_2548986 : Nat := 872569999720979542834955

theorem tailTrace_2548986 : CollatzResearch.WordTrace tailWord_2548986 prefixEnd_2548986 872569999720979542834955 := by
  unfold tailWord_2548986
  simp only [CollatzResearch.WordTrace]
  refine ⟨23242289285866632248836703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61979438095644352663564541 23242289285866632248836703)
  ·
    refine ⟨34863433928799948373255055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23242289285866632248836703 34863433928799948373255055)
    ·
      refine ⟨52295150893199922559882583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34863433928799948373255055 52295150893199922559882583)
      ·
        refine ⟨78442726339799883839823875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52295150893199922559882583 78442726339799883839823875)
        ·
          refine ⟨117664089509699825759735813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78442726339799883839823875 117664089509699825759735813)
          ·
            refine ⟨22062016783068717329950465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117664089509699825759735813 22062016783068717329950465)
            ·
              refine ⟨16546512587301537997462849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22062016783068717329950465 16546512587301537997462849)
              ·
                refine ⟨12409884440476153498097137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16546512587301537997462849 12409884440476153498097137)
                ·
                  refine ⟨9307413330357115123572853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12409884440476153498097137 9307413330357115123572853)
                  ·
                    refine ⟨872569999720979542834955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9307413330357115123572853 872569999720979542834955)
                    ·
                      rfl

theorem cell22_2548986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_2548986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2548986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2548986 prefixEnd_2548986 := by exact prefixLift 2548986
  have htrace : WordTrace (prefixWord ++ tailWord_2548986) baseStart_2548986 baseEnd_2548986 := by
    simpa [prefixWord, tailWord_2548986, baseEnd_2548986] using wordTrace_append hprefix tailTrace_2548986
  have hstable : (prefixWord ++ tailWord_2548986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548986).length < 2 ^ (prefixWord ++ tailWord_2548986).sum := by decide
  have hdescent : baseEnd_2548986 < baseStart_2548986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549001 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 5, 4]
def baseStart_2549001 : Nat := 118140960795 + 2549001 * 2 ^ 59
def prefixEnd_2549001 : Nat := 4983230072969 + 3 ^ 40 * 2549001 * 2
def baseEnd_2549001 : Nat := 872575134527524503709909

theorem tailTrace_2549001 : CollatzResearch.WordTrace tailWord_2549001 prefixEnd_2549001 872575134527524503709909 := by
  unfold tailWord_2549001
  simp only [CollatzResearch.WordTrace]
  refine ⟨92969704238412186557142857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61979802825608124371428571 92969704238412186557142857)
  ·
    refine ⟨69727278178809139917857143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92969704238412186557142857 69727278178809139917857143)
    ·
      refine ⟨104590917268213709876785715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69727278178809139917857143 104590917268213709876785715)
      ·
        refine ⟨156886375902320564815178573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104590917268213709876785715 156886375902320564815178573)
        ·
          refine ⟨58832390963370211805691965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156886375902320564815178573 58832390963370211805691965)
          ·
            refine ⟨22062146611263829427134487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58832390963370211805691965 22062146611263829427134487)
            ·
              refine ⟨33093219916895744140701731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22062146611263829427134487 33093219916895744140701731)
              ·
                refine ⟨49639829875343616211052597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33093219916895744140701731 49639829875343616211052597)
                ·
                  refine ⟨4653734050813464019786181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49639829875343616211052597 4653734050813464019786181)
                  ·
                    refine ⟨872575134527524503709909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4653734050813464019786181 872575134527524503709909)
                    ·
                      rfl

theorem cell22_2549001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_2549001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549001 prefixEnd_2549001 := by exact prefixLift 2549001
  have htrace : WordTrace (prefixWord ++ tailWord_2549001) baseStart_2549001 baseEnd_2549001 := by
    simpa [prefixWord, tailWord_2549001, baseEnd_2549001] using wordTrace_append hprefix tailTrace_2549001
  have hstable : (prefixWord ++ tailWord_2549001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549001).length < 2 ^ (prefixWord ++ tailWord_2549001).sum := by decide
  have hdescent : baseEnd_2549001 < baseStart_2549001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549016 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 8]
def baseStart_2549016 : Nat := 118140960795 + 2549016 * 2 ^ 59
def prefixEnd_2549016 : Nat := 4983230072969 + 3 ^ 40 * 2549016 * 2
def baseEnd_2549016 : Nat := 290860089778023154861621

theorem tailTrace_2549016 : CollatzResearch.WordTrace tailWord_2549016 prefixEnd_2549016 290860089778023154861621 := by
  unfold tailWord_2549016
  simp only [CollatzResearch.WordTrace]
  refine ⟨46485125666678922059469451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61980167555571896079292601 46485125666678922059469451)
  ·
    refine ⟨69727688500018383089204177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46485125666678922059469451 69727688500018383089204177)
    ·
      refine ⟨52295766375013787316903133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69727688500018383089204177 52295766375013787316903133)
      ·
        refine ⟨19610912390630170243838675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52295766375013787316903133 19610912390630170243838675)
        ·
          refine ⟨29416368585945255365758013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19610912390630170243838675 29416368585945255365758013)
          ·
            refine ⟨11031138219729470762159255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29416368585945255365758013 11031138219729470762159255)
            ·
              refine ⟨16546707329594206143238883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11031138219729470762159255 16546707329594206143238883)
              ·
                refine ⟨24820060994391309214858325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16546707329594206143238883 24820060994391309214858325)
                ·
                  refine ⟨290860089778023154861621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24820060994391309214858325 290860089778023154861621)
                  ·
                    rfl

theorem cell22_2549016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 8].length) (baseStart_2549016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549016 prefixEnd_2549016 := by exact prefixLift 2549016
  have htrace : WordTrace (prefixWord ++ tailWord_2549016) baseStart_2549016 baseEnd_2549016 := by
    simpa [prefixWord, tailWord_2549016, baseEnd_2549016] using wordTrace_append hprefix tailTrace_2549016
  have hstable : (prefixWord ++ tailWord_2549016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549016).length < 2 ^ (prefixWord ++ tailWord_2549016).sum := by decide
  have hdescent : baseEnd_2549016 < baseStart_2549016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549018 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 3, 4]
def baseStart_2549018 : Nat := 118140960795 + 2549018 * 2 ^ 59
def prefixEnd_2549018 : Nat := 4983230072969 + 3 ^ 40 * 2549018 * 2
def baseEnd_2549018 : Nat := 872580953974942126034857

theorem tailTrace_2549018 : CollatzResearch.WordTrace tailWord_2549018 prefixEnd_2549018 872580953974942126034857 := by
  unfold tailWord_2549018
  simp only [CollatzResearch.WordTrace]
  refine ⟨23242581069837649615127927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61980216186233732307007805 23242581069837649615127927)
  ·
    refine ⟨34863871604756474422691891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23242581069837649615127927 34863871604756474422691891)
    ·
      refine ⟨52295807407134711634037837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34863871604756474422691891 52295807407134711634037837)
      ·
        refine ⟨19610927777675516862764189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52295807407134711634037837 19610927777675516862764189)
        ·
          refine ⟨7354097916628318823536571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19610927777675516862764189 7354097916628318823536571)
          ·
            refine ⟨11031146874942478235304857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7354097916628318823536571 11031146874942478235304857)
            ·
              refine ⟨8273360156206858676478643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11031146874942478235304857 8273360156206858676478643)
              ·
                refine ⟨12410040234310288014717965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8273360156206858676478643 12410040234310288014717965)
                ·
                  refine ⟨4653765087866358005519237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12410040234310288014717965 4653765087866358005519237)
                  ·
                    refine ⟨872580953974942126034857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4653765087866358005519237 872580953974942126034857)
                    ·
                      rfl

theorem cell22_2549018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_2549018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549018 prefixEnd_2549018 := by exact prefixLift 2549018
  have htrace : WordTrace (prefixWord ++ tailWord_2549018) baseStart_2549018 baseEnd_2549018 := by
    simpa [prefixWord, tailWord_2549018, baseEnd_2549018] using wordTrace_append hprefix tailTrace_2549018
  have hstable : (prefixWord ++ tailWord_2549018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549018).length < 2 ^ (prefixWord ++ tailWord_2549018).sum := by decide
  have hdescent : baseEnd_2549018 < baseStart_2549018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549069 : List Nat := [1, 6, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_2549069 : Nat := 118140960795 + 2549069 * 2 ^ 59
def prefixEnd_2549069 : Nat := 4983230072969 + 3 ^ 40 * 2549069 * 2
def baseEnd_2549069 : Nat := 872598412317194993009701

theorem tailTrace_2549069 : CollatzResearch.WordTrace tailWord_2549069 prefixEnd_2549069 872598412317194993009701 := by
  unfold tailWord_2549069
  simp only [CollatzResearch.WordTrace]
  refine ⟨92972184402165834170618261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61981456268110556113745507 92972184402165834170618261)
  ·
    refine ⟨4358071143851523476747731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92972184402165834170618261 4358071143851523476747731)
    ·
      refine ⟨6537106715777285215121597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4358071143851523476747731 6537106715777285215121597)
      ·
        refine ⟨2451415018416481955670599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6537106715777285215121597 2451415018416481955670599)
        ·
          refine ⟨3677122527624722933505899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451415018416481955670599 3677122527624722933505899)
          ·
            refine ⟨5515683791437084400258849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3677122527624722933505899 5515683791437084400258849)
            ·
              refine ⟨4136762843577813300194137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5515683791437084400258849 4136762843577813300194137)
              ·
                refine ⟨3102572132683359975145603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4136762843577813300194137 3102572132683359975145603)
                ·
                  refine ⟨4653858199025039962718405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3102572132683359975145603 4653858199025039962718405)
                  ·
                    refine ⟨872598412317194993009701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4653858199025039962718405 872598412317194993009701)
                    ·
                      rfl

theorem cell22_2549069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_2549069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549069 prefixEnd_2549069 := by exact prefixLift 2549069
  have htrace : WordTrace (prefixWord ++ tailWord_2549069) baseStart_2549069 baseEnd_2549069 := by
    simpa [prefixWord, tailWord_2549069, baseEnd_2549069] using wordTrace_append hprefix tailTrace_2549069
  have hstable : (prefixWord ++ tailWord_2549069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549069).length < 2 ^ (prefixWord ++ tailWord_2549069).sum := by decide
  have hdescent : baseEnd_2549069 < baseStart_2549069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549095 : List Nat := [1, 1, 5, 1, 5, 1, 8]
def baseStart_2549095 : Nat := 118140960795 + 2549095 * 2 ^ 59
def prefixEnd_2549095 : Nat := 4983230072969 + 3 ^ 40 * 2549095 * 2
def baseEnd_2549095 : Nat := 32318789357353318217023

theorem tailTrace_2549095 : CollatzResearch.WordTrace tailWord_2549095 prefixEnd_2549095 32318789357353318217023 := by
  unfold tailWord_2549095
  simp only [CollatzResearch.WordTrace]
  refine ⟨92973132700071640611064739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61982088466714427074043159 92973132700071640611064739)
  ·
    refine ⟨139459699050107460916597109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92973132700071640611064739 139459699050107460916597109)
    ·
      refine ⟨13074346785947574460930979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139459699050107460916597109 13074346785947574460930979)
      ·
        refine ⟨19611520178921361691396469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13074346785947574460930979 19611520178921361691396469)
        ·
          refine ⟨1838580016773877658568419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19611520178921361691396469 1838580016773877658568419)
          ·
            refine ⟨2757870025160816487852629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838580016773877658568419 2757870025160816487852629)
            ·
              refine ⟨32318789357353318217023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2757870025160816487852629 32318789357353318217023)
              ·
                rfl

theorem cell22_2549095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 8].length) (baseStart_2549095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549095 prefixEnd_2549095 := by exact prefixLift 2549095
  have htrace : WordTrace (prefixWord ++ tailWord_2549095) baseStart_2549095 baseEnd_2549095 := by
    simpa [prefixWord, tailWord_2549095, baseEnd_2549095] using wordTrace_append hprefix tailTrace_2549095
  have hstable : (prefixWord ++ tailWord_2549095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549095).length < 2 ^ (prefixWord ++ tailWord_2549095).sum := by decide
  have hdescent : baseEnd_2549095 < baseStart_2549095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549217 : List Nat := [1, 2, 3, 1, 2, 3, 3, 2, 2, 3]
def baseStart_2549217 : Nat := 118140960795 + 2549217 * 2 ^ 59
def prefixEnd_2549217 : Nat := 4983230072969 + 3 ^ 40 * 2549217 * 2
def baseEnd_2549217 : Nat := 872649075741771940309247

theorem tailTrace_2549217 : CollatzResearch.WordTrace tailWord_2549217 prefixEnd_2549217 872649075741771940309247 := by
  unfold tailWord_2549217
  simp only [CollatzResearch.WordTrace]
  refine ⟨92977582405629655447005905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61985054937086436964670603 92977582405629655447005905)
  ·
    refine ⟨69733186804222241585254429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92977582405629655447005905 69733186804222241585254429)
    ·
      refine ⟨26149945051583340594470411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69733186804222241585254429 26149945051583340594470411)
      ·
        refine ⟨39224917577375010891705617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26149945051583340594470411 39224917577375010891705617)
        ·
          refine ⟨29418688183031258168779213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39224917577375010891705617 29418688183031258168779213)
          ·
            refine ⟨11032008068636721813292205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29418688183031258168779213 11032008068636721813292205)
            ·
              refine ⟨4137003025738770679984577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11032008068636721813292205 4137003025738770679984577)
              ·
                refine ⟨3102752269304078009988433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4137003025738770679984577 3102752269304078009988433)
                ·
                  refine ⟨2327064201978058507491325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3102752269304078009988433 2327064201978058507491325)
                  ·
                    refine ⟨872649075741771940309247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2327064201978058507491325 872649075741771940309247)
                    ·
                      rfl

theorem cell22_2549217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_2549217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549217 prefixEnd_2549217 := by exact prefixLift 2549217
  have htrace : WordTrace (prefixWord ++ tailWord_2549217) baseStart_2549217 baseEnd_2549217 := by
    simpa [prefixWord, tailWord_2549217, baseEnd_2549217] using wordTrace_append hprefix tailTrace_2549217
  have hstable : (prefixWord ++ tailWord_2549217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549217).length < 2 ^ (prefixWord ++ tailWord_2549217).sum := by decide
  have hdescent : baseEnd_2549217 < baseStart_2549217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549290 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 1, 7]
def baseStart_2549290 : Nat := 118140960795 + 2549290 * 2 ^ 59
def prefixEnd_2549290 : Nat := 4983230072969 + 3 ^ 40 * 2549290 * 2
def baseEnd_2549290 : Nat := 872674065133624083234023

theorem tailTrace_2549290 : CollatzResearch.WordTrace tailWord_2549290 prefixEnd_2549290 872674065133624083234023 := by
  unfold tailWord_2549290
  simp only [CollatzResearch.WordTrace]
  refine ⟨23245061233591297228603331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61986829956243459276275549 23245061233591297228603331)
  ·
    refine ⟨34867591850386945842904997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23245061233591297228603331 34867591850386945842904997)
    ·
      refine ⟨6537673471947552345544687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34867591850386945842904997 6537673471947552345544687)
      ·
        refine ⟨9806510207921328518317031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6537673471947552345544687 9806510207921328518317031)
        ·
          refine ⟨14709765311881992777475547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9806510207921328518317031 14709765311881992777475547)
          ·
            refine ⟨22064647967822989166213321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14709765311881992777475547 22064647967822989166213321)
            ·
              refine ⟨16548485975867241874659991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22064647967822989166213321 16548485975867241874659991)
              ·
                refine ⟨24822728963800862811989987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16548485975867241874659991 24822728963800862811989987)
                ·
                  refine ⟨37234093445701294217984981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24822728963800862811989987 37234093445701294217984981)
                  ·
                    refine ⟨872674065133624083234023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37234093445701294217984981 872674065133624083234023)
                    ·
                      rfl

theorem cell22_2549290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_2549290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549290 prefixEnd_2549290 := by exact prefixLift 2549290
  have htrace : WordTrace (prefixWord ++ tailWord_2549290) baseStart_2549290 baseEnd_2549290 := by
    simpa [prefixWord, tailWord_2549290, baseEnd_2549290] using wordTrace_append hprefix tailTrace_2549290
  have hstable : (prefixWord ++ tailWord_2549290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549290).length < 2 ^ (prefixWord ++ tailWord_2549290).sum := by decide
  have hdescent : baseEnd_2549290 < baseStart_2549290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549352 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 1, 5]
def baseStart_2549352 : Nat := 118140960795 + 2549352 * 2 ^ 59
def prefixEnd_2549352 : Nat := 4983230072969 + 3 ^ 40 * 2549352 * 2
def baseEnd_2549352 : Nat := 872695289000676588183833

theorem tailTrace_2549352 : CollatzResearch.WordTrace tailWord_2549352 prefixEnd_2549352 872695289000676588183833 := by
  unfold tailWord_2549352
  simp only [CollatzResearch.WordTrace]
  refine ⟨46491253130070286751585155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61988337506760382335446873 46491253130070286751585155)
  ·
    refine ⟨69736879695105430127377733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46491253130070286751585155 69736879695105430127377733)
    ·
      refine ⟨13075664942832268148883325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69736879695105430127377733 13075664942832268148883325)
      ·
        refine ⟨4903374353562100555831247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13075664942832268148883325 4903374353562100555831247)
        ·
          refine ⟨7355061530343150833746871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4903374353562100555831247 7355061530343150833746871)
          ·
            refine ⟨11032592295514726250620307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7355061530343150833746871 11032592295514726250620307)
            ·
              refine ⟨16548888443272089375930461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11032592295514726250620307 16548888443272089375930461)
              ·
                refine ⟨6205833166227033515973923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16548888443272089375930461 6205833166227033515973923)
                ·
                  refine ⟨9308749749340550273960885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6205833166227033515973923 9308749749340550273960885)
                  ·
                    refine ⟨872695289000676588183833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9308749749340550273960885 872695289000676588183833)
                    ·
                      rfl

theorem cell22_2549352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_2549352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549352 prefixEnd_2549352 := by exact prefixLift 2549352
  have htrace : WordTrace (prefixWord ++ tailWord_2549352) baseStart_2549352 baseEnd_2549352 := by
    simpa [prefixWord, tailWord_2549352, baseEnd_2549352] using wordTrace_append hprefix tailTrace_2549352
  have hstable : (prefixWord ++ tailWord_2549352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549352).length < 2 ^ (prefixWord ++ tailWord_2549352).sum := by decide
  have hdescent : baseEnd_2549352 < baseStart_2549352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549386 : List Nat := [3, 1, 2, 3, 2, 3, 1, 2, 2, 3]
def baseStart_2549386 : Nat := 118140960795 + 2549386 * 2 ^ 59
def prefixEnd_2549386 : Nat := 4983230072969 + 3 ^ 40 * 2549386 * 2
def baseEnd_2549386 : Nat := 872706927895511832833729

theorem tailTrace_2549386 : CollatzResearch.WordTrace tailWord_2549386 prefixEnd_2549386 872706927895511832833729 := by
  unfold tailWord_2549386
  simp only [CollatzResearch.WordTrace]
  refine ⟨23245936585504349327477003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61989164228011598206605341 23245936585504349327477003)
  ·
    refine ⟨34868904878256523991215505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23245936585504349327477003 34868904878256523991215505)
    ·
      refine ⟨26151678658692392993411629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34868904878256523991215505 26151678658692392993411629)
      ·
        refine ⟨9806879497009647372529361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26151678658692392993411629 9806879497009647372529361)
        ·
          refine ⟨7355159622757235529397021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9806879497009647372529361 7355159622757235529397021)
          ·
            refine ⟨2758184858533963323523883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7355159622757235529397021 2758184858533963323523883)
            ·
              refine ⟨4137277287800944985285825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2758184858533963323523883 4137277287800944985285825)
              ·
                refine ⟨3102957965850708738964369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4137277287800944985285825 3102957965850708738964369)
                ·
                  refine ⟨2327218474388031554223277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3102957965850708738964369 2327218474388031554223277)
                  ·
                    refine ⟨872706927895511832833729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2327218474388031554223277 872706927895511832833729)
                    ·
                      rfl

theorem cell22_2549386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_2549386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549386 prefixEnd_2549386 := by exact prefixLift 2549386
  have htrace : WordTrace (prefixWord ++ tailWord_2549386) baseStart_2549386 baseEnd_2549386 := by
    simpa [prefixWord, tailWord_2549386, baseEnd_2549386] using wordTrace_append hprefix tailTrace_2549386
  have hstable : (prefixWord ++ tailWord_2549386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549386).length < 2 ^ (prefixWord ++ tailWord_2549386).sum := by decide
  have hdescent : baseEnd_2549386 < baseStart_2549386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549416 : List Nat := [2, 1, 7, 1, 1, 1, 1, 8]
def baseStart_2549416 : Nat := 118140960795 + 2549416 * 2 ^ 59
def prefixEnd_2549416 : Nat := 4983230072969 + 3 ^ 40 * 2549416 * 2
def baseEnd_2549416 : Nat := 96968577500955750509293

theorem tailTrace_2549416 : CollatzResearch.WordTrace tailWord_2549416 prefixEnd_2549416 96968577500955750509293 := by
  unfold tailWord_2549416
  simp only [CollatzResearch.WordTrace]
  refine ⟨46492420265954356216750051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61989893687939141622333401 46492420265954356216750051)
  ·
    refine ⟨69738630398931534325125077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46492420265954356216750051 69738630398931534325125077)
    ·
      refine ⟨1634499149974957835745119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 69738630398931534325125077 1634499149974957835745119)
      ·
        refine ⟨2451748724962436753617679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1634499149974957835745119 2451748724962436753617679)
        ·
          refine ⟨3677623087443655130426519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451748724962436753617679 3677623087443655130426519)
          ·
            refine ⟨5516434631165482695639779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3677623087443655130426519 5516434631165482695639779)
            ·
              refine ⟨8274651946748224043459669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5516434631165482695639779 8274651946748224043459669)
              ·
                refine ⟨96968577500955750509293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8274651946748224043459669 96968577500955750509293)
                ·
                  rfl

theorem cell22_2549416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 8].length) (baseStart_2549416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549416 prefixEnd_2549416 := by exact prefixLift 2549416
  have htrace : WordTrace (prefixWord ++ tailWord_2549416) baseStart_2549416 baseEnd_2549416 := by
    simpa [prefixWord, tailWord_2549416, baseEnd_2549416] using wordTrace_append hprefix tailTrace_2549416
  have hstable : (prefixWord ++ tailWord_2549416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549416).length < 2 ^ (prefixWord ++ tailWord_2549416).sum := by decide
  have hdescent : baseEnd_2549416 < baseStart_2549416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549431 : List Nat := [1, 1, 3, 1, 5, 1, 3, 3, 1, 3]
def baseStart_2549431 : Nat := 118140960795 + 2549431 * 2 ^ 59
def prefixEnd_2549431 : Nat := 4983230072969 + 3 ^ 40 * 2549431 * 2
def baseEnd_2549431 : Nat := 872722332315146715458591

theorem tailTrace_2549431 : CollatzResearch.WordTrace tailWord_2549431 prefixEnd_2549431 872722332315146715458591 := by
  unfold tailWord_2549431
  simp only [CollatzResearch.WordTrace]
  refine ⟨92985387626854369995296147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61990258417902913330197431 92985387626854369995296147)
  ·
    refine ⟨139478081440281554992944221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92985387626854369995296147 139478081440281554992944221)
    ·
      refine ⟨52304280540105583122354083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139478081440281554992944221 52304280540105583122354083)
      ·
        refine ⟨78456420810158374683531125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52304280540105583122354083 78456420810158374683531125)
        ·
          refine ⟨7355289450952347626581043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78456420810158374683531125 7355289450952347626581043)
          ·
            refine ⟨11032934176428521439871565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7355289450952347626581043 11032934176428521439871565)
            ·
              refine ⟨4137350316160695539951837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11032934176428521439871565 4137350316160695539951837)
              ·
                refine ⟨1551506368560260827481939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4137350316160695539951837 1551506368560260827481939)
                ·
                  refine ⟨2327259552840391241222909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1551506368560260827481939 2327259552840391241222909)
                  ·
                    refine ⟨872722332315146715458591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2327259552840391241222909 872722332315146715458591)
                    ·
                      rfl

theorem cell22_2549431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_2549431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549431 prefixEnd_2549431 := by exact prefixLift 2549431
  have htrace : WordTrace (prefixWord ++ tailWord_2549431) baseStart_2549431 baseEnd_2549431 := by
    simpa [prefixWord, tailWord_2549431, baseEnd_2549431] using wordTrace_append hprefix tailTrace_2549431
  have hstable : (prefixWord ++ tailWord_2549431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549431).length < 2 ^ (prefixWord ++ tailWord_2549431).sum := by decide
  have hdescent : baseEnd_2549431 < baseStart_2549431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549487 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 1, 5]
def baseStart_2549487 : Nat := 118140960795 + 2549487 * 2 ^ 59
def prefixEnd_2549487 : Nat := 4983230072969 + 3 ^ 40 * 2549487 * 2
def baseEnd_2549487 : Nat := 872741502259581236058419

theorem tailTrace_2549487 : CollatzResearch.WordTrace tailWord_2549487 prefixEnd_2549487 872741502259581236058419 := by
  unfold tailWord_2549487
  simp only [CollatzResearch.WordTrace]
  refine ⟨92987430114651491559334715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61991620076434327706223143 92987430114651491559334715)
  ·
    refine ⟨139481145171977237339002073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92987430114651491559334715 139481145171977237339002073)
    ·
      refine ⟨104610858878982928004251555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139481145171977237339002073 104610858878982928004251555)
      ·
        refine ⟨156916288318474392006377333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104610858878982928004251555 156916288318474392006377333)
        ·
          refine ⟨14710902029856974250597875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156916288318474392006377333 14710902029856974250597875)
          ·
            refine ⟨22066353044785461375896813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14710902029856974250597875 22066353044785461375896813)
            ·
              refine ⟨8274882391794548015961305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22066353044785461375896813 8274882391794548015961305)
              ·
                refine ⟨6206161793845911011970979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8274882391794548015961305 6206161793845911011970979)
                ·
                  refine ⟨9309242690768866517956469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6206161793845911011970979 9309242690768866517956469)
                  ·
                    refine ⟨872741502259581236058419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9309242690768866517956469 872741502259581236058419)
                    ·
                      rfl

theorem cell22_2549487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_2549487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549487 prefixEnd_2549487 := by exact prefixLift 2549487
  have htrace : WordTrace (prefixWord ++ tailWord_2549487) baseStart_2549487 baseEnd_2549487 := by
    simpa [prefixWord, tailWord_2549487, baseEnd_2549487] using wordTrace_append hprefix tailTrace_2549487
  have hstable : (prefixWord ++ tailWord_2549487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549487).length < 2 ^ (prefixWord ++ tailWord_2549487).sum := by decide
  have hdescent : baseEnd_2549487 < baseStart_2549487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549506 : List Nat := [3, 4, 1, 1, 1, 1, 3, 4, 4]
def baseStart_2549506 : Nat := 118140960795 + 2549506 * 2 ^ 59
def prefixEnd_2549506 : Nat := 4983230072969 + 3 ^ 40 * 2549506 * 2
def baseEnd_2549506 : Nat := 290916002115957173277787

theorem tailTrace_2549506 : CollatzResearch.WordTrace tailWord_2549506 prefixEnd_2549506 290916002115957173277787 := by
  unfold tailWord_2549506
  simp only [CollatzResearch.WordTrace]
  refine ⟨23247030775395664451069093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61992082067721771869517581 23247030775395664451069093)
  ·
    refine ⟨4358818270386687084575455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23247030775395664451069093 4358818270386687084575455)
    ·
      refine ⟨6538227405580030626863183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4358818270386687084575455 6538227405580030626863183)
      ·
        refine ⟨9807341108370045940294775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6538227405580030626863183 9807341108370045940294775)
        ·
          refine ⟨14711011662555068910442163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9807341108370045940294775 14711011662555068910442163)
          ·
            refine ⟨22066517493832603365663245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14711011662555068910442163 22066517493832603365663245)
            ·
              refine ⟨8274944060187226262123717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22066517493832603365663245 8274944060187226262123717)
              ·
                refine ⟨1551552011285104924148197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8274944060187226262123717 1551552011285104924148197)
                ·
                  refine ⟨290916002115957173277787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1551552011285104924148197 290916002115957173277787)
                  ·
                    rfl

theorem cell22_2549506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_2549506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549506 prefixEnd_2549506 := by exact prefixLift 2549506
  have htrace : WordTrace (prefixWord ++ tailWord_2549506) baseStart_2549506 baseEnd_2549506 := by
    simpa [prefixWord, tailWord_2549506, baseEnd_2549506] using wordTrace_append hprefix tailTrace_2549506
  have hstable : (prefixWord ++ tailWord_2549506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549506).length < 2 ^ (prefixWord ++ tailWord_2549506).sum := by decide
  have hdescent : baseEnd_2549506 < baseStart_2549506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549566 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_2549566 : Nat := 118140960795 + 2549566 * 2 ^ 59
def prefixEnd_2549566 : Nat := 4983230072969 + 3 ^ 40 * 2549566 * 2
def baseEnd_2549566 : Nat := 872768545574051363333177

theorem tailTrace_2549566 : CollatzResearch.WordTrace tailWord_2549566 prefixEnd_2549566 872768545574051363333177 := by
  unfold tailWord_2549566
  simp only [CollatzResearch.WordTrace]
  refine ⟨11623788935170661006432569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61993540987576858700973701 11623788935170661006432569)
  ·
    refine ⟨8717841701377995754824427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11623788935170661006432569 8717841701377995754824427)
    ·
      refine ⟨13076762552066993632236641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8717841701377995754824427 13076762552066993632236641)
      ·
        refine ⟨9807571914050245224177481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13076762552066993632236641 9807571914050245224177481)
        ·
          refine ⟨7355678935537683918133111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9807571914050245224177481 7355678935537683918133111)
          ·
            refine ⟨11033518403306525877199667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7355678935537683918133111 11033518403306525877199667)
            ·
              refine ⟨16550277604959788815799501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11033518403306525877199667 16550277604959788815799501)
              ·
                refine ⟨6206354101859920805924813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16550277604959788815799501 6206354101859920805924813)
                ·
                  refine ⟨2327382788197470302221805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6206354101859920805924813 2327382788197470302221805)
                  ·
                    refine ⟨872768545574051363333177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2327382788197470302221805 872768545574051363333177)
                    ·
                      rfl

theorem cell22_2549566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_2549566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549566 prefixEnd_2549566 := by exact prefixLift 2549566
  have htrace : WordTrace (prefixWord ++ tailWord_2549566) baseStart_2549566 baseEnd_2549566 := by
    simpa [prefixWord, tailWord_2549566, baseEnd_2549566] using wordTrace_append hprefix tailTrace_2549566
  have hstable : (prefixWord ++ tailWord_2549566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549566).length < 2 ^ (prefixWord ++ tailWord_2549566).sum := by decide
  have hdescent : baseEnd_2549566 < baseStart_2549566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549577 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 2, 5]
def baseStart_2549577 : Nat := 118140960795 + 2549577 * 2 ^ 59
def prefixEnd_2549577 : Nat := 4983230072969 + 3 ^ 40 * 2549577 * 2
def baseEnd_2549577 : Nat := 872772311098851001308143

theorem tailTrace_2549577 : CollatzResearch.WordTrace tailWord_2549577 prefixEnd_2549577 872772311098851001308143 := by
  unfold tailWord_2549577
  simp only [CollatzResearch.WordTrace]
  refine ⟨92990712684325436930110985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61993808456216957953407323 92990712684325436930110985)
  ·
    refine ⟨69743034513244077697583239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92990712684325436930110985 69743034513244077697583239)
    ·
      refine ⟨104614551769866116546374859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69743034513244077697583239 104614551769866116546374859)
      ·
        refine ⟨156921827654799174819562289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104614551769866116546374859 156921827654799174819562289)
        ·
          refine ⟨117691370741099381114671717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156921827654799174819562289 117691370741099381114671717)
          ·
            refine ⟨22067132013956133959000947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117691370741099381114671717 22067132013956133959000947)
            ·
              refine ⟨33100698020934200938501421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22067132013956133959000947 33100698020934200938501421)
              ·
                refine ⟨12412761757850325351938033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33100698020934200938501421 12412761757850325351938033)
                ·
                  refine ⟨9309571318387744013953525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12412761757850325351938033 9309571318387744013953525)
                  ·
                    refine ⟨872772311098851001308143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9309571318387744013953525 872772311098851001308143)
                    ·
                      rfl

theorem cell22_2549577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_2549577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549577 prefixEnd_2549577 := by exact prefixLift 2549577
  have htrace : WordTrace (prefixWord ++ tailWord_2549577) baseStart_2549577 baseEnd_2549577 := by
    simpa [prefixWord, tailWord_2549577, baseEnd_2549577] using wordTrace_append hprefix tailTrace_2549577
  have hstable : (prefixWord ++ tailWord_2549577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549577).length < 2 ^ (prefixWord ++ tailWord_2549577).sum := by decide
  have hdescent : baseEnd_2549577 < baseStart_2549577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549630 : List Nat := [4, 2, 3, 1, 1, 3, 2, 1, 5]
def baseStart_2549630 : Nat := 118140960795 + 2549630 * 2 ^ 59
def prefixEnd_2549630 : Nat := 4983230072969 + 3 ^ 40 * 2549630 * 2
def baseEnd_2549630 : Nat := 290930151360658843244327

theorem tailTrace_2549630 : CollatzResearch.WordTrace tailWord_2549630 prefixEnd_2549630 290930151360658843244327 := by
  unfold tailWord_2549630
  simp only [CollatzResearch.WordTrace]
  refine ⟨11624080719141678372723793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61995097168755617987860229 11624080719141678372723793)
  ·
    refine ⟨8718060539356258779542845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11624080719141678372723793 8718060539356258779542845)
    ·
      refine ⟨3269272702258597042328567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8718060539356258779542845 3269272702258597042328567)
      ·
        refine ⟨4903909053387895563492851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3269272702258597042328567 4903909053387895563492851)
        ·
          refine ⟨7355863580081843345239277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4903909053387895563492851 7355863580081843345239277)
          ·
            refine ⟨2758448842530691254464729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7355863580081843345239277 2758448842530691254464729)
            ·
              refine ⟨2068836631898018440848547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2758448842530691254464729 2068836631898018440848547)
              ·
                refine ⟨3103254947847027661272821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2068836631898018440848547 3103254947847027661272821)
                ·
                  refine ⟨290930151360658843244327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3103254947847027661272821 290930151360658843244327)
                  ·
                    rfl

theorem cell22_2549630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_2549630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549630 prefixEnd_2549630 := by exact prefixLift 2549630
  have htrace : WordTrace (prefixWord ++ tailWord_2549630) baseStart_2549630 baseEnd_2549630 := by
    simpa [prefixWord, tailWord_2549630, baseEnd_2549630] using wordTrace_append hprefix tailTrace_2549630
  have hstable : (prefixWord ++ tailWord_2549630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549630).length < 2 ^ (prefixWord ++ tailWord_2549630).sum := by decide
  have hdescent : baseEnd_2549630 < baseStart_2549630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549671 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2549671 : Nat := 118140960795 + 2549671 * 2 ^ 59
def prefixEnd_2549671 : Nat := 4983230072969 + 3 ^ 40 * 2549671 * 2
def baseEnd_2549671 : Nat := 872804489219866089457855

theorem tailTrace_2549671 : CollatzResearch.WordTrace tailWord_2549671 prefixEnd_2549671 872804489219866089457855 := by
  unfold tailWord_2549671
  simp only [CollatzResearch.WordTrace]
  refine ⟨92994141145984890984032867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61996094097323260656021911 92994141145984890984032867)
  ·
    refine ⟨139491211718977336476049301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92994141145984890984032867 139491211718977336476049301)
    ·
      refine ⟨6538650549327062647314811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139491211718977336476049301 6538650549327062647314811)
      ·
        refine ⟨9807975823990593970972217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6538650549327062647314811 9807975823990593970972217)
        ·
          refine ⟨7355981867992945478229163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9807975823990593970972217 7355981867992945478229163)
          ·
            refine ⟨11033972801989418217343745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7355981867992945478229163 11033972801989418217343745)
            ·
              refine ⟨8275479601492063663007809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11033972801989418217343745 8275479601492063663007809)
              ·
                refine ⟨6206609701119047747255857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8275479601492063663007809 6206609701119047747255857)
                ·
                  refine ⟨4654957275839285810441893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6206609701119047747255857 4654957275839285810441893)
                  ·
                    refine ⟨872804489219866089457855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4654957275839285810441893 872804489219866089457855)
                    ·
                      rfl

theorem cell22_2549671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2549671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549671 prefixEnd_2549671 := by exact prefixLift 2549671
  have htrace : WordTrace (prefixWord ++ tailWord_2549671) baseStart_2549671 baseEnd_2549671 := by
    simpa [prefixWord, tailWord_2549671, baseEnd_2549671] using wordTrace_append hprefix tailTrace_2549671
  have hstable : (prefixWord ++ tailWord_2549671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549671).length < 2 ^ (prefixWord ++ tailWord_2549671).sum := by decide
  have hdescent : baseEnd_2549671 < baseStart_2549671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549724 : List Nat := [2, 2, 6, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2549724 : Nat := 118140960795 + 2549724 * 2 ^ 59
def prefixEnd_2549724 : Nat := 4983230072969 + 3 ^ 40 * 2549724 * 2
def baseEnd_2549724 : Nat := 872822632202991617882693

theorem tailTrace_2549724 : CollatzResearch.WordTrace tailWord_2549724 prefixEnd_2549724 872822632202991617882693 := by
  unfold tailWord_2549724
  simp only [CollatzResearch.WordTrace]
  refine ⟨46498037107396440517856113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61997382809861920690474817 46498037107396440517856113)
  ·
    refine ⟨34873527830547330388392085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46498037107396440517856113 34873527830547330388392085)
    ·
      refine ⟨1634696617056906111955879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34873527830547330388392085 1634696617056906111955879)
      ·
        refine ⟨2452044925585359167933819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1634696617056906111955879 2452044925585359167933819)
        ·
          refine ⟨3678067388378038751900729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2452044925585359167933819 3678067388378038751900729)
          ·
            refine ⟨2758550541283529063925547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3678067388378038751900729 2758550541283529063925547)
            ·
              refine ⟨4137825811925293595888321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2758550541283529063925547 4137825811925293595888321)
              ·
                refine ⟨3103369358943970196916241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4137825811925293595888321 3103369358943970196916241)
                ·
                  refine ⟨2327527019207977647687181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3103369358943970196916241 2327527019207977647687181)
                  ·
                    refine ⟨872822632202991617882693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2327527019207977647687181 872822632202991617882693)
                    ·
                      rfl

theorem cell22_2549724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2549724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549724 prefixEnd_2549724 := by exact prefixLift 2549724
  have htrace : WordTrace (prefixWord ++ tailWord_2549724) baseStart_2549724 baseEnd_2549724 := by
    simpa [prefixWord, tailWord_2549724, baseEnd_2549724] using wordTrace_append hprefix tailTrace_2549724
  have hstable : (prefixWord ++ tailWord_2549724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549724).length < 2 ^ (prefixWord ++ tailWord_2549724).sum := by decide
  have hdescent : baseEnd_2549724 < baseStart_2549724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549729 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 2, 5]
def baseStart_2549729 : Nat := 118140960795 + 2549729 * 2 ^ 59
def prefixEnd_2549729 : Nat := 4983230072969 + 3 ^ 40 * 2549729 * 2
def baseEnd_2549729 : Nat := 872824343805173271507677

theorem tailTrace_2549729 : CollatzResearch.WordTrace tailWord_2549729 prefixEnd_2549729 872824343805173271507677 := by
  unfold tailWord_2549729
  simp only [CollatzResearch.WordTrace]
  refine ⟨92996256579774766889644241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61997504386516511259762827 92996256579774766889644241)
  ·
    refine ⟨69747192434831075167233181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92996256579774766889644241 69747192434831075167233181)
    ·
      refine ⟨26155197163061653187712443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69747192434831075167233181 26155197163061653187712443)
      ·
        refine ⟨39232795744592479781568665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26155197163061653187712443 39232795744592479781568665)
        ·
          refine ⟨29424596808444359836176499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39232795744592479781568665 29424596808444359836176499)
          ·
            refine ⟨44136895212666539754264749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29424596808444359836176499 44136895212666539754264749)
            ·
              refine ⟨16551335704749952407849281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44136895212666539754264749 16551335704749952407849281)
              ·
                refine ⟨12413501778562464305886961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16551335704749952407849281 12413501778562464305886961)
                ·
                  refine ⟨9310126333921848229415221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12413501778562464305886961 9310126333921848229415221)
                  ·
                    refine ⟨872824343805173271507677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9310126333921848229415221 872824343805173271507677)
                    ·
                      rfl

theorem cell22_2549729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_2549729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549729 prefixEnd_2549729 := by exact prefixLift 2549729
  have htrace : WordTrace (prefixWord ++ tailWord_2549729) baseStart_2549729 baseEnd_2549729 := by
    simpa [prefixWord, tailWord_2549729, baseEnd_2549729] using wordTrace_append hprefix tailTrace_2549729
  have hstable : (prefixWord ++ tailWord_2549729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549729).length < 2 ^ (prefixWord ++ tailWord_2549729).sum := by decide
  have hdescent : baseEnd_2549729 < baseStart_2549729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549731 : List Nat := [1, 1, 1, 6, 1, 2, 3, 2, 5]
def baseStart_2549731 : Nat := 118140960795 + 2549731 * 2 ^ 59
def prefixEnd_2549731 : Nat := 4983230072969 + 3 ^ 40 * 2549731 * 2
def baseEnd_2549731 : Nat := 290941676148681977652557

theorem tailTrace_2549731 : CollatzResearch.WordTrace tailWord_2549731 prefixEnd_2549731 290941676148681977652557 := by
  unfold tailWord_2549731
  simp only [CollatzResearch.WordTrace]
  refine ⟨92996329525767521231217047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61997553017178347487478031 92996329525767521231217047)
  ·
    refine ⟨139494494288651281846825571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92996329525767521231217047 139494494288651281846825571)
    ·
      refine ⟨209241741432976922770238357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139494494288651281846825571 209241741432976922770238357)
      ·
        refine ⟨9808206629670793254854923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 209241741432976922770238357 9808206629670793254854923)
        ·
          refine ⟨14712309944506189882282385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9808206629670793254854923 14712309944506189882282385)
          ·
            refine ⟨11034232458379642411711789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14712309944506189882282385 11034232458379642411711789)
            ·
              refine ⟨4137837171892365904391921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11034232458379642411711789 4137837171892365904391921)
              ·
                refine ⟨3103377878919274428293941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4137837171892365904391921 3103377878919274428293941)
                ·
                  refine ⟨290941676148681977652557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3103377878919274428293941 290941676148681977652557)
                  ·
                    rfl

theorem cell22_2549731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 5].length) (baseStart_2549731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549731 prefixEnd_2549731 := by exact prefixLift 2549731
  have htrace : WordTrace (prefixWord ++ tailWord_2549731) baseStart_2549731 baseEnd_2549731 := by
    simpa [prefixWord, tailWord_2549731, baseEnd_2549731] using wordTrace_append hprefix tailTrace_2549731
  have hstable : (prefixWord ++ tailWord_2549731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549731).length < 2 ^ (prefixWord ++ tailWord_2549731).sum := by decide
  have hdescent : baseEnd_2549731 < baseStart_2549731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549744 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 5, 4]
def baseStart_2549744 : Nat := 118140960795 + 2549744 * 2 ^ 59
def prefixEnd_2549744 : Nat := 4983230072969 + 3 ^ 40 * 2549744 * 2
def baseEnd_2549744 : Nat := 872829478611718232382631

theorem tailTrace_2549744 : CollatzResearch.WordTrace tailWord_2549744 prefixEnd_2549744 872829478611718232382631 := by
  unfold tailWord_2549744
  simp only [CollatzResearch.WordTrace]
  refine ⟨46498401837360212225720143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61997869116480282967626857 46498401837360212225720143)
  ·
    refine ⟨69747602756040318338580215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46498401837360212225720143 69747602756040318338580215)
    ·
      refine ⟨104621404134060477507870323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69747602756040318338580215 104621404134060477507870323)
      ·
        refine ⟨156932106201090716261805485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104621404134060477507870323 156932106201090716261805485)
        ·
          refine ⟨58849539825409018598177057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156932106201090716261805485 58849539825409018598177057)
          ·
            refine ⟨44137154869056763948632793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58849539825409018598177057 44137154869056763948632793)
            ·
              refine ⟨33102866151792572961474595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44137154869056763948632793 33102866151792572961474595)
              ·
                refine ⟨49654299227688859442211893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33102866151792572961474595 49654299227688859442211893)
                ·
                  refine ⟨4655090552595830572707365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49654299227688859442211893 4655090552595830572707365)
                  ·
                    refine ⟨872829478611718232382631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4655090552595830572707365 872829478611718232382631)
                    ·
                      rfl

theorem cell22_2549744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_2549744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549744 prefixEnd_2549744 := by exact prefixLift 2549744
  have htrace : WordTrace (prefixWord ++ tailWord_2549744) baseStart_2549744 baseEnd_2549744 := by
    simpa [prefixWord, tailWord_2549744, baseEnd_2549744] using wordTrace_append hprefix tailTrace_2549744
  have hstable : (prefixWord ++ tailWord_2549744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549744).length < 2 ^ (prefixWord ++ tailWord_2549744).sum := by decide
  have hdescent : baseEnd_2549744 < baseStart_2549744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549791 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 4, 3]
def baseStart_2549791 : Nat := 118140960795 + 2549791 * 2 ^ 59
def prefixEnd_2549791 : Nat := 4983230072969 + 3 ^ 40 * 2549791 * 2
def baseEnd_2549791 : Nat := 872845567672225776457487

theorem tailTrace_2549791 : CollatzResearch.WordTrace tailWord_2549791 prefixEnd_2549791 872845567672225776457487 := by
  unfold tailWord_2549791
  simp only [CollatzResearch.WordTrace]
  refine ⟨92998517905550151478401227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61999011937033434318934151 92998517905550151478401227)
  ·
    refine ⟨139497776858325227217601841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92998517905550151478401227 139497776858325227217601841)
    ·
      refine ⟨104623332643743920413201381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139497776858325227217601841 104623332643743920413201381)
      ·
        refine ⟨19616874870701985077475259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104623332643743920413201381 19616874870701985077475259)
        ·
          refine ⟨29425312306052977616212889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19616874870701985077475259 29425312306052977616212889)
          ·
            refine ⟨22068984229539733212159667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29425312306052977616212889 22068984229539733212159667)
            ·
              refine ⟨33103476344309599818239501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22068984229539733212159667 33103476344309599818239501)
              ·
                refine ⟨12413803629116099931839813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33103476344309599818239501 12413803629116099931839813)
                ·
                  refine ⟨2327588180459268737219965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12413803629116099931839813 2327588180459268737219965)
                  ·
                    refine ⟨872845567672225776457487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2327588180459268737219965 872845567672225776457487)
                    ·
                      rfl

theorem cell22_2549791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 3].length) (baseStart_2549791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549791 prefixEnd_2549791 := by exact prefixLift 2549791
  have htrace : WordTrace (prefixWord ++ tailWord_2549791) baseStart_2549791 baseEnd_2549791 := by
    simpa [prefixWord, tailWord_2549791, baseEnd_2549791] using wordTrace_append hprefix tailTrace_2549791
  have hstable : (prefixWord ++ tailWord_2549791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549791).length < 2 ^ (prefixWord ++ tailWord_2549791).sum := by decide
  have hdescent : baseEnd_2549791 < baseStart_2549791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549793 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 6]
def baseStart_2549793 : Nat := 118140960795 + 2549793 * 2 ^ 59
def prefixEnd_2549793 : Nat := 4983230072969 + 3 ^ 40 * 2549793 * 2
def baseEnd_2549793 : Nat := 290948750771032812635827

theorem tailTrace_2549793 : CollatzResearch.WordTrace tailWord_2549793 prefixEnd_2549793 290948750771032812635827 := by
  unfold tailWord_2549793
  simp only [CollatzResearch.WordTrace]
  refine ⟨92998590851542905819974033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61999060567695270546649355 92998590851542905819974033)
  ·
    refine ⟨69748943138657179364980525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92998590851542905819974033 69748943138657179364980525)
    ·
      refine ⟨26155853676996442261867697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69748943138657179364980525 26155853676996442261867697)
      ·
        refine ⟨19616890257747331696400773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26155853676996442261867697 19616890257747331696400773)
        ·
          refine ⟨3678166923327624693075145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19616890257747331696400773 3678166923327624693075145)
          ·
            refine ⟨2758625192495718519806359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3678166923327624693075145 2758625192495718519806359)
            ·
              refine ⟨4137937788743577779709539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2758625192495718519806359 4137937788743577779709539)
              ·
                refine ⟨6206906683115366669564309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4137937788743577779709539 6206906683115366669564309)
                ·
                  refine ⟨290948750771032812635827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6206906683115366669564309 290948750771032812635827)
                  ·
                    rfl

theorem cell22_2549793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 6].length) (baseStart_2549793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549793 prefixEnd_2549793 := by exact prefixLift 2549793
  have htrace : WordTrace (prefixWord ++ tailWord_2549793) baseStart_2549793 baseEnd_2549793 := by
    simpa [prefixWord, tailWord_2549793, baseEnd_2549793] using wordTrace_append hprefix tailTrace_2549793
  have hstable : (prefixWord ++ tailWord_2549793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549793).length < 2 ^ (prefixWord ++ tailWord_2549793).sum := by decide
  have hdescent : baseEnd_2549793 < baseStart_2549793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549808 : List Nat := [2, 1, 1, 1, 2, 6, 1, 3, 2, 3]
def baseStart_2549808 : Nat := 118140960795 + 2549808 * 2 ^ 59
def prefixEnd_2549808 : Nat := 4983230072969 + 3 ^ 40 * 2549808 * 2
def baseEnd_2549808 : Nat := 872851387119643398782435

theorem tailTrace_2549808 : CollatzResearch.WordTrace tailWord_2549808 prefixEnd_2549808 872851387119643398782435 := by
  unfold tailWord_2549808
  simp only [CollatzResearch.WordTrace]
  refine ⟨46499568973244281690885039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61999425297659042254513385 46499568973244281690885039)
  ·
    refine ⟨69749353459866422536327559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46499568973244281690885039 69749353459866422536327559)
    ·
      refine ⟨104624030189799633804491339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69749353459866422536327559 104624030189799633804491339)
      ·
        refine ⟨156936045284699450706737009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104624030189799633804491339 156936045284699450706737009)
        ·
          refine ⟨117702033963524588030052757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156936045284699450706737009 117702033963524588030052757)
          ·
            refine ⟨5517282842040215063908723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117702033963524588030052757 5517282842040215063908723)
            ·
              refine ⟨8275924263060322595863085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5517282842040215063908723 8275924263060322595863085)
              ·
                refine ⟨3103471598647620973448657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8275924263060322595863085 3103471598647620973448657)
                ·
                  refine ⟨2327603698985715730086493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3103471598647620973448657 2327603698985715730086493)
                  ·
                    refine ⟨872851387119643398782435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2327603698985715730086493 872851387119643398782435)
                    ·
                      rfl

theorem cell22_2549808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 2, 3].length) (baseStart_2549808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549808 prefixEnd_2549808 := by exact prefixLift 2549808
  have htrace : WordTrace (prefixWord ++ tailWord_2549808) baseStart_2549808 baseEnd_2549808 := by
    simpa [prefixWord, tailWord_2549808, baseEnd_2549808] using wordTrace_append hprefix tailTrace_2549808
  have hstable : (prefixWord ++ tailWord_2549808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549808).length < 2 ^ (prefixWord ++ tailWord_2549808).sum := by decide
  have hdescent : baseEnd_2549808 < baseStart_2549808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549812 : List Nat := [2, 5, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_2549812 : Nat := 118140960795 + 2549812 * 2 ^ 59
def prefixEnd_2549812 : Nat := 4983230072969 + 3 ^ 40 * 2549812 * 2
def baseEnd_2549812 : Nat := 872852756401388721682423

theorem tailTrace_2549812 : CollatzResearch.WordTrace tailWord_2549812 prefixEnd_2549812 872852756401388721682423 := by
  unfold tailWord_2549812
  simp only [CollatzResearch.WordTrace]
  refine ⟨46499641919237036032457845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61999522558982714709943793 46499641919237036032457845)
  ·
    refine ⟨4359341429928472128042923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46499641919237036032457845 4359341429928472128042923)
    ·
      refine ⟨6539012144892708192064385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4359341429928472128042923 6539012144892708192064385)
      ·
        refine ⟨4904259108669531144048289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6539012144892708192064385 4904259108669531144048289)
        ·
          refine ⟨3678194331502148358036217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4904259108669531144048289 3678194331502148358036217)
          ·
            refine ⟨2758645748626611268527163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3678194331502148358036217 2758645748626611268527163)
            ·
              refine ⟨4137968622939916902790745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2758645748626611268527163 4137968622939916902790745)
              ·
                refine ⟨3103476467204937677093059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4137968622939916902790745 3103476467204937677093059)
                ·
                  refine ⟨4655214700807406515639589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3103476467204937677093059 4655214700807406515639589)
                  ·
                    refine ⟨872852756401388721682423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4655214700807406515639589 872852756401388721682423)
                    ·
                      rfl

theorem cell22_2549812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_2549812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549812 prefixEnd_2549812 := by exact prefixLift 2549812
  have htrace : WordTrace (prefixWord ++ tailWord_2549812) baseStart_2549812 baseEnd_2549812 := by
    simpa [prefixWord, tailWord_2549812, baseEnd_2549812] using wordTrace_append hprefix tailTrace_2549812
  have hstable : (prefixWord ++ tailWord_2549812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549812).length < 2 ^ (prefixWord ++ tailWord_2549812).sum := by decide
  have hdescent : baseEnd_2549812 < baseStart_2549812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549943 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 4, 3]
def baseStart_2549943 : Nat := 118140960795 + 2549943 * 2 ^ 59
def prefixEnd_2549943 : Nat := 4983230072969 + 3 ^ 40 * 2549943 * 2
def baseEnd_2549943 : Nat := 872897600378548046657021

theorem tailTrace_2549943 : CollatzResearch.WordTrace tailWord_2549943 prefixEnd_2549943 872897600378548046657021 := by
  unfold tailWord_2549943
  simp only [CollatzResearch.WordTrace]
  refine ⟨93004061800999481437934483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62002707867332987625289655 93004061800999481437934483)
  ·
    refine ⟨139506092701499222156901725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93004061800999481437934483 139506092701499222156901725)
    ·
      refine ⟨52314784763062208308838147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139506092701499222156901725 52314784763062208308838147)
      ·
        refine ⟨78472177144593312463257221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52314784763062208308838147 78472177144593312463257221)
        ·
          refine ⟨14713533214611246086860729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78472177144593312463257221 14713533214611246086860729)
          ·
            refine ⟨11035149910958434565145547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14713533214611246086860729 11035149910958434565145547)
            ·
              refine ⟨16552724866437651847718321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11035149910958434565145547 16552724866437651847718321)
              ·
                refine ⟨12414543649828238885788741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16552724866437651847718321 12414543649828238885788741)
                ·
                  refine ⟨2327726934342794791085389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12414543649828238885788741 2327726934342794791085389)
                  ·
                    refine ⟨872897600378548046657021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2327726934342794791085389 872897600378548046657021)
                    ·
                      rfl

theorem cell22_2549943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_2549943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549943 prefixEnd_2549943 := by exact prefixLift 2549943
  have htrace : WordTrace (prefixWord ++ tailWord_2549943) baseStart_2549943 baseEnd_2549943 := by
    simpa [prefixWord, tailWord_2549943, baseEnd_2549943] using wordTrace_append hprefix tailTrace_2549943
  have hstable : (prefixWord ++ tailWord_2549943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549943).length < 2 ^ (prefixWord ++ tailWord_2549943).sum := by decide
  have hdescent : baseEnd_2549943 < baseStart_2549943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2549988 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 5, 3]
def baseStart_2549988 : Nat := 118140960795 + 2549988 * 2 ^ 59
def prefixEnd_2549988 : Nat := 4983230072969 + 3 ^ 40 * 2549988 * 2
def baseEnd_2549988 : Nat := 872913004798182929281883

theorem tailTrace_2549988 : CollatzResearch.WordTrace tailWord_2549988 prefixEnd_2549988 872913004798182929281883 := by
  unfold tailWord_2549988
  simp only [CollatzResearch.WordTrace]
  refine ⟨46502851542918227061661309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62003802057224302748881745 46502851542918227061661309)
  ·
    refine ⟨17438569328594335148122991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46502851542918227061661309 17438569328594335148122991)
    ·
      refine ⟨26157853992891502722184487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17438569328594335148122991 26157853992891502722184487)
      ·
        refine ⟨39236780989337254083276731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26157853992891502722184487 39236780989337254083276731)
        ·
          refine ⟨58855171484005881124915097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39236780989337254083276731 58855171484005881124915097)
          ·
            refine ⟨44141378613004410843686323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58855171484005881124915097 44141378613004410843686323)
            ·
              refine ⟨66212067919506616265529485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44141378613004410843686323 66212067919506616265529485)
              ·
                refine ⟨24829525469814981099573557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66212067919506616265529485 24829525469814981099573557)
                ·
                  refine ⟨2327768012795154478085021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24829525469814981099573557 2327768012795154478085021)
                  ·
                    refine ⟨872913004798182929281883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2327768012795154478085021 872913004798182929281883)
                    ·
                      rfl

theorem cell22_2549988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_2549988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2549988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2549988 prefixEnd_2549988 := by exact prefixLift 2549988
  have htrace : WordTrace (prefixWord ++ tailWord_2549988) baseStart_2549988 baseEnd_2549988 := by
    simpa [prefixWord, tailWord_2549988, baseEnd_2549988] using wordTrace_append hprefix tailTrace_2549988
  have hstable : (prefixWord ++ tailWord_2549988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2549988).length < 2 ^ (prefixWord ++ tailWord_2549988).sum := by decide
  have hdescent : baseEnd_2549988 < baseStart_2549988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2549988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550001 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 9]
def baseStart_2550001 : Nat := 118140960795 + 2550001 * 2 ^ 59
def prefixEnd_2550001 : Nat := 4983230072969 + 3 ^ 40 * 2550001 * 2
def baseEnd_2550001 : Nat := 290972484987951742902281

theorem tailTrace_2550001 : CollatzResearch.WordTrace tailWord_2550001 prefixEnd_2550001 290972484987951742902281 := by
  unfold tailWord_2550001
  simp only [CollatzResearch.WordTrace]
  refine ⟨93006177234789357343545857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62004118156526238229030571 93006177234789357343545857)
  ·
    refine ⟨69754632926092018007659393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93006177234789357343545857 69754632926092018007659393)
    ·
      refine ⟨52315974694569013505744545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69754632926092018007659393 52315974694569013505744545)
      ·
        refine ⟨39236981020926760129308409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52315974694569013505744545 39236981020926760129308409)
        ·
          refine ⟨29427735765695070096981307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39236981020926760129308409 29427735765695070096981307)
          ·
            refine ⟨44141603648542605145471961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29427735765695070096981307 44141603648542605145471961)
            ·
              refine ⟨33106202736406953859103971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44141603648542605145471961 33106202736406953859103971)
              ·
                refine ⟨49659304104610430788655957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33106202736406953859103971 49659304104610430788655957)
                ·
                  refine ⟨290972484987951742902281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49659304104610430788655957 290972484987951742902281)
                  ·
                    rfl

theorem cell22_2550001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 9].length) (baseStart_2550001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550001 prefixEnd_2550001 := by exact prefixLift 2550001
  have htrace : WordTrace (prefixWord ++ tailWord_2550001) baseStart_2550001 baseEnd_2550001 := by
    simpa [prefixWord, tailWord_2550001, baseEnd_2550001] using wordTrace_append hprefix tailTrace_2550001
  have hstable : (prefixWord ++ tailWord_2550001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550001).length < 2 ^ (prefixWord ++ tailWord_2550001).sum := by decide
  have hdescent : baseEnd_2550001 < baseStart_2550001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550033 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 2, 5]
def baseStart_2550033 : Nat := 118140960795 + 2550033 * 2 ^ 59
def prefixEnd_2550033 : Nat := 4983230072969 + 3 ^ 40 * 2550033 * 2
def baseEnd_2550033 : Nat := 872928409217817811906745

theorem tailTrace_2550033 : CollatzResearch.WordTrace tailWord_2550033 prefixEnd_2550033 872928409217817811906745 := by
  unfold tailWord_2550033
  simp only [CollatzResearch.WordTrace]
  refine ⟨93007344370673426808710753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62004896247115617872473835 93007344370673426808710753)
  ·
    refine ⟨69755508278005070106533065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93007344370673426808710753 69755508278005070106533065)
    ·
      refine ⟨52316631208503802579899799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69755508278005070106533065 52316631208503802579899799)
      ·
        refine ⟨78474946812755703869849699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52316631208503802579899799 78474946812755703869849699)
        ·
          refine ⟨117712420219133555804774549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78474946812755703869849699 117712420219133555804774549)
          ·
            refine ⟨5517769697771885428348807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117712420219133555804774549 5517769697771885428348807)
            ·
              refine ⟨8276654546657828142523211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5517769697771885428348807 8276654546657828142523211)
              ·
                refine ⟨12414981819986742213784817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8276654546657828142523211 12414981819986742213784817)
                ·
                  refine ⟨9311236364990056660338613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12414981819986742213784817 9311236364990056660338613)
                  ·
                    refine ⟨872928409217817811906745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9311236364990056660338613 872928409217817811906745)
                    ·
                      rfl

theorem cell22_2550033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_2550033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550033 prefixEnd_2550033 := by exact prefixLift 2550033
  have htrace : WordTrace (prefixWord ++ tailWord_2550033) baseStart_2550033 baseEnd_2550033 := by
    simpa [prefixWord, tailWord_2550033, baseEnd_2550033] using wordTrace_append hprefix tailTrace_2550033
  have hstable : (prefixWord ++ tailWord_2550033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550033).length < 2 ^ (prefixWord ++ tailWord_2550033).sum := by decide
  have hdescent : baseEnd_2550033 < baseStart_2550033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550114 : List Nat := [3, 3, 2, 1, 1, 4, 1, 3, 4]
def baseStart_2550114 : Nat := 118140960795 + 2550114 * 2 ^ 59
def prefixEnd_2550114 : Nat := 4983230072969 + 3 ^ 40 * 2550114 * 2
def baseEnd_2550114 : Nat := 290985379057720200210499

theorem tailTrace_2550114 : CollatzResearch.WordTrace tailWord_2550114 prefixEnd_2550114 290985379057720200210499 := by
  unfold tailWord_2550114
  simp only [CollatzResearch.WordTrace]
  refine ⟨23252574670844994410602349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62006865788919985094939597 23252574670844994410602349)
  ·
    refine ⟨8719715501566872903975881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23252574670844994410602349 8719715501566872903975881)
    ·
      refine ⟨6539786626175154677981911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8719715501566872903975881 6539786626175154677981911)
      ·
        refine ⟨9809679939262732016972867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6539786626175154677981911 9809679939262732016972867)
        ·
          refine ⟨14714519908894098025459301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9809679939262732016972867 14714519908894098025459301)
          ·
            refine ⟨2758972482917643379773619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14714519908894098025459301 2758972482917643379773619)
            ·
              refine ⟨4138458724376465069660429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2758972482917643379773619 4138458724376465069660429)
              ·
                refine ⟨1551922021641174401122661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4138458724376465069660429 1551922021641174401122661)
                ·
                  refine ⟨290985379057720200210499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1551922021641174401122661 290985379057720200210499)
                  ·
                    rfl

theorem cell22_2550114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_2550114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550114 prefixEnd_2550114 := by exact prefixLift 2550114
  have htrace : WordTrace (prefixWord ++ tailWord_2550114) baseStart_2550114 baseEnd_2550114 := by
    simpa [prefixWord, tailWord_2550114, baseEnd_2550114] using wordTrace_append hprefix tailTrace_2550114
  have hstable : (prefixWord ++ tailWord_2550114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550114).length < 2 ^ (prefixWord ++ tailWord_2550114).sum := by decide
  have hdescent : baseEnd_2550114 < baseStart_2550114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550140 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 3, 3]
def baseStart_2550140 : Nat := 118140960795 + 2550140 * 2 ^ 59
def prefixEnd_2550140 : Nat := 4983230072969 + 3 ^ 40 * 2550140 * 2
def baseEnd_2550140 : Nat := 872965037504505199481417

theorem tailTrace_2550140 : CollatzResearch.WordTrace tailWord_2550140 prefixEnd_2550140 872965037504505199481417 := by
  unfold tailWord_2550140
  simp only [CollatzResearch.WordTrace]
  refine ⟨46505623490642892041427937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62007497987523856055237249 46505623490642892041427937)
  ·
    refine ⟨34879217617982169031070953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46505623490642892041427937 34879217617982169031070953)
    ·
      refine ⟨26159413213486626773303215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34879217617982169031070953 26159413213486626773303215)
      ·
        refine ⟨39239119820229940159954823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26159413213486626773303215 39239119820229940159954823)
        ·
          refine ⟨58858679730344910239932235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39239119820229940159954823 58858679730344910239932235)
          ·
            refine ⟨88288019595517365359898353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58858679730344910239932235 88288019595517365359898353)
            ·
              refine ⟨66216014696638024019923765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88288019595517365359898353 66216014696638024019923765)
              ·
                refine ⟨6207751377809814751867853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66216014696638024019923765 6207751377809814751867853)
                ·
                  refine ⟨2327906766678680531950445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6207751377809814751867853 2327906766678680531950445)
                  ·
                    refine ⟨872965037504505199481417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2327906766678680531950445 872965037504505199481417)
                    ·
                      rfl

theorem cell22_2550140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_2550140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550140 prefixEnd_2550140 := by exact prefixLift 2550140
  have htrace : WordTrace (prefixWord ++ tailWord_2550140) baseStart_2550140 baseEnd_2550140 := by
    simpa [prefixWord, tailWord_2550140, baseEnd_2550140] using wordTrace_append hprefix tailTrace_2550140
  have hstable : (prefixWord ++ tailWord_2550140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550140).length < 2 ^ (prefixWord ++ tailWord_2550140).sum := by decide
  have hdescent : baseEnd_2550140 < baseStart_2550140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550146 : List Nat := [3, 4, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_2550146 : Nat := 118140960795 + 2550146 * 2 ^ 59
def prefixEnd_2550146 : Nat := 4983230072969 + 3 ^ 40 * 2550146 * 2
def baseEnd_2550146 : Nat := 872967091427123183831399

theorem tailTrace_2550146 : CollatzResearch.WordTrace tailWord_2550146 prefixEnd_2550146 872967091427123183831399 := by
  unfold tailWord_2550146
  simp only [CollatzResearch.WordTrace]
  refine ⟨23252866454816011776893573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62007643879509364738382861 23252866454816011776893573)
  ·
    refine ⟨4359912460278002208167545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23252866454816011776893573 4359912460278002208167545)
    ·
      refine ⟨3269934345208501656125659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4359912460278002208167545 3269934345208501656125659)
      ·
        refine ⟨4904901517812752484188489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3269934345208501656125659 4904901517812752484188489)
        ·
          refine ⟨3678676138359564363141367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4904901517812752484188489 3678676138359564363141367)
          ·
            refine ⟨5518014207539346544712051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3678676138359564363141367 5518014207539346544712051)
            ·
              refine ⟨8277021311309019817068077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5518014207539346544712051 8277021311309019817068077)
              ·
                refine ⟨3103882991740882431400529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8277021311309019817068077 3103882991740882431400529)
                ·
                  refine ⟨2327912243805661823550397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3103882991740882431400529 2327912243805661823550397)
                  ·
                    refine ⟨872967091427123183831399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2327912243805661823550397 872967091427123183831399)
                    ·
                      rfl

theorem cell22_2550146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_2550146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550146 prefixEnd_2550146 := by exact prefixLift 2550146
  have htrace : WordTrace (prefixWord ++ tailWord_2550146) baseStart_2550146 baseEnd_2550146 := by
    simpa [prefixWord, tailWord_2550146, baseEnd_2550146] using wordTrace_append hprefix tailTrace_2550146
  have hstable : (prefixWord ++ tailWord_2550146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550146).length < 2 ^ (prefixWord ++ tailWord_2550146).sum := by decide
  have hdescent : baseEnd_2550146 < baseStart_2550146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550215 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 6]
def baseStart_2550215 : Nat := 118140960795 + 2550215 * 2 ^ 59
def prefixEnd_2550215 : Nat := 4983230072969 + 3 ^ 40 * 2550215 * 2
def baseEnd_2550215 : Nat := 290996903845743334618729

theorem tailTrace_2550215 : CollatzResearch.WordTrace tailWord_2550215 prefixEnd_2550215 290996903845743334618729 := by
  unfold tailWord_2550215
  simp only [CollatzResearch.WordTrace]
  refine ⟨93013982456014071891836099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62009321637342714594557399 93013982456014071891836099)
  ·
    refine ⟨139520973684021107837754149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93013982456014071891836099 139520973684021107837754149)
    ·
      refine ⟨26160182565753957719578903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139520973684021107837754149 26160182565753957719578903)
      ·
        refine ⟨39240273848630936579368355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26160182565753957719578903 39240273848630936579368355)
        ·
          refine ⟨58860410772946404869052533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39240273848630936579368355 58860410772946404869052533)
          ·
            refine ⟨5518163509963725456473675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58860410772946404869052533 5518163509963725456473675)
            ·
              refine ⟨8277245264945588184710513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5518163509963725456473675 8277245264945588184710513)
              ·
                refine ⟨6207933948709191138532885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8277245264945588184710513 6207933948709191138532885)
                ·
                  refine ⟨290996903845743334618729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6207933948709191138532885 290996903845743334618729)
                  ·
                    rfl

theorem cell22_2550215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 6].length) (baseStart_2550215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550215 prefixEnd_2550215 := by exact prefixLift 2550215
  have htrace : WordTrace (prefixWord ++ tailWord_2550215) baseStart_2550215 baseEnd_2550215 := by
    simpa [prefixWord, tailWord_2550215, baseEnd_2550215] using wordTrace_append hprefix tailTrace_2550215
  have hstable : (prefixWord ++ tailWord_2550215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550215).length < 2 ^ (prefixWord ++ tailWord_2550215).sum := by decide
  have hdescent : baseEnd_2550215 < baseStart_2550215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550247 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 4, 3]
def baseStart_2550247 : Nat := 118140960795 + 2550247 * 2 ^ 59
def prefixEnd_2550247 : Nat := 4983230072969 + 3 ^ 40 * 2550247 * 2
def baseEnd_2550247 : Nat := 873001665791192587056089

theorem tailTrace_2550247 : CollatzResearch.WordTrace tailWord_2550247 prefixEnd_2550247 873001665791192587056089 := by
  unfold tailWord_2550247
  simp only [CollatzResearch.WordTrace]
  refine ⟨93015149591898141357000995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62010099727932094238000663 93015149591898141357000995)
  ·
    refine ⟨139522724387847212035501493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93015149591898141357000995 139522724387847212035501493)
    ·
      refine ⟨13080255411360676128328265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139522724387847212035501493 13080255411360676128328265)
      ·
        refine ⟨9810191558520507096246199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13080255411360676128328265 9810191558520507096246199)
        ·
          refine ⟨14715287337780760644369299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9810191558520507096246199 14715287337780760644369299)
          ·
            refine ⟨22072931006671140966553949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14715287337780760644369299 22072931006671140966553949)
            ·
              refine ⟨8277349127501677862457731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22072931006671140966553949 8277349127501677862457731)
              ·
                refine ⟨12416023691252516793686597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8277349127501677862457731 12416023691252516793686597)
                ·
                  refine ⟨2328004442109846898816237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12416023691252516793686597 2328004442109846898816237)
                  ·
                    refine ⟨873001665791192587056089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2328004442109846898816237 873001665791192587056089)
                    ·
                      rfl

theorem cell22_2550247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_2550247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550247 prefixEnd_2550247 := by exact prefixLift 2550247
  have htrace : WordTrace (prefixWord ++ tailWord_2550247) baseStart_2550247 baseEnd_2550247 := by
    simpa [prefixWord, tailWord_2550247, baseEnd_2550247] using wordTrace_append hprefix tailTrace_2550247
  have hstable : (prefixWord ++ tailWord_2550247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550247).length < 2 ^ (prefixWord ++ tailWord_2550247).sum := by decide
  have hdescent : baseEnd_2550247 < baseStart_2550247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550264 : List Nat := [2, 1, 2, 1, 1, 4, 5, 1, 2, 3]
def baseStart_2550264 : Nat := 118140960795 + 2550264 * 2 ^ 59
def prefixEnd_2550264 : Nat := 4983230072969 + 3 ^ 40 * 2550264 * 2
def baseEnd_2550264 : Nat := 873007485238610209381037

theorem tailTrace_2550264 : CollatzResearch.WordTrace tailWord_2550264 prefixEnd_2550264 873007485238610209381037 := by
  unfold tailWord_2550264
  simp only [CollatzResearch.WordTrace]
  refine ⟨46507884816418276630184923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62010513088557702173579897 46507884816418276630184923)
  ·
    refine ⟨69761827224627414945277385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46507884816418276630184923 69761827224627414945277385)
    ·
      refine ⟨52321370418470561208958039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69761827224627414945277385 52321370418470561208958039)
      ·
        refine ⟨78482055627705841813437059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52321370418470561208958039 78482055627705841813437059)
        ·
          refine ⟨117723083441558762720155589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78482055627705841813437059 117723083441558762720155589)
          ·
            refine ⟨22073078145292268010029173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117723083441558762720155589 22073078145292268010029173)
            ·
              refine ⟨2069351076121150125940235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22073078145292268010029173 2069351076121150125940235)
              ·
                refine ⟨3104026614181725188910353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2069351076121150125940235 3104026614181725188910353)
                ·
                  refine ⟨2328019960636293891682765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3104026614181725188910353 2328019960636293891682765)
                  ·
                    refine ⟨873007485238610209381037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2328019960636293891682765 873007485238610209381037)
                    ·
                      rfl

theorem cell22_2550264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_2550264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550264 prefixEnd_2550264 := by exact prefixLift 2550264
  have htrace : WordTrace (prefixWord ++ tailWord_2550264) baseStart_2550264 baseEnd_2550264 := by
    simpa [prefixWord, tailWord_2550264, baseEnd_2550264] using wordTrace_append hprefix tailTrace_2550264
  have hstable : (prefixWord ++ tailWord_2550264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550264).length < 2 ^ (prefixWord ++ tailWord_2550264).sum := by decide
  have hdescent : baseEnd_2550264 < baseStart_2550264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550305 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 7]
def baseStart_2550305 : Nat := 118140960795 + 2550305 * 2 ^ 59
def prefixEnd_2550305 : Nat := 4983230072969 + 3 ^ 40 * 2550305 * 2
def baseEnd_2550305 : Nat := 291007173458833256368637

theorem tailTrace_2550305 : CollatzResearch.WordTrace tailWord_2550305 prefixEnd_2550305 291007173458833256368637 := by
  unfold tailWord_2550305
  simp only [CollatzResearch.WordTrace]
  refine ⟨93017265025688017262612369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62011510017125344841741579 93017265025688017262612369)
  ·
    refine ⟨69762948769266012946959277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93017265025688017262612369 69762948769266012946959277)
    ·
      refine ⟨26161105788474754855109729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69762948769266012946959277 26161105788474754855109729)
      ·
        refine ⟨19620829341356066141332297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26161105788474754855109729 19620829341356066141332297)
        ·
          refine ⟨14715622006017049605999223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19620829341356066141332297 14715622006017049605999223)
          ·
            refine ⟨22073433009025574408998835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14715622006017049605999223 22073433009025574408998835)
            ·
              refine ⟨33110149513538361613498253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22073433009025574408998835 33110149513538361613498253)
              ·
                refine ⟨12416306067576885605061845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33110149513538361613498253 12416306067576885605061845)
                ·
                  refine ⟨291007173458833256368637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12416306067576885605061845 291007173458833256368637)
                  ·
                    rfl

theorem cell22_2550305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 7].length) (baseStart_2550305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550305 prefixEnd_2550305 := by exact prefixLift 2550305
  have htrace : WordTrace (prefixWord ++ tailWord_2550305) baseStart_2550305 baseEnd_2550305 := by
    simpa [prefixWord, tailWord_2550305, baseEnd_2550305] using wordTrace_append hprefix tailTrace_2550305
  have hstable : (prefixWord ++ tailWord_2550305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550305).length < 2 ^ (prefixWord ++ tailWord_2550305).sum := by decide
  have hdescent : baseEnd_2550305 < baseStart_2550305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550309 : List Nat := [1, 3, 1, 2, 2, 1, 2, 6, 1, 3]
def baseStart_2550309 : Nat := 118140960795 + 2550309 * 2 ^ 59
def prefixEnd_2550309 : Nat := 4983230072969 + 3 ^ 40 * 2550309 * 2
def baseEnd_2550309 : Nat := 873022889658245092005899

theorem tailTrace_2550309 : CollatzResearch.WordTrace tailWord_2550309 prefixEnd_2550309 873022889658245092005899 := by
  unfold tailWord_2550309
  simp only [CollatzResearch.WordTrace]
  refine ⟨93017410917673525945757981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62011607278449017297171987 93017410917673525945757981)
  ·
    refine ⟨34881529094127572229659243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93017410917673525945757981 34881529094127572229659243)
    ·
      refine ⟨52322293641191358344488865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34881529094127572229659243 52322293641191358344488865)
      ·
        refine ⟨39241720230893518758366649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52322293641191358344488865 39241720230893518758366649)
        ·
          refine ⟨29431290173170139068774987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39241720230893518758366649 29431290173170139068774987)
          ·
            refine ⟨44146935259755208603162481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29431290173170139068774987 44146935259755208603162481)
            ·
              refine ⟨33110201444816406452371861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44146935259755208603162481 33110201444816406452371861)
              ·
                refine ⟨1552040692725769052454931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33110201444816406452371861 1552040692725769052454931)
                ·
                  refine ⟨2328061039088653578682397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552040692725769052454931 2328061039088653578682397)
                  ·
                    refine ⟨873022889658245092005899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2328061039088653578682397 873022889658245092005899)
                    ·
                      rfl

theorem cell22_2550309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_2550309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550309 prefixEnd_2550309 := by exact prefixLift 2550309
  have htrace : WordTrace (prefixWord ++ tailWord_2550309) baseStart_2550309 baseEnd_2550309 := by
    simpa [prefixWord, tailWord_2550309, baseEnd_2550309] using wordTrace_append hprefix tailTrace_2550309
  have hstable : (prefixWord ++ tailWord_2550309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550309).length < 2 ^ (prefixWord ++ tailWord_2550309).sum := by decide
  have hdescent : baseEnd_2550309 < baseStart_2550309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550320 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 2, 5]
def baseStart_2550320 : Nat := 118140960795 + 2550320 * 2 ^ 59
def prefixEnd_2550320 : Nat := 4983230072969 + 3 ^ 40 * 2550320 * 2
def baseEnd_2550320 : Nat := 873026655183044729980865

theorem tailTrace_2550320 : CollatzResearch.WordTrace tailWord_2550320 prefixEnd_2550320 873026655183044729980865 := by
  unfold tailWord_2550320
  simp only [CollatzResearch.WordTrace]
  refine ⟨46508906060316837412204207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62011874747089116549605609 46508906060316837412204207)
  ·
    refine ⟨69763359090475256118306311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46508906060316837412204207 69763359090475256118306311)
    ·
      refine ⟨104645038635712884177459467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69763359090475256118306311 104645038635712884177459467)
      ·
        refine ⟨156967557953569326266189201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104645038635712884177459467 156967557953569326266189201)
        ·
          refine ⟨117725668465176994699641901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156967557953569326266189201 117725668465176994699641901)
          ·
            refine ⟨44147125674441373012365713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117725668465176994699641901 44147125674441373012365713)
            ·
              refine ⟨33110344255831029759274285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44147125674441373012365713 33110344255831029759274285)
              ·
                refine ⟨12416379095936636159727857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33110344255831029759274285 12416379095936636159727857)
                ·
                  refine ⟨9312284321952477119795893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12416379095936636159727857 9312284321952477119795893)
                  ·
                    refine ⟨873026655183044729980865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9312284321952477119795893 873026655183044729980865)
                    ·
                      rfl

theorem cell22_2550320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_2550320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550320 prefixEnd_2550320 := by exact prefixLift 2550320
  have htrace : WordTrace (prefixWord ++ tailWord_2550320) baseStart_2550320 baseEnd_2550320 := by
    simpa [prefixWord, tailWord_2550320, baseEnd_2550320] using wordTrace_append hprefix tailTrace_2550320
  have hstable : (prefixWord ++ tailWord_2550320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550320).length < 2 ^ (prefixWord ++ tailWord_2550320).sum := by decide
  have hdescent : baseEnd_2550320 < baseStart_2550320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550433 : List Nat := [1, 2, 3, 3, 3, 1, 3, 1, 2, 3]
def baseStart_2550433 : Nat := 118140960795 + 2550433 * 2 ^ 59
def prefixEnd_2550433 : Nat := 4983230072969 + 3 ^ 40 * 2550433 * 2
def baseEnd_2550433 : Nat := 873065337392350101905519

theorem tailTrace_2550433 : CollatzResearch.WordTrace tailWord_2550433 prefixEnd_2550433 873065337392350101905519 := by
  unfold tailWord_2550433
  simp only [CollatzResearch.WordTrace]
  refine ⟨93021933569224295123271953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62014622379482863415514635 93021933569224295123271953)
  ·
    refine ⟨69766450176918221342453965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93021933569224295123271953 69766450176918221342453965)
    ·
      refine ⟨26162418816344333003420237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69766450176918221342453965 26162418816344333003420237)
      ·
        refine ⟨9810907056129124876282589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26162418816344333003420237 9810907056129124876282589)
        ·
          refine ⟨3679090146048421828605971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9810907056129124876282589 3679090146048421828605971)
          ·
            refine ⟨5518635219072632742908957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3679090146048421828605971 5518635219072632742908957)
            ·
              refine ⟨2069488207152237278590859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5518635219072632742908957 2069488207152237278590859)
              ·
                refine ⟨3104232310728355917886289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2069488207152237278590859 3104232310728355917886289)
                ·
                  refine ⟨2328174233046266938414717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3104232310728355917886289 2328174233046266938414717)
                  ·
                    refine ⟨873065337392350101905519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2328174233046266938414717 873065337392350101905519)
                    ·
                      rfl

theorem cell22_2550433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_2550433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550433 prefixEnd_2550433 := by exact prefixLift 2550433
  have htrace : WordTrace (prefixWord ++ tailWord_2550433) baseStart_2550433 baseEnd_2550433 := by
    simpa [prefixWord, tailWord_2550433, baseEnd_2550433] using wordTrace_append hprefix tailTrace_2550433
  have hstable : (prefixWord ++ tailWord_2550433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550433).length < 2 ^ (prefixWord ++ tailWord_2550433).sum := by decide
  have hdescent : baseEnd_2550433 < baseStart_2550433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550446 : List Nat := [4, 1, 4, 1, 1, 1, 4, 6]
def baseStart_2550446 : Nat := 118140960795 + 2550446 * 2 ^ 59
def prefixEnd_2550446 : Nat := 4983230072969 + 3 ^ 40 * 2550446 * 2
def baseEnd_2550446 : Nat := 97007754173113600147831

theorem tailTrace_2550446 : CollatzResearch.WordTrace tailWord_2550446 prefixEnd_2550446 97007754173113600147831 := by
  unfold tailWord_2550446
  simp only [CollatzResearch.WordTrace]
  refine ⟨11627800964772149792936899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62014938478784798895663461 11627800964772149792936899)
  ·
    refine ⟨17441701447158224689405349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11627800964772149792936899 17441701447158224689405349)
    ·
      refine ⟨3270319021342167129263503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17441701447158224689405349 3270319021342167129263503)
      ·
        refine ⟨4905478532013250693895255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3270319021342167129263503 4905478532013250693895255)
        ·
          refine ⟨7358217798019876040842883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4905478532013250693895255 7358217798019876040842883)
          ·
            refine ⟨11037326697029814061264325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7358217798019876040842883 11037326697029814061264325)
            ·
              refine ⟨2069498755693090136487061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11037326697029814061264325 2069498755693090136487061)
              ·
                refine ⟨97007754173113600147831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2069498755693090136487061 97007754173113600147831)
                ·
                  rfl

theorem cell22_2550446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_2550446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550446 prefixEnd_2550446 := by exact prefixLift 2550446
  have htrace : WordTrace (prefixWord ++ tailWord_2550446) baseStart_2550446 baseEnd_2550446 := by
    simpa [prefixWord, tailWord_2550446, baseEnd_2550446] using wordTrace_append hprefix tailTrace_2550446
  have hstable : (prefixWord ++ tailWord_2550446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550446).length < 2 ^ (prefixWord ++ tailWord_2550446).sum := by decide
  have hdescent : baseEnd_2550446 < baseStart_2550446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550519 : List Nat := [1, 1, 3, 1, 1, 1, 3, 7, 4]
def baseStart_2550519 : Nat := 118140960795 + 2550519 * 2 ^ 59
def prefixEnd_2550519 : Nat := 4983230072969 + 3 ^ 40 * 2550519 * 2
def baseEnd_2550519 : Nat := 291031592316624848085085

theorem tailTrace_2550519 : CollatzResearch.WordTrace tailWord_2550519 prefixEnd_2550519 291031592316624848085085 := by
  unfold tailWord_2550519
  simp only [CollatzResearch.WordTrace]
  refine ⟨93025070246912731810902611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62016713497941821207268407 93025070246912731810902611)
  ·
    refine ⟨139537605370369097716353917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93025070246912731810902611 139537605370369097716353917)
    ·
      refine ⟨52326602013888411643632719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139537605370369097716353917 52326602013888411643632719)
      ·
        refine ⟨78489903020832617465449079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52326602013888411643632719 78489903020832617465449079)
        ·
          refine ⟨117734854531248926198173619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78489903020832617465449079 117734854531248926198173619)
          ·
            refine ⟨176602281796873389297260429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117734854531248926198173619 176602281796873389297260429)
            ·
              refine ⟨66225855673827520986472661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176602281796873389297260429 66225855673827520986472661)
              ·
                refine ⟨1552168492355332523120453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 66225855673827520986472661 1552168492355332523120453)
                ·
                  refine ⟨291031592316624848085085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1552168492355332523120453 291031592316624848085085)
                  ·
                    rfl

theorem cell22_2550519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 4].length) (baseStart_2550519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550519 prefixEnd_2550519 := by exact prefixLift 2550519
  have htrace : WordTrace (prefixWord ++ tailWord_2550519) baseStart_2550519 baseEnd_2550519 := by
    simpa [prefixWord, tailWord_2550519, baseEnd_2550519] using wordTrace_append hprefix tailTrace_2550519
  have hstable : (prefixWord ++ tailWord_2550519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550519).length < 2 ^ (prefixWord ++ tailWord_2550519).sum := by decide
  have hdescent : baseEnd_2550519 < baseStart_2550519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550536 : List Nat := [2, 1, 3, 2, 2, 3, 1, 4, 4]
def baseStart_2550536 : Nat := 118140960795 + 2550536 * 2 ^ 59
def prefixEnd_2550536 : Nat := 4983230072969 + 3 ^ 40 * 2550536 * 2
def baseEnd_2550536 : Nat := 291033532132430722193401

theorem tailTrace_2550536 : CollatzResearch.WordTrace tailWord_2550536 prefixEnd_2550536 291033532132430722193401 := by
  unfold tailWord_2550536
  simp only [CollatzResearch.WordTrace]
  refine ⟨46512845143925571857135731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62017126858567429142847641 46512845143925571857135731)
  ·
    refine ⟨69769267715888357785703597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46512845143925571857135731 69769267715888357785703597)
    ·
      refine ⟨26163475393458134169638849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69769267715888357785703597 26163475393458134169638849)
      ·
        refine ⟨19622606545093600627229137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26163475393458134169638849 19622606545093600627229137)
        ·
          refine ⟨14716954908820200470421853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19622606545093600627229137 14716954908820200470421853)
          ·
            refine ⟨5518858090807575176408195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14716954908820200470421853 5518858090807575176408195)
            ·
              refine ⟨8278287136211362764612293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5518858090807575176408195 8278287136211362764612293)
              ·
                refine ⟨1552178838039630518364805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8278287136211362764612293 1552178838039630518364805)
                ·
                  refine ⟨291033532132430722193401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1552178838039630518364805 291033532132430722193401)
                  ·
                    rfl

theorem cell22_2550536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 4].length) (baseStart_2550536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550536 prefixEnd_2550536 := by exact prefixLift 2550536
  have htrace : WordTrace (prefixWord ++ tailWord_2550536) baseStart_2550536 baseEnd_2550536 := by
    simpa [prefixWord, tailWord_2550536, baseEnd_2550536] using wordTrace_append hprefix tailTrace_2550536
  have hstable : (prefixWord ++ tailWord_2550536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550536).length < 2 ^ (prefixWord ++ tailWord_2550536).sum := by decide
  have hdescent : baseEnd_2550536 < baseStart_2550536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550551 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 1, 5]
def baseStart_2550551 : Nat := 118140960795 + 2550551 * 2 ^ 59
def prefixEnd_2550551 : Nat := 4983230072969 + 3 ^ 40 * 2550551 * 2
def baseEnd_2550551 : Nat := 873105731203837127455157

theorem tailTrace_2550551 : CollatzResearch.WordTrace tailWord_2550551 prefixEnd_2550551 873105731203837127455157 := by
  unfold tailWord_2550551
  simp only [CollatzResearch.WordTrace]
  refine ⟨93026237382796801276067507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62017491588531200850711671 93026237382796801276067507)
  ·
    refine ⟨139539356074195201914101261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93026237382796801276067507 139539356074195201914101261)
    ·
      refine ⟨52327258527823200717787973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139539356074195201914101261 52327258527823200717787973)
      ·
        refine ⟨9811360973966850134585245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52327258527823200717787973 9811360973966850134585245)
        ·
          refine ⟨3679260365237568800469467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9811360973966850134585245 3679260365237568800469467)
          ·
            refine ⟨5518890547856353200704201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3679260365237568800469467 5518890547856353200704201)
            ·
              refine ⟨4139167910892264900528151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5518890547856353200704201 4139167910892264900528151)
              ·
                refine ⟨6208751866338397350792227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4139167910892264900528151 6208751866338397350792227)
                ·
                  refine ⟨9313127799507596026188341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6208751866338397350792227 9313127799507596026188341)
                  ·
                    refine ⟨873105731203837127455157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9313127799507596026188341 873105731203837127455157)
                    ·
                      rfl

theorem cell22_2550551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_2550551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550551 prefixEnd_2550551 := by exact prefixLift 2550551
  have htrace : WordTrace (prefixWord ++ tailWord_2550551) baseStart_2550551 baseEnd_2550551 := by
    simpa [prefixWord, tailWord_2550551, baseEnd_2550551] using wordTrace_append hprefix tailTrace_2550551
  have hstable : (prefixWord ++ tailWord_2550551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550551).length < 2 ^ (prefixWord ++ tailWord_2550551).sum := by decide
  have hdescent : baseEnd_2550551 < baseStart_2550551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550570 : List Nat := [3, 1, 4, 3, 1, 1, 2, 3, 4]
def baseStart_2550570 : Nat := 118140960795 + 2550570 * 2 ^ 59
def prefixEnd_2550570 : Nat := 4983230072969 + 3 ^ 40 * 2550570 * 2
def baseEnd_2550570 : Nat := 291037411764042470410033

theorem tailTrace_2550570 : CollatzResearch.WordTrace tailWord_2550570 prefixEnd_2550570 291037411764042470410033 := by
  unfold tailWord_2550570
  simp only [CollatzResearch.WordTrace]
  refine ⟨23256732592431991880252291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62017953579818645014006109 23256732592431991880252291)
  ·
    refine ⟨34885098888647987820378437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23256732592431991880252291 34885098888647987820378437)
    ·
      refine ⟨6540956041621497716320957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34885098888647987820378437 6540956041621497716320957)
      ·
        refine ⟨2452858515608061643620359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6540956041621497716320957 2452858515608061643620359)
        ·
          refine ⟨3679287773412092465430539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2452858515608061643620359 3679287773412092465430539)
          ·
            refine ⟨5518931660118138698145809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3679287773412092465430539 5518931660118138698145809)
            ·
              refine ⟨4139198745088604023609357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5518931660118138698145809 4139198745088604023609357)
              ·
                refine ⟨1552199529408226508853509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4139198745088604023609357 1552199529408226508853509)
                ·
                  refine ⟨291037411764042470410033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1552199529408226508853509 291037411764042470410033)
                  ·
                    rfl

theorem cell22_2550570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_2550570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550570 prefixEnd_2550570 := by exact prefixLift 2550570
  have htrace : WordTrace (prefixWord ++ tailWord_2550570) baseStart_2550570 baseEnd_2550570 := by
    simpa [prefixWord, tailWord_2550570, baseEnd_2550570] using wordTrace_append hprefix tailTrace_2550570
  have hstable : (prefixWord ++ tailWord_2550570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550570).length < 2 ^ (prefixWord ++ tailWord_2550570).sum := by decide
  have hdescent : baseEnd_2550570 < baseStart_2550570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550690 : List Nat := [3, 3, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_2550690 : Nat := 118140960795 + 2550690 * 2 ^ 59
def prefixEnd_2550690 : Nat := 4983230072969 + 3 ^ 40 * 2550690 * 2
def baseEnd_2550690 : Nat := 873153313744487098229731

theorem tailTrace_2550690 : CollatzResearch.WordTrace tailWord_2550690 prefixEnd_2550690 873153313744487098229731 := by
  unfold tailWord_2550690
  simp only [CollatzResearch.WordTrace]
  refine ⟨23257826782323307003844381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62020871419528818676918349 23257826782323307003844381)
  ·
    refine ⟨8721685043371240126441643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23257826782323307003844381 8721685043371240126441643)
    ·
      refine ⟨13082527565056860189662465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8721685043371240126441643 13082527565056860189662465)
      ·
        refine ⟨9811895673792645142246849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13082527565056860189662465 9811895673792645142246849)
        ·
          refine ⟨7358921755344483856685137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9811895673792645142246849 7358921755344483856685137)
          ·
            refine ⟨5519191316508362892513853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7358921755344483856685137 5519191316508362892513853)
            ·
              refine ⟨2069696743690636084692695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5519191316508362892513853 2069696743690636084692695)
              ·
                refine ⟨3104545115535954127039043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2069696743690636084692695 3104545115535954127039043)
                ·
                  refine ⟨4656817673303931190558565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3104545115535954127039043 4656817673303931190558565)
                  ·
                    refine ⟨873153313744487098229731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4656817673303931190558565 873153313744487098229731)
                    ·
                      rfl

theorem cell22_2550690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_2550690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550690 prefixEnd_2550690 := by exact prefixLift 2550690
  have htrace : WordTrace (prefixWord ++ tailWord_2550690) baseStart_2550690 baseEnd_2550690 := by
    simpa [prefixWord, tailWord_2550690, baseEnd_2550690] using wordTrace_append hprefix tailTrace_2550690
  have hstable : (prefixWord ++ tailWord_2550690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550690).length < 2 ^ (prefixWord ++ tailWord_2550690).sum := by decide
  have hdescent : baseEnd_2550690 < baseStart_2550690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550731 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 5, 3]
def baseStart_2550731 : Nat := 118140960795 + 2550731 * 2 ^ 59
def prefixEnd_2550731 : Nat := 4983230072969 + 3 ^ 40 * 2550731 * 2
def baseEnd_2550731 : Nat := 873167348882376657954605

theorem tailTrace_2550731 : CollatzResearch.WordTrace tailWord_2550731 prefixEnd_2550731 873167348882376657954605 := by
  unfold tailWord_2550731
  simp only [CollatzResearch.WordTrace]
  refine ⟨93032802522144692017620047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62021868348096461345080031 93032802522144692017620047)
  ·
    refine ⟨139549203783217038026430071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93032802522144692017620047 139549203783217038026430071)
    ·
      refine ⟨209323805674825557039645107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139549203783217038026430071 209323805674825557039645107)
      ·
        refine ⟨313985708512238335559467661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209323805674825557039645107 313985708512238335559467661)
        ·
          refine ⟨117744640692089375834800373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313985708512238335559467661 117744640692089375834800373)
          ·
            refine ⟨11038560064883378984512535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117744640692089375834800373 11038560064883378984512535)
            ·
              refine ⟨16557840097325068476768803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11038560064883378984512535 16557840097325068476768803)
              ·
                refine ⟨24836760145987602715153205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16557840097325068476768803 24836760145987602715153205)
                ·
                  refine ⟨2328446263686337754545613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24836760145987602715153205 2328446263686337754545613)
                  ·
                    refine ⟨873167348882376657954605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2328446263686337754545613 873167348882376657954605)
                    ·
                      rfl

theorem cell22_2550731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 3].length) (baseStart_2550731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550731 prefixEnd_2550731 := by exact prefixLift 2550731
  have htrace : WordTrace (prefixWord ++ tailWord_2550731) baseStart_2550731 baseEnd_2550731 := by
    simpa [prefixWord, tailWord_2550731, baseEnd_2550731] using wordTrace_append hprefix tailTrace_2550731
  have hstable : (prefixWord ++ tailWord_2550731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550731).length < 2 ^ (prefixWord ++ tailWord_2550731).sum := by decide
  have hdescent : baseEnd_2550731 < baseStart_2550731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550808 : List Nat := [2, 1, 2, 3, 2, 2, 2, 3, 1, 4]
def baseStart_2550808 : Nat := 118140960795 + 2550808 * 2 ^ 59
def prefixEnd_2550808 : Nat := 4983230072969 + 3 ^ 40 * 2550808 * 2
def baseEnd_2550808 : Nat := 873193707555974123779369

theorem tailTrace_2550808 : CollatzResearch.WordTrace tailWord_2550808 prefixEnd_2550808 873193707555974123779369 := by
  unfold tailWord_2550808
  simp only [CollatzResearch.WordTrace]
  refine ⟨46517805471432867084086539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62023740628577156112115385 46517805471432867084086539)
  ·
    refine ⟨69776708207149300626129809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46517805471432867084086539 69776708207149300626129809)
    ·
      refine ⟨52332531155361975469597357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69776708207149300626129809 52332531155361975469597357)
      ·
        refine ⟨19624699183260740801099009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52332531155361975469597357 19624699183260740801099009)
        ·
          refine ⟨14718524387445555600824257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19624699183260740801099009 14718524387445555600824257)
          ·
            refine ⟨11038893290584166700618193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14718524387445555600824257 11038893290584166700618193)
            ·
              refine ⟨8279169967938125025463645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11038893290584166700618193 8279169967938125025463645)
              ·
                refine ⟨3104688737976796884548867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8279169967938125025463645 3104688737976796884548867)
                ·
                  refine ⟨4657033106965195326823301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3104688737976796884548867 4657033106965195326823301)
                  ·
                    refine ⟨873193707555974123779369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4657033106965195326823301 873193707555974123779369)
                    ·
                      rfl

theorem cell22_2550808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_2550808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550808 prefixEnd_2550808 := by exact prefixLift 2550808
  have htrace : WordTrace (prefixWord ++ tailWord_2550808) baseStart_2550808 baseEnd_2550808 := by
    simpa [prefixWord, tailWord_2550808, baseEnd_2550808] using wordTrace_append hprefix tailTrace_2550808
  have hstable : (prefixWord ++ tailWord_2550808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550808).length < 2 ^ (prefixWord ++ tailWord_2550808).sum := by decide
  have hdescent : baseEnd_2550808 < baseStart_2550808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550881 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 2, 6]
def baseStart_2550881 : Nat := 118140960795 + 2550881 * 2 ^ 59
def prefixEnd_2550881 : Nat := 4983230072969 + 3 ^ 40 * 2550881 * 2
def baseEnd_2550881 : Nat := 873218696947826266704145

theorem tailTrace_2550881 : CollatzResearch.WordTrace tailWord_2550881 prefixEnd_2550881 873218696947826266704145 := by
  unfold tailWord_2550881
  simp only [CollatzResearch.WordTrace]
  refine ⟨93038273471601267635580497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62025515647734178423720331 93038273471601267635580497)
  ·
    refine ⟨69778705103700950726685373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93038273471601267635580497 69778705103700950726685373)
    ·
      refine ⟨26167014413887856522507015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69778705103700950726685373 26167014413887856522507015)
      ·
        refine ⟨39250521620831784783760523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26167014413887856522507015 39250521620831784783760523)
        ·
          refine ⟨58875782431247677175640785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39250521620831784783760523 58875782431247677175640785)
          ·
            refine ⟨44156836823435757881730589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58875782431247677175640785 44156836823435757881730589)
            ·
              refine ⟨16558813808788409205648971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44156836823435757881730589 16558813808788409205648971)
              ·
                refine ⟨24838220713182613808473457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16558813808788409205648971 24838220713182613808473457)
                ·
                  refine ⟨18628665534886960356355093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24838220713182613808473457 18628665534886960356355093)
                  ·
                    refine ⟨873218696947826266704145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18628665534886960356355093 873218696947826266704145)
                    ·
                      rfl

theorem cell22_2550881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_2550881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550881 prefixEnd_2550881 := by exact prefixLift 2550881
  have htrace : WordTrace (prefixWord ++ tailWord_2550881) baseStart_2550881 baseEnd_2550881 := by
    simpa [prefixWord, tailWord_2550881, baseEnd_2550881] using wordTrace_append hprefix tailTrace_2550881
  have hstable : (prefixWord ++ tailWord_2550881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550881).length < 2 ^ (prefixWord ++ tailWord_2550881).sum := by decide
  have hdescent : baseEnd_2550881 < baseStart_2550881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550883 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 3, 3]
def baseStart_2550883 : Nat := 118140960795 + 2550883 * 2 ^ 59
def prefixEnd_2550883 : Nat := 4983230072969 + 3 ^ 40 * 2550883 * 2
def baseEnd_2550883 : Nat := 873219381588698928154139

theorem tailTrace_2550883 : CollatzResearch.WordTrace tailWord_2550883 prefixEnd_2550883 873219381588698928154139 := by
  unfold tailWord_2550883
  simp only [CollatzResearch.WordTrace]
  refine ⟨93038346417594021977153303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62025564278396014651435535 93038346417594021977153303)
  ·
    refine ⟨139557519626391032965729955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93038346417594021977153303 139557519626391032965729955)
    ·
      refine ⟨209336279439586549448594933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139557519626391032965729955 209336279439586549448594933)
      ·
        refine ⟨19625276197461239010805775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 209336279439586549448594933 19625276197461239010805775)
        ·
          refine ⟨29437914296191858516208663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19625276197461239010805775 29437914296191858516208663)
          ·
            refine ⟨44156871444287787774312995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29437914296191858516208663 44156871444287787774312995)
            ·
              refine ⟨66235307166431681661469493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44156871444287787774312995 66235307166431681661469493)
              ·
                refine ⟨6209560046852970155762765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66235307166431681661469493 6209560046852970155762765)
                ·
                  refine ⟨2328585017569863808411037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6209560046852970155762765 2328585017569863808411037)
                  ·
                    refine ⟨873219381588698928154139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2328585017569863808411037 873219381588698928154139)
                    ·
                      rfl

theorem cell22_2550883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 3].length) (baseStart_2550883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550883 prefixEnd_2550883 := by exact prefixLift 2550883
  have htrace : WordTrace (prefixWord ++ tailWord_2550883) baseStart_2550883 baseEnd_2550883 := by
    simpa [prefixWord, tailWord_2550883, baseEnd_2550883] using wordTrace_append hprefix tailTrace_2550883
  have hstable : (prefixWord ++ tailWord_2550883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550883).length < 2 ^ (prefixWord ++ tailWord_2550883).sum := by decide
  have hdescent : baseEnd_2550883 < baseStart_2550883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550930 : List Nat := [3, 2, 3, 1, 1, 2, 3, 2, 5]
def baseStart_2550930 : Nat := 118140960795 + 2550930 * 2 ^ 59
def prefixEnd_2550930 : Nat := 4983230072969 + 3 ^ 40 * 2550930 * 2
def baseEnd_2550930 : Nat := 291078490216402157409665

theorem tailTrace_2550930 : CollatzResearch.WordTrace tailWord_2550930 prefixEnd_2550930 291078490216402157409665 := by
  unfold tailWord_2550930
  simp only [CollatzResearch.WordTrace]
  refine ⟨23260015162105937251028561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62026707098949166002742829 23260015162105937251028561)
  ·
    refine ⟨17445011371579452938271421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23260015162105937251028561 17445011371579452938271421)
    ·
      refine ⟨6541879264342294851851783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17445011371579452938271421 6541879264342294851851783)
      ·
        refine ⟨9812818896513442277777675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6541879264342294851851783 9812818896513442277777675)
        ·
          refine ⟨14719228344770163416666513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9812818896513442277777675 14719228344770163416666513)
          ·
            refine ⟨11039421258577622562499885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14719228344770163416666513 11039421258577622562499885)
            ·
              refine ⟨4139782971966608460937457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11039421258577622562499885 4139782971966608460937457)
              ·
                refine ⟨3104837228974956345703093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4139782971966608460937457 3104837228974956345703093)
                ·
                  refine ⟨291078490216402157409665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3104837228974956345703093 291078490216402157409665)
                  ·
                    rfl

theorem cell22_2550930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_2550930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550930 prefixEnd_2550930 := by exact prefixLift 2550930
  have htrace : WordTrace (prefixWord ++ tailWord_2550930) baseStart_2550930 baseEnd_2550930 := by
    simpa [prefixWord, tailWord_2550930, baseEnd_2550930] using wordTrace_append hprefix tailTrace_2550930
  have hstable : (prefixWord ++ tailWord_2550930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550930).length < 2 ^ (prefixWord ++ tailWord_2550930).sum := by decide
  have hdescent : baseEnd_2550930 < baseStart_2550930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550973 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_2550973 : Nat := 118140960795 + 2550973 * 2 ^ 59
def prefixEnd_2550973 : Nat := 4983230072969 + 3 ^ 40 * 2550973 * 2
def baseEnd_2550973 : Nat := 873250190427968693403863

theorem tailTrace_2550973 : CollatzResearch.WordTrace tailWord_2550973 prefixEnd_2550973 873250190427968693403863 := by
  unfold tailWord_2550973
  simp only [CollatzResearch.WordTrace]
  refine ⟨93041628987267967347929573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62027752658178644898619715 93041628987267967347929573)
  ·
    refine ⟨17445305435112743877736795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93041628987267967347929573 17445305435112743877736795)
    ·
      refine ⟨26167958152669115816605193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17445305435112743877736795 26167958152669115816605193)
      ·
        refine ⟨19625968614501836862453895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26167958152669115816605193 19625968614501836862453895)
        ·
          refine ⟨29438952921752755293680843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19625968614501836862453895 29438952921752755293680843)
          ·
            refine ⟨44158429382629132940521265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29438952921752755293680843 44158429382629132940521265)
            ·
              refine ⟨33118822036971849705390949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44158429382629132940521265 33118822036971849705390949)
              ·
                refine ⟨6209779131932221819760803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33118822036971849705390949 6209779131932221819760803)
                ·
                  refine ⟨9314668697898332729641205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6209779131932221819760803 9314668697898332729641205)
                  ·
                    refine ⟨873250190427968693403863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9314668697898332729641205 873250190427968693403863)
                    ·
                      rfl

theorem cell22_2550973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_2550973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550973 prefixEnd_2550973 := by exact prefixLift 2550973
  have htrace : WordTrace (prefixWord ++ tailWord_2550973) baseStart_2550973 baseEnd_2550973 := by
    simpa [prefixWord, tailWord_2550973, baseEnd_2550973] using wordTrace_append hprefix tailTrace_2550973
  have hstable : (prefixWord ++ tailWord_2550973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550973).length < 2 ^ (prefixWord ++ tailWord_2550973).sum := by decide
  have hdescent : baseEnd_2550973 < baseStart_2550973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550975 : List Nat := [1, 1, 2, 2, 2, 2, 5, 3, 4]
def baseStart_2550975 : Nat := 118140960795 + 2550975 * 2 ^ 59
def prefixEnd_2550975 : Nat := 4983230072969 + 3 ^ 40 * 2550975 * 2
def baseEnd_2550975 : Nat := 291083625022947118284619

theorem tailTrace_2550975 : CollatzResearch.WordTrace tailWord_2550975 prefixEnd_2550975 291083625022947118284619 := by
  unfold tailWord_2550975
  simp only [CollatzResearch.WordTrace]
  refine ⟨93041701933260721689502379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62027801288840481126334919 93041701933260721689502379)
  ·
    refine ⟨139562552899891082534253569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93041701933260721689502379 139562552899891082534253569)
    ·
      refine ⟨104671914674918311900690177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139562552899891082534253569 104671914674918311900690177)
      ·
        refine ⟨78503936006188733925517633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104671914674918311900690177 78503936006188733925517633)
        ·
          refine ⟨58877952004641550444138225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78503936006188733925517633 58877952004641550444138225)
          ·
            refine ⟨44158464003481162833103669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58877952004641550444138225 44158464003481162833103669)
            ·
              refine ⟨4139856000326359015603469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44158464003481162833103669 4139856000326359015603469)
              ·
                refine ⟨1552446000122384630851301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4139856000326359015603469 1552446000122384630851301)
                ·
                  refine ⟨291083625022947118284619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1552446000122384630851301 291083625022947118284619)
                  ·
                    rfl

theorem cell22_2550975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 4].length) (baseStart_2550975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550975 prefixEnd_2550975 := by exact prefixLift 2550975
  have htrace : WordTrace (prefixWord ++ tailWord_2550975) baseStart_2550975 baseEnd_2550975 := by
    simpa [prefixWord, tailWord_2550975, baseEnd_2550975] using wordTrace_append hprefix tailTrace_2550975
  have hstable : (prefixWord ++ tailWord_2550975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550975).length < 2 ^ (prefixWord ++ tailWord_2550975).sum := by decide
  have hdescent : baseEnd_2550975 < baseStart_2550975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2550977 : List Nat := [1, 2, 6, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2550977 : Nat := 118140960795 + 2550977 * 2 ^ 59
def prefixEnd_2550977 : Nat := 4983230072969 + 3 ^ 40 * 2550977 * 2
def baseEnd_2550977 : Nat := 873251559709714016303851

theorem tailTrace_2550977 : CollatzResearch.WordTrace tailWord_2550977 prefixEnd_2550977 873251559709714016303851 := by
  unfold tailWord_2550977
  simp only [CollatzResearch.WordTrace]
  refine ⟨93041774879253476031075185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62027849919502317354050123 93041774879253476031075185)
  ·
    refine ⟨69781331159440107023306389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93041774879253476031075185 69781331159440107023306389)
    ·
      refine ⟨3270999898098755016717487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69781331159440107023306389 3270999898098755016717487)
      ·
        refine ⟨4906499847148132525076231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3270999898098755016717487 4906499847148132525076231)
        ·
          refine ⟨7359749770722198787614347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4906499847148132525076231 7359749770722198787614347)
          ·
            refine ⟨11039624656083298181421521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7359749770722198787614347 11039624656083298181421521)
            ·
              refine ⟨8279718492062473636066141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11039624656083298181421521 8279718492062473636066141)
              ·
                refine ⟨3104894434523427613524803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8279718492062473636066141 3104894434523427613524803)
                ·
                  refine ⟨4657341651785141420287205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3104894434523427613524803 4657341651785141420287205)
                  ·
                    refine ⟨873251559709714016303851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4657341651785141420287205 873251559709714016303851)
                    ·
                      rfl

theorem cell22_2550977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2550977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2550977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2550977 prefixEnd_2550977 := by exact prefixLift 2550977
  have htrace : WordTrace (prefixWord ++ tailWord_2550977) baseStart_2550977 baseEnd_2550977 := by
    simpa [prefixWord, tailWord_2550977, baseEnd_2550977] using wordTrace_append hprefix tailTrace_2550977
  have hstable : (prefixWord ++ tailWord_2550977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2550977).length < 2 ^ (prefixWord ++ tailWord_2550977).sum := by decide
  have hdescent : baseEnd_2550977 < baseStart_2550977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2550977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551007 : List Nat := [1, 1, 2, 3, 2, 1, 6, 1, 2, 3]
def baseStart_2551007 : Nat := 118140960795 + 2551007 * 2 ^ 59
def prefixEnd_2551007 : Nat := 4983230072969 + 3 ^ 40 * 2551007 * 2
def baseEnd_2551007 : Nat := 873261829322803938053759

theorem tailTrace_2551007 : CollatzResearch.WordTrace tailWord_2551007 prefixEnd_2551007 873261829322803938053759 := by
  unfold tailWord_2551007
  simp only [CollatzResearch.WordTrace]
  refine ⟨93042869069144791154667275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62028579379429860769778183 93042869069144791154667275)
  ·
    refine ⟨139564303603717186732000913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93042869069144791154667275 139564303603717186732000913)
    ·
      refine ⟨104673227702787890049000685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139564303603717186732000913 104673227702787890049000685)
      ·
        refine ⟨39252460388545458768375257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104673227702787890049000685 39252460388545458768375257)
        ·
          refine ⟨29439345291409094076281443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39252460388545458768375257 29439345291409094076281443)
          ·
            refine ⟨44159017937113641114422165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29439345291409094076281443 44159017937113641114422165)
            ·
              refine ⟨2069953965802201927238539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44159017937113641114422165 2069953965802201927238539)
              ·
                refine ⟨3104930948703302890857809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2069953965802201927238539 3104930948703302890857809)
                ·
                  refine ⟨2328698211527477168143357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3104930948703302890857809 2328698211527477168143357)
                  ·
                    refine ⟨873261829322803938053759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2328698211527477168143357 873261829322803938053759)
                    ·
                      rfl

theorem cell22_2551007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 2, 3].length) (baseStart_2551007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551007 prefixEnd_2551007 := by exact prefixLift 2551007
  have htrace : WordTrace (prefixWord ++ tailWord_2551007) baseStart_2551007 baseEnd_2551007 := by
    simpa [prefixWord, tailWord_2551007, baseEnd_2551007] using wordTrace_append hprefix tailTrace_2551007
  have hstable : (prefixWord ++ tailWord_2551007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551007).length < 2 ^ (prefixWord ++ tailWord_2551007).sum := by decide
  have hdescent : baseEnd_2551007 < baseStart_2551007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551028 : List Nat := [2, 6, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_2551028 : Nat := 118140960795 + 2551028 * 2 ^ 59
def prefixEnd_2551028 : Nat := 4983230072969 + 3 ^ 40 * 2551028 * 2
def baseEnd_2551028 : Nat := 873269018051966883278695

theorem tailTrace_2551028 : CollatzResearch.WordTrace tailWord_2551028 prefixEnd_2551028 873269018051966883278695 := by
  unfold tailWord_2551028
  simp only [CollatzResearch.WordTrace]
  refine ⟨46521817501034355870590869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62029090001379141160787825 46521817501034355870590869)
  ·
    refine ⟨2180710195360985431433947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46521817501034355870590869 2180710195360985431433947)
    ·
      refine ⟨3271065293041478147150921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2180710195360985431433947 3271065293041478147150921)
      ·
        refine ⟨2453298969781108610363191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3271065293041478147150921 2453298969781108610363191)
        ·
          refine ⟨3679948454671662915544787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2453298969781108610363191 3679948454671662915544787)
          ·
            refine ⟨5519922682007494373317181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3679948454671662915544787 5519922682007494373317181)
            ·
              refine ⟨2069971005752810389993943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5519922682007494373317181 2069971005752810389993943)
              ·
                refine ⟨3104956508629215584990915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2069971005752810389993943 3104956508629215584990915)
                ·
                  refine ⟨4657434762943823377486373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3104956508629215584990915 4657434762943823377486373)
                  ·
                    refine ⟨873269018051966883278695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4657434762943823377486373 873269018051966883278695)
                    ·
                      rfl

theorem cell22_2551028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_2551028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551028 prefixEnd_2551028 := by exact prefixLift 2551028
  have htrace : WordTrace (prefixWord ++ tailWord_2551028) baseStart_2551028 baseEnd_2551028 := by
    simpa [prefixWord, tailWord_2551028, baseEnd_2551028] using wordTrace_append hprefix tailTrace_2551028
  have hstable : (prefixWord ++ tailWord_2551028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551028).length < 2 ^ (prefixWord ++ tailWord_2551028).sum := by decide
  have hdescent : baseEnd_2551028 < baseStart_2551028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551123 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 3, 6]
def baseStart_2551123 : Nat := 118140960795 + 2551123 * 2 ^ 59
def prefixEnd_2551123 : Nat := 4983230072969 + 3 ^ 40 * 2551123 * 2
def baseEnd_2551123 : Nat := 873301538493418302153403

theorem tailTrace_2551123 : CollatzResearch.WordTrace tailWord_2551123 prefixEnd_2551123 873301538493418302153403 := by
  unfold tailWord_2551123
  simp only [CollatzResearch.WordTrace]
  refine ⟨93047099936724542965890023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62031399957816361977260015 93047099936724542965890023)
  ·
    refine ⟨139570649905086814448835035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93047099936724542965890023 139570649905086814448835035)
    ·
      refine ⟨209355974857630221673252553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139570649905086814448835035 209355974857630221673252553)
      ·
        refine ⟨157016981143222666254939415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209355974857630221673252553 157016981143222666254939415)
        ·
          refine ⟨235525471714833999382409123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157016981143222666254939415 235525471714833999382409123)
          ·
            refine ⟨353288207572250999073613685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235525471714833999382409123 353288207572250999073613685)
            ·
              refine ⟨33120769459898531163151283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 353288207572250999073613685 33120769459898531163151283)
              ·
                refine ⟨49681154189847796744726925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33120769459898531163151283 49681154189847796744726925)
                ·
                  refine ⟨18630432821192923779272597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49681154189847796744726925 18630432821192923779272597)
                  ·
                    refine ⟨873301538493418302153403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18630432821192923779272597 873301538493418302153403)
                    ·
                      rfl

theorem cell22_2551123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 6].length) (baseStart_2551123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551123 prefixEnd_2551123 := by exact prefixLift 2551123
  have htrace : WordTrace (prefixWord ++ tailWord_2551123) baseStart_2551123 baseEnd_2551123 := by
    simpa [prefixWord, tailWord_2551123, baseEnd_2551123] using wordTrace_append hprefix tailTrace_2551123
  have hstable : (prefixWord ++ tailWord_2551123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551123).length < 2 ^ (prefixWord ++ tailWord_2551123).sum := by decide
  have hdescent : baseEnd_2551123 < baseStart_2551123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551140 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_2551140 : Nat := 118140960795 + 2551140 * 2 ^ 59
def prefixEnd_2551140 : Nat := 4983230072969 + 3 ^ 40 * 2551140 * 2
def baseEnd_2551140 : Nat := 873307357940835924478351

theorem tailTrace_2551140 : CollatzResearch.WordTrace tailWord_2551140 prefixEnd_2551140 873307357940835924478351 := by
  unfold tailWord_2551140
  simp only [CollatzResearch.WordTrace]
  refine ⟨46523859988831477434629437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62031813318441969912839249 46523859988831477434629437)
  ·
    refine ⟨17446447495811804037986039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46523859988831477434629437 17446447495811804037986039)
    ·
      refine ⟨26169671243717706056979059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17446447495811804037986039 26169671243717706056979059)
      ·
        refine ⟨39254506865576559085468589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26169671243717706056979059 39254506865576559085468589)
        ·
          refine ⟨14720440074591209657050721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39254506865576559085468589 14720440074591209657050721)
          ·
            refine ⟨11040330055943407242788041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14720440074591209657050721 11040330055943407242788041)
            ·
              refine ⟨8280247541957555432091031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11040330055943407242788041 8280247541957555432091031)
              ·
                refine ⟨12420371312936333148136547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8280247541957555432091031 12420371312936333148136547)
                ·
                  refine ⟨18630556969404499722204821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12420371312936333148136547 18630556969404499722204821)
                  ·
                    refine ⟨873307357940835924478351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18630556969404499722204821 873307357940835924478351)
                    ·
                      rfl

theorem cell22_2551140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_2551140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551140 prefixEnd_2551140 := by exact prefixLift 2551140
  have htrace : WordTrace (prefixWord ++ tailWord_2551140) baseStart_2551140 baseEnd_2551140 := by
    simpa [prefixWord, tailWord_2551140, baseEnd_2551140] using wordTrace_append hprefix tailTrace_2551140
  have hstable : (prefixWord ++ tailWord_2551140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551140).length < 2 ^ (prefixWord ++ tailWord_2551140).sum := by decide
  have hdescent : baseEnd_2551140 < baseStart_2551140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551176 : List Nat := [2, 1, 3, 3, 1, 4, 2, 1, 2, 3]
def baseStart_2551176 : Nat := 118140960795 + 2551176 * 2 ^ 59
def prefixEnd_2551176 : Nat := 4983230072969 + 3 ^ 40 * 2551176 * 2
def baseEnd_2551176 : Nat := 873319681476543830578241

theorem tailTrace_2551176 : CollatzResearch.WordTrace tailWord_2551176 prefixEnd_2551176 873319681476543830578241 := by
  unfold tailWord_2551176
  simp only [CollatzResearch.WordTrace]
  refine ⟨46524516502766266508784691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62032688670355022011712921 46524516502766266508784691)
  ·
    refine ⟨69786774754149399763177037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46524516502766266508784691 69786774754149399763177037)
    ·
      refine ⟨26170040532806024911191389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69786774754149399763177037 26170040532806024911191389)
      ·
        refine ⟨9813765199802259341696771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26170040532806024911191389 9813765199802259341696771)
        ·
          refine ⟨14720647799703389012545157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9813765199802259341696771 14720647799703389012545157)
          ·
            refine ⟨2760121462444385439852217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14720647799703389012545157 2760121462444385439852217)
            ·
              refine ⟨2070091096833289079889163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2760121462444385439852217 2070091096833289079889163)
              ·
                refine ⟨3105136645249933619833745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2070091096833289079889163 3105136645249933619833745)
                ·
                  refine ⟨2328852483937450214875309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3105136645249933619833745 2328852483937450214875309)
                  ·
                    refine ⟨873319681476543830578241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2328852483937450214875309 873319681476543830578241)
                    ·
                      rfl

theorem cell22_2551176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_2551176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551176 prefixEnd_2551176 := by exact prefixLift 2551176
  have htrace : WordTrace (prefixWord ++ tailWord_2551176) baseStart_2551176 baseEnd_2551176 := by
    simpa [prefixWord, tailWord_2551176, baseEnd_2551176] using wordTrace_append hprefix tailTrace_2551176
  have hstable : (prefixWord ++ tailWord_2551176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551176).length < 2 ^ (prefixWord ++ tailWord_2551176).sum := by decide
  have hdescent : baseEnd_2551176 < baseStart_2551176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551204 : List Nat := [2, 3, 1, 2, 1, 1, 1, 7, 1, 3]
def baseStart_2551204 : Nat := 118140960795 + 2551204 * 2 ^ 59
def prefixEnd_2551204 : Nat := 4983230072969 + 3 ^ 40 * 2551204 * 2
def baseEnd_2551204 : Nat := 873329266448761090878155

theorem tailTrace_2551204 : CollatzResearch.WordTrace tailWord_2551204 prefixEnd_2551204 873329266448761090878155 := by
  unfold tailWord_2551204
  simp only [CollatzResearch.WordTrace]
  refine ⟨46525027124715546899794333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62033369499620729199725777 46525027124715546899794333)
  ·
    refine ⟨17446885171768330087422875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46525027124715546899794333 17446885171768330087422875)
    ·
      refine ⟨26170327757652495131134313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17446885171768330087422875 26170327757652495131134313)
      ·
        refine ⟨19627745818239371348350735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26170327757652495131134313 19627745818239371348350735)
        ·
          refine ⟨29441618727359057022526103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19627745818239371348350735 29441618727359057022526103)
          ·
            refine ⟨44162428091038585533789155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29441618727359057022526103 44162428091038585533789155)
            ·
              refine ⟨66243642136557878300683733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44162428091038585533789155 66243642136557878300683733)
              ·
                refine ⟨1552585362575575272672275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 66243642136557878300683733 1552585362575575272672275)
                ·
                  refine ⟨2328878043863362909008413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552585362575575272672275 2328878043863362909008413)
                  ·
                    refine ⟨873329266448761090878155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2328878043863362909008413 873329266448761090878155)
                    ·
                      rfl

theorem cell22_2551204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_2551204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551204 prefixEnd_2551204 := by exact prefixLift 2551204
  have htrace : WordTrace (prefixWord ++ tailWord_2551204) baseStart_2551204 baseEnd_2551204 := by
    simpa [prefixWord, tailWord_2551204, baseEnd_2551204] using wordTrace_append hprefix tailTrace_2551204
  have hstable : (prefixWord ++ tailWord_2551204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551204).length < 2 ^ (prefixWord ++ tailWord_2551204).sum := by decide
  have hdescent : baseEnd_2551204 < baseStart_2551204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551217 : List Nat := [1, 2, 2, 4, 1, 1, 4, 2, 5]
def baseStart_2551217 : Nat := 118140960795 + 2551217 * 2 ^ 59
def prefixEnd_2551217 : Nat := 4983230072969 + 3 ^ 40 * 2551217 * 2
def baseEnd_2551217 : Nat := 291111238871477796767705

theorem tailTrace_2551217 : CollatzResearch.WordTrace tailWord_2551217 prefixEnd_2551217 291111238871477796767705 := by
  unfold tailWord_2551217
  simp only [CollatzResearch.WordTrace]
  refine ⟨93050528398383997019811905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62033685598922664679874603 93050528398383997019811905)
  ·
    refine ⟨69787896298787997764858929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93050528398383997019811905 69787896298787997764858929)
    ·
      refine ⟨52340922224090998323644197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69787896298787997764858929 52340922224090998323644197)
      ·
        refine ⟨9813922917017062185683287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52340922224090998323644197 9813922917017062185683287)
        ·
          refine ⟨14720884375525593278524931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9813922917017062185683287 14720884375525593278524931)
          ·
            refine ⟨22081326563288389917787397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14720884375525593278524931 22081326563288389917787397)
            ·
              refine ⟨4140248730616573109585137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22081326563288389917787397 4140248730616573109585137)
              ·
                refine ⟨3105186547962429832188853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4140248730616573109585137 3105186547962429832188853)
                ·
                  refine ⟨291111238871477796767705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3105186547962429832188853 291111238871477796767705)
                  ·
                    rfl

theorem cell22_2551217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 5].length) (baseStart_2551217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551217 prefixEnd_2551217 := by exact prefixLift 2551217
  have htrace : WordTrace (prefixWord ++ tailWord_2551217) baseStart_2551217 baseEnd_2551217 := by
    simpa [prefixWord, tailWord_2551217, baseEnd_2551217] using wordTrace_append hprefix tailTrace_2551217
  have hstable : (prefixWord ++ tailWord_2551217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551217).length < 2 ^ (prefixWord ++ tailWord_2551217).sum := by decide
  have hdescent : baseEnd_2551217 < baseStart_2551217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551221 : List Nat := [1, 3, 3, 2, 2, 2, 1, 4, 1, 3]
def baseStart_2551221 : Nat := 118140960795 + 2551221 * 2 ^ 59
def prefixEnd_2551221 : Nat := 4983230072969 + 3 ^ 40 * 2551221 * 2
def baseEnd_2551221 : Nat := 873335085896178713203103

theorem tailTrace_2551221 : CollatzResearch.WordTrace tailWord_2551221 prefixEnd_2551221 873335085896178713203103 := by
  unfold tailWord_2551221
  simp only [CollatzResearch.WordTrace]
  refine ⟨93050674290369505702957517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62033782860246337135305011 93050674290369505702957517)
  ·
    refine ⟨34894002858888564638609069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93050674290369505702957517 34894002858888564638609069)
    ·
      refine ⟨13085251072083211739478401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34894002858888564638609069 13085251072083211739478401)
      ·
        refine ⟨9813938304062408804608801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13085251072083211739478401 9813938304062408804608801)
        ·
          refine ⟨7360453728046806603456601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9813938304062408804608801 7360453728046806603456601)
          ·
            refine ⟨5520340296035104952592451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7360453728046806603456601 5520340296035104952592451)
            ·
              refine ⟨8280510444052657428888677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5520340296035104952592451 8280510444052657428888677)
              ·
                refine ⟨1552595708259873267916627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8280510444052657428888677 1552595708259873267916627)
                ·
                  refine ⟨2328893562389809901874941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552595708259873267916627 2328893562389809901874941)
                  ·
                    refine ⟨873335085896178713203103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2328893562389809901874941 873335085896178713203103)
                    ·
                      rfl

theorem cell22_2551221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_2551221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551221 prefixEnd_2551221 := by exact prefixLift 2551221
  have htrace : WordTrace (prefixWord ++ tailWord_2551221) baseStart_2551221 baseEnd_2551221 := by
    simpa [prefixWord, tailWord_2551221, baseEnd_2551221] using wordTrace_append hprefix tailTrace_2551221
  have hstable : (prefixWord ++ tailWord_2551221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551221).length < 2 ^ (prefixWord ++ tailWord_2551221).sum := by decide
  have hdescent : baseEnd_2551221 < baseStart_2551221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551290 : List Nat := [3, 1, 1, 1, 1, 2, 4, 9]
def baseStart_2551290 : Nat := 118140960795 + 2551290 * 2 ^ 59
def prefixEnd_2551290 : Nat := 4983230072969 + 3 ^ 40 * 2551290 * 2
def baseEnd_2551290 : Nat := 97039856222920614803099

theorem tailTrace_2551290 : CollatzResearch.WordTrace tailWord_2551290 prefixEnd_2551290 97039856222920614803099 := by
  unfold tailWord_2551290
  simp only [CollatzResearch.WordTrace]
  refine ⟨23263297731779882621804831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62035460618079686991479549 23263297731779882621804831)
  ·
    refine ⟨34894946597669823932707247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23263297731779882621804831 34894946597669823932707247)
    ·
      refine ⟨52342419896504735899060871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34894946597669823932707247 52342419896504735899060871)
      ·
        refine ⟨78513629844757103848591307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52342419896504735899060871 78513629844757103848591307)
        ·
          refine ⟨117770444767135655772886961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78513629844757103848591307 117770444767135655772886961)
          ·
            refine ⟨88327833575351741829665221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117770444767135655772886961 88327833575351741829665221)
            ·
              refine ⟨16561468795378451593062229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88327833575351741829665221 16561468795378451593062229)
              ·
                refine ⟨97039856222920614803099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16561468795378451593062229 97039856222920614803099)
                ·
                  rfl

theorem cell22_2551290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 9].length) (baseStart_2551290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551290 prefixEnd_2551290 := by exact prefixLift 2551290
  have htrace : WordTrace (prefixWord ++ tailWord_2551290) baseStart_2551290 baseEnd_2551290 := by
    simpa [prefixWord, tailWord_2551290, baseEnd_2551290] using wordTrace_append hprefix tailTrace_2551290
  have hstable : (prefixWord ++ tailWord_2551290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551290).length < 2 ^ (prefixWord ++ tailWord_2551290).sum := by decide
  have hdescent : baseEnd_2551290 < baseStart_2551290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551305 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 2, 7]
def baseStart_2551305 : Nat := 118140960795 + 2551305 * 2 ^ 59
def prefixEnd_2551305 : Nat := 4983230072969 + 3 ^ 40 * 2551305 * 2
def baseEnd_2551305 : Nat := 873363840812830494102845

theorem tailTrace_2551305 : CollatzResearch.WordTrace tailWord_2551305 prefixEnd_2551305 873363840812830494102845 := by
  unfold tailWord_2551305
  simp only [CollatzResearch.WordTrace]
  refine ⟨93053738022065188049015369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62035825348043458699343579 93053738022065188049015369)
  ·
    refine ⟨69790303516548891036761527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93053738022065188049015369 69790303516548891036761527)
    ·
      refine ⟨104685455274823336555142291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69790303516548891036761527 104685455274823336555142291)
      ·
        refine ⟨157028182912235004832713437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104685455274823336555142291 157028182912235004832713437)
        ·
          refine ⟨58885568592088126812267539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157028182912235004832713437 58885568592088126812267539)
          ·
            refine ⟨88328352888132190218401309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58885568592088126812267539 88328352888132190218401309)
            ·
              refine ⟨33123132333049571331900491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88328352888132190218401309 33123132333049571331900491)
              ·
                refine ⟨49684698499574356997850737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33123132333049571331900491 49684698499574356997850737)
                ·
                  refine ⟨37263523874680767748388053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49684698499574356997850737 37263523874680767748388053)
                  ·
                    refine ⟨873363840812830494102845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37263523874680767748388053 873363840812830494102845)
                    ·
                      rfl

theorem cell22_2551305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_2551305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551305 prefixEnd_2551305 := by exact prefixLift 2551305
  have htrace : WordTrace (prefixWord ++ tailWord_2551305) baseStart_2551305 baseEnd_2551305 := by
    simpa [prefixWord, tailWord_2551305, baseEnd_2551305] using wordTrace_append hprefix tailTrace_2551305
  have hstable : (prefixWord ++ tailWord_2551305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551305).length < 2 ^ (prefixWord ++ tailWord_2551305).sum := by decide
  have hdescent : baseEnd_2551305 < baseStart_2551305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551307 : List Nat := [1, 1, 1, 1, 8, 1, 1, 8]
def baseStart_2551307 : Nat := 118140960795 + 2551307 * 2 ^ 59
def prefixEnd_2551307 : Nat := 4983230072969 + 3 ^ 40 * 2551307 * 2
def baseEnd_2551307 : Nat := 97040502828189239505871

theorem tailTrace_2551307 : CollatzResearch.WordTrace tailWord_2551307 prefixEnd_2551307 97040502828189239505871 := by
  unfold tailWord_2551307
  simp only [CollatzResearch.WordTrace]
  refine ⟨93053810968057942390588175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62035873978705294927058783 93053810968057942390588175)
  ·
    refine ⟨139580716452086913585882263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93053810968057942390588175 139580716452086913585882263)
    ·
      refine ⟨209371074678130370378823395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139580716452086913585882263 209371074678130370378823395)
      ·
        refine ⟨314056612017195555568235093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209371074678130370378823395 314056612017195555568235093)
        ·
          refine ⟨3680350922076510416815255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 314056612017195555568235093 3680350922076510416815255)
          ·
            refine ⟨5520526383114765625222883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3680350922076510416815255 5520526383114765625222883)
            ·
              refine ⟨8280789574672148437834325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5520526383114765625222883 8280789574672148437834325)
              ·
                refine ⟨97040502828189239505871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8280789574672148437834325 97040502828189239505871)
                ·
                  rfl

theorem cell22_2551307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 8].length) (baseStart_2551307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551307 prefixEnd_2551307 := by exact prefixLift 2551307
  have htrace : WordTrace (prefixWord ++ tailWord_2551307) baseStart_2551307 baseEnd_2551307 := by
    simpa [prefixWord, tailWord_2551307, baseEnd_2551307] using wordTrace_append hprefix tailTrace_2551307
  have hstable : (prefixWord ++ tailWord_2551307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551307).length < 2 ^ (prefixWord ++ tailWord_2551307).sum := by decide
  have hdescent : baseEnd_2551307 < baseStart_2551307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551414 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_2551414 : Nat := 118140960795 + 2551414 * 2 ^ 59
def prefixEnd_2551414 : Nat := 4983230072969 + 3 ^ 40 * 2551414 * 2
def baseEnd_2551414 : Nat := 291133717913463514375837

theorem tailTrace_2551414 : CollatzResearch.WordTrace tailWord_2551414 prefixEnd_2551414 291133717913463514375837 := by
  unfold tailWord_2551414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5816107098666893729045831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62038475719113533109822197 5816107098666893729045831)
  ·
    refine ⟨8724160648000340593568747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5816107098666893729045831 8724160648000340593568747)
    ·
      refine ⟨13086240972000510890353121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8724160648000340593568747 13086240972000510890353121)
      ·
        refine ⟨9814680729000383167764841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13086240972000510890353121 9814680729000383167764841)
        ·
          refine ⟨7361010546750287375823631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9814680729000383167764841 7361010546750287375823631)
          ·
            refine ⟨11041515820125431063735447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7361010546750287375823631 11041515820125431063735447)
            ·
              refine ⟨16562273730188146595603171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11041515820125431063735447 16562273730188146595603171)
              ·
                refine ⟨24843410595282219893404757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16562273730188146595603171 24843410595282219893404757)
                ·
                  refine ⟨291133717913463514375837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24843410595282219893404757 291133717913463514375837)
                  ·
                    rfl

theorem cell22_2551414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_2551414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551414 prefixEnd_2551414 := by exact prefixLift 2551414
  have htrace : WordTrace (prefixWord ++ tailWord_2551414) baseStart_2551414 baseEnd_2551414 := by
    simpa [prefixWord, tailWord_2551414, baseEnd_2551414] using wordTrace_append hprefix tailTrace_2551414
  have hstable : (prefixWord ++ tailWord_2551414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551414).length < 2 ^ (prefixWord ++ tailWord_2551414).sum := by decide
  have hdescent : baseEnd_2551414 < baseStart_2551414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551429 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 4, 3]
def baseStart_2551429 : Nat := 118140960795 + 2551429 * 2 ^ 59
def prefixEnd_2551429 : Nat := 4983230072969 + 3 ^ 40 * 2551429 * 2
def baseEnd_2551429 : Nat := 873406288546935504002465

theorem tailTrace_2551429 : CollatzResearch.WordTrace tailWord_2551429 prefixEnd_2551429 873406288546935504002465 := by
  unfold tailWord_2551429
  simp only [CollatzResearch.WordTrace]
  refine ⟨93058260673615957226529341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62038840449077304817686227 93058260673615957226529341)
  ·
    refine ⟨34896847752605983959948503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93058260673615957226529341 34896847752605983959948503)
    ·
      refine ⟨52345271628908975939922755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34896847752605983959948503 52345271628908975939922755)
      ·
        refine ⟨78517907443363463909884133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52345271628908975939922755 78517907443363463909884133)
        ·
          refine ⟨14722107645630649483103275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78517907443363463909884133 14722107645630649483103275)
          ·
            refine ⟨22083161468445974224654913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14722107645630649483103275 22083161468445974224654913)
            ·
              refine ⟨16562371101334480668491185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22083161468445974224654913 16562371101334480668491185)
              ·
                refine ⟨12421778326000860501368389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16562371101334480668491185 12421778326000860501368389)
                ·
                  refine ⟨2329083436125161344006573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12421778326000860501368389 2329083436125161344006573)
                  ·
                    refine ⟨873406288546935504002465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2329083436125161344006573 873406288546935504002465)
                    ·
                      rfl

theorem cell22_2551429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_2551429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551429 prefixEnd_2551429 := by exact prefixLift 2551429
  have htrace : WordTrace (prefixWord ++ tailWord_2551429) baseStart_2551429 baseEnd_2551429 := by
    simpa [prefixWord, tailWord_2551429, baseEnd_2551429] using wordTrace_append hprefix tailTrace_2551429
  have hstable : (prefixWord ++ tailWord_2551429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551429).length < 2 ^ (prefixWord ++ tailWord_2551429).sum := by decide
  have hdescent : baseEnd_2551429 < baseStart_2551429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551431 : List Nat := [1, 1, 4, 2, 1, 4, 2, 3, 4]
def baseStart_2551431 : Nat := 118140960795 + 2551431 * 2 ^ 59
def prefixEnd_2551431 : Nat := 4983230072969 + 3 ^ 40 * 2551431 * 2
def baseEnd_2551431 : Nat := 291135657729269388484153

theorem tailTrace_2551431 : CollatzResearch.WordTrace tailWord_2551431 prefixEnd_2551431 291135657729269388484153 := by
  unfold tailWord_2551431
  simp only [CollatzResearch.WordTrace]
  refine ⟨93058333619608711568102147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62038889079739141045401431 93058333619608711568102147)
  ·
    refine ⟨139587500429413067352153221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93058333619608711568102147 139587500429413067352153221)
    ·
      refine ⟨26172656330514950128528729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139587500429413067352153221 26172656330514950128528729)
      ·
        refine ⟨19629492247886212596396547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26172656330514950128528729 19629492247886212596396547)
        ·
          refine ⟨29444238371829318894594821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19629492247886212596396547 29444238371829318894594821)
          ·
            refine ⟨5520794694717997292736529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29444238371829318894594821 5520794694717997292736529)
            ·
              refine ⟨4140596021038497969552397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5520794694717997292736529 4140596021038497969552397)
              ·
                refine ⟨1552723507889436738582149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4140596021038497969552397 1552723507889436738582149)
                ·
                  refine ⟨291135657729269388484153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1552723507889436738582149 291135657729269388484153)
                  ·
                    rfl

theorem cell22_2551431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 4].length) (baseStart_2551431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551431 prefixEnd_2551431 := by exact prefixLift 2551431
  have htrace : WordTrace (prefixWord ++ tailWord_2551431) baseStart_2551431 baseEnd_2551431 := by
    simpa [prefixWord, tailWord_2551431, baseEnd_2551431] using wordTrace_append hprefix tailTrace_2551431
  have hstable : (prefixWord ++ tailWord_2551431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551431).length < 2 ^ (prefixWord ++ tailWord_2551431).sum := by decide
  have hdescent : baseEnd_2551431 < baseStart_2551431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551472 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 2, 6]
def baseStart_2551472 : Nat := 118140960795 + 2551472 * 2 ^ 59
def prefixEnd_2551472 : Nat := 4983230072969 + 3 ^ 40 * 2551472 * 2
def baseEnd_2551472 : Nat := 873421008325697725177333

theorem tailTrace_2551472 : CollatzResearch.WordTrace tailWord_2551472 prefixEnd_2551472 873421008325697725177333 := by
  unfold tailWord_2551472
  simp only [CollatzResearch.WordTrace]
  refine ⟨46529914506230087785172335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62039886008306783713563113 46529914506230087785172335)
  ·
    refine ⟨69794871759345131677758503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46529914506230087785172335 69794871759345131677758503)
    ·
      refine ⟨104692307639017697516637755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69794871759345131677758503 104692307639017697516637755)
      ·
        refine ⟨157038461458526546274956633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104692307639017697516637755 157038461458526546274956633)
        ·
          refine ⟨117778846093894909706217475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157038461458526546274956633 117778846093894909706217475)
          ·
            refine ⟨176668269140842364559326213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117778846093894909706217475 176668269140842364559326213)
            ·
              refine ⟨33125300463907943354873665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176668269140842364559326213 33125300463907943354873665)
              ·
                refine ⟨24843975347930957516155249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33125300463907943354873665 24843975347930957516155249)
                ·
                  refine ⟨18632981510948218137116437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24843975347930957516155249 18632981510948218137116437)
                  ·
                    refine ⟨873421008325697725177333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18632981510948218137116437 873421008325697725177333)
                    ·
                      rfl

theorem cell22_2551472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_2551472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551472 prefixEnd_2551472 := by exact prefixLift 2551472
  have htrace : WordTrace (prefixWord ++ tailWord_2551472) baseStart_2551472 baseEnd_2551472 := by
    simpa [prefixWord, tailWord_2551472, baseEnd_2551472] using wordTrace_append hprefix tailTrace_2551472
  have hstable : (prefixWord ++ tailWord_2551472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551472).length < 2 ^ (prefixWord ++ tailWord_2551472).sum := by decide
  have hdescent : baseEnd_2551472 < baseStart_2551472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551487 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 9]
def baseStart_2551487 : Nat := 118140960795 + 2551487 * 2 ^ 59
def prefixEnd_2551487 : Nat := 4983230072969 + 3 ^ 40 * 2551487 * 2
def baseEnd_2551487 : Nat := 291142047710747562017429

theorem tailTrace_2551487 : CollatzResearch.WordTrace tailWord_2551487 prefixEnd_2551487 291142047710747562017429 := by
  unfold tailWord_2551487
  simp only [CollatzResearch.WordTrace]
  refine ⟨93060376107405833132140715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62040250738270555421427143 93060376107405833132140715)
  ·
    refine ⟨139590564161108749698211073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93060376107405833132140715 139590564161108749698211073)
    ·
      refine ⟨104692923120831562273658305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139590564161108749698211073 104692923120831562273658305)
      ·
        refine ⟨78519692340623671705243729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104692923120831562273658305 78519692340623671705243729)
        ·
          refine ⟨58889769255467753778932797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78519692340623671705243729 58889769255467753778932797)
          ·
            refine ⟨22083663470800407667099799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58889769255467753778932797 22083663470800407667099799)
            ·
              refine ⟨33125495206200611500649699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22083663470800407667099799 33125495206200611500649699)
              ·
                refine ⟨49688242809300917250974549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33125495206200611500649699 49688242809300917250974549)
                ·
                  refine ⟨291142047710747562017429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49688242809300917250974549 291142047710747562017429)
                  ·
                    rfl

theorem cell22_2551487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 9].length) (baseStart_2551487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551487 prefixEnd_2551487 := by exact prefixLift 2551487
  have htrace : WordTrace (prefixWord ++ tailWord_2551487) baseStart_2551487 baseEnd_2551487 := by
    simpa [prefixWord, tailWord_2551487, baseEnd_2551487] using wordTrace_append hprefix tailTrace_2551487
  have hstable : (prefixWord ++ tailWord_2551487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551487).length < 2 ^ (prefixWord ++ tailWord_2551487).sum := by decide
  have hdescent : baseEnd_2551487 < baseStart_2551487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
