import V185TrunkScan20Chunk167

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_1022797 : List Nat := [1, 6, 1, 2, 2, 1, 2, 3, 2]
def baseStart_1022797 : Nat := 118140960795 + 1022797 * 2 ^ 59
def prefixEnd_1022797 : Nat := 4983230072969 + 3 ^ 40 * 1022797 * 2
def baseEnd_1022797 : Nat := 466832420423768920652221

theorem tailTrace_1022797 : CollatzResearch.WordTrace tailWord_1022797 prefixEnd_1022797 466832420423768920652221 := by
  unfold tailWord_1022797
  simp only [CollatzResearch.WordTrace]
  refine ⟨37304471275588623665738645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24869647517059082443825763 37304471275588623665738645)
  ·
    refine ⟨1748647091043216734331499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37304471275588623665738645 1748647091043216734331499)
    ·
      refine ⟨2622970636564825101497249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1748647091043216734331499 2622970636564825101497249)
      ·
        refine ⟨1967227977423618826122937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2622970636564825101497249 1967227977423618826122937)
        ·
          refine ⟨1475420983067714119592203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1967227977423618826122937 1475420983067714119592203)
          ·
            refine ⟨2213131474601571179388305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475420983067714119592203 2213131474601571179388305)
            ·
              refine ⟨1659848605951178384541229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213131474601571179388305 1659848605951178384541229)
              ·
                refine ⟨622443227231691894202961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1659848605951178384541229 622443227231691894202961)
                ·
                  refine ⟨466832420423768920652221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622443227231691894202961 466832420423768920652221)
                  ·
                    rfl

theorem cell20_1022797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_1022797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022797 prefixEnd_1022797 := by exact prefixLift 1022797
  have htrace : WordTrace (prefixWord ++ tailWord_1022797) baseStart_1022797 baseEnd_1022797 := by
    simpa [prefixWord, tailWord_1022797, baseEnd_1022797] using wordTrace_append hprefix tailTrace_1022797
  have hstable : (prefixWord ++ tailWord_1022797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022797).length < 2 ^ (prefixWord ++ tailWord_1022797).sum := by decide
  have hdescent : baseEnd_1022797 < baseStart_1022797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022805 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 6]
def baseStart_1022805 : Nat := 118140960795 + 1022805 * 2 ^ 59
def prefixEnd_1022805 : Nat := 4983230072969 + 3 ^ 40 * 1022805 * 2
def baseEnd_1022805 : Nat := 466836071841756448385521

theorem tailTrace_1022805 : CollatzResearch.WordTrace tailWord_1022805 prefixEnd_1022805 466836071841756448385521 := by
  unfold tailWord_1022805
  simp only [CollatzResearch.WordTrace]
  refine ⟨37304763059559641032029869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24869842039706427354686579 37304763059559641032029869)
  ·
    refine ⟨13989286147334865387011201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37304763059559641032029869 13989286147334865387011201)
    ·
      refine ⟨10491964610501149040258401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13989286147334865387011201 10491964610501149040258401)
      ·
        refine ⟨7868973457875861780193801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10491964610501149040258401 7868973457875861780193801)
        ·
          refine ⟨5901730093406896335145351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7868973457875861780193801 5901730093406896335145351)
          ·
            refine ⟨8852595140110344502718027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5901730093406896335145351 8852595140110344502718027)
            ·
              refine ⟨13278892710165516754077041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8852595140110344502718027 13278892710165516754077041)
              ·
                refine ⟨9959169532624137565557781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13278892710165516754077041 9959169532624137565557781)
                ·
                  refine ⟨466836071841756448385521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9959169532624137565557781 466836071841756448385521)
                  ·
                    rfl

theorem cell20_1022805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_1022805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022805 prefixEnd_1022805 := by exact prefixLift 1022805
  have htrace : WordTrace (prefixWord ++ tailWord_1022805) baseStart_1022805 baseEnd_1022805 := by
    simpa [prefixWord, tailWord_1022805, baseEnd_1022805] using wordTrace_append hprefix tailTrace_1022805
  have hstable : (prefixWord ++ tailWord_1022805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022805).length < 2 ^ (prefixWord ++ tailWord_1022805).sum := by decide
  have hdescent : baseEnd_1022805 < baseStart_1022805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022843 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 4]
def baseStart_1022843 : Nat := 118140960795 + 1022843 * 2 ^ 59
def prefixEnd_1022843 : Nat := 4983230072969 + 3 ^ 40 * 1022843 * 2
def baseEnd_1022843 : Nat := 466853416077197205118699

theorem tailTrace_1022843 : CollatzResearch.WordTrace tailWord_1022843 prefixEnd_1022843 466853416077197205118699 := by
  unfold tailWord_1022843
  simp only [CollatzResearch.WordTrace]
  refine ⟨37306149033421973521913183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24870766022281315681275455 37306149033421973521913183)
  ·
    refine ⟨55959223550132960282869775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37306149033421973521913183 55959223550132960282869775)
    ·
      refine ⟨83938835325199440424304663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55959223550132960282869775 83938835325199440424304663)
      ·
        refine ⟨125908252987799160636456995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83938835325199440424304663 125908252987799160636456995)
        ·
          refine ⟨188862379481698740954685493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125908252987799160636456995 188862379481698740954685493)
          ·
            refine ⟨17705848076409256964501765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188862379481698740954685493 17705848076409256964501765)
            ·
              refine ⟨3319846514326735680844081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17705848076409256964501765 3319846514326735680844081)
              ·
                refine ⟨2489884885745051760633061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3319846514326735680844081 2489884885745051760633061)
                ·
                  refine ⟨466853416077197205118699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2489884885745051760633061 466853416077197205118699)
                  ·
                    rfl

theorem cell20_1022843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_1022843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022843 prefixEnd_1022843 := by exact prefixLift 1022843
  have htrace : WordTrace (prefixWord ++ tailWord_1022843) baseStart_1022843 baseEnd_1022843 := by
    simpa [prefixWord, tailWord_1022843, baseEnd_1022843] using wordTrace_append hprefix tailTrace_1022843
  have hstable : (prefixWord ++ tailWord_1022843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022843).length < 2 ^ (prefixWord ++ tailWord_1022843).sum := by decide
  have hdescent : baseEnd_1022843 < baseStart_1022843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022856 : List Nat := [2, 1, 3, 3, 2, 3, 1, 3, 2]
def baseStart_1022856 : Nat := 118140960795 + 1022856 * 2 ^ 59
def prefixEnd_1022856 : Nat := 4983230072969 + 3 ^ 40 * 1022856 * 2
def baseEnd_1022856 : Nat := 466859349631426937685313

theorem tailTrace_1022856 : CollatzResearch.WordTrace tailWord_1022856 prefixEnd_1022856 466859349631426937685313 := by
  unfold tailWord_1022856
  simp only [CollatzResearch.WordTrace]
  refine ⟨18653311591187438371068211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24871082121583251161424281 18653311591187438371068211)
  ·
    refine ⟨27979967386781157556602317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18653311591187438371068211 27979967386781157556602317)
    ·
      refine ⟨10492487770042934083725869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27979967386781157556602317 10492487770042934083725869)
      ·
        refine ⟨3934682913766100281397201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10492487770042934083725869 3934682913766100281397201)
        ·
          refine ⟨2951012185324575211047901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3934682913766100281397201 2951012185324575211047901)
          ·
            refine ⟨1106629569496715704142963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2951012185324575211047901 1106629569496715704142963)
            ·
              refine ⟨1659944354245073556214445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1106629569496715704142963 1659944354245073556214445)
              ·
                refine ⟨622479132841902583580417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1659944354245073556214445 622479132841902583580417)
                ·
                  refine ⟨466859349631426937685313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622479132841902583580417 466859349631426937685313)
                  ·
                    rfl

theorem cell20_1022856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 2].length) (baseStart_1022856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022856 prefixEnd_1022856 := by exact prefixLift 1022856
  have htrace : WordTrace (prefixWord ++ tailWord_1022856) baseStart_1022856 baseEnd_1022856 := by
    simpa [prefixWord, tailWord_1022856, baseEnd_1022856] using wordTrace_append hprefix tailTrace_1022856
  have hstable : (prefixWord ++ tailWord_1022856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022856).length < 2 ^ (prefixWord ++ tailWord_1022856).sum := by decide
  have hdescent : baseEnd_1022856 < baseStart_1022856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022887 : List Nat := [1, 1, 6, 1, 3, 2, 2, 1, 3]
def baseStart_1022887 : Nat := 118140960795 + 1022887 * 2 ^ 59
def prefixEnd_1022887 : Nat := 4983230072969 + 3 ^ 40 * 1022887 * 2
def baseEnd_1022887 : Nat := 466873498876128607651853

theorem tailTrace_1022887 : CollatzResearch.WordTrace tailWord_1022887 prefixEnd_1022887 466873498876128607651853 := by
  unfold tailWord_1022887
  simp only [CollatzResearch.WordTrace]
  refine ⟨37307753845262569036514915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24871835896841712691009943 37307753845262569036514915)
  ·
    refine ⟨55961630767893853554772373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37307753845262569036514915 55961630767893853554772373)
    ·
      refine ⟨2623201442245024385379955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55961630767893853554772373 2623201442245024385379955)
      ·
        refine ⟨3934802163367536578069933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2623201442245024385379955 3934802163367536578069933)
        ·
          refine ⟨1475550811262826216776225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3934802163367536578069933 1475550811262826216776225)
          ·
            refine ⟨1106663108447119662582169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1475550811262826216776225 1106663108447119662582169)
            ·
              refine ⟨829997331335339746936627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106663108447119662582169 829997331335339746936627)
              ·
                refine ⟨1244995997003009620404941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829997331335339746936627 1244995997003009620404941)
                ·
                  refine ⟨466873498876128607651853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1244995997003009620404941 466873498876128607651853)
                  ·
                    rfl

theorem cell20_1022887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 3].length) (baseStart_1022887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022887 prefixEnd_1022887 := by exact prefixLift 1022887
  have htrace : WordTrace (prefixWord ++ tailWord_1022887) baseStart_1022887 baseEnd_1022887 := by
    simpa [prefixWord, tailWord_1022887, baseEnd_1022887] using wordTrace_append hprefix tailTrace_1022887
  have hstable : (prefixWord ++ tailWord_1022887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022887).length < 2 ^ (prefixWord ++ tailWord_1022887).sum := by decide
  have hdescent : baseEnd_1022887 < baseStart_1022887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022895 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 7]
def baseStart_1022895 : Nat := 118140960795 + 1022895 * 2 ^ 59
def prefixEnd_1022895 : Nat := 4983230072969 + 3 ^ 40 * 1022895 * 2
def baseEnd_1022895 : Nat := 466877150294116135385153

theorem tailTrace_1022895 : CollatzResearch.WordTrace tailWord_1022895 prefixEnd_1022895 466877150294116135385153 := by
  unfold tailWord_1022895
  simp only [CollatzResearch.WordTrace]
  refine ⟨37308045629233586402806139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24872030419489057601870759 37308045629233586402806139)
  ·
    refine ⟨55962068443850379604209209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37308045629233586402806139 55962068443850379604209209)
    ·
      refine ⟨41971551332887784703156907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55962068443850379604209209 41971551332887784703156907)
      ·
        refine ⟨62957326999331677054735361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41971551332887784703156907 62957326999331677054735361)
        ·
          refine ⟨47217995249498757791051521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62957326999331677054735361 47217995249498757791051521)
          ·
            refine ⟨35413496437124068343288641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47217995249498757791051521 35413496437124068343288641)
            ·
              refine ⟨26560122327843051257466481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35413496437124068343288641 26560122327843051257466481)
              ·
                refine ⟨19920091745882288443099861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26560122327843051257466481 19920091745882288443099861)
                ·
                  refine ⟨466877150294116135385153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19920091745882288443099861 466877150294116135385153)
                  ·
                    rfl

theorem cell20_1022895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_1022895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022895 prefixEnd_1022895 := by exact prefixLift 1022895
  have htrace : WordTrace (prefixWord ++ tailWord_1022895) baseStart_1022895 baseEnd_1022895 := by
    simpa [prefixWord, tailWord_1022895, baseEnd_1022895] using wordTrace_append hprefix tailTrace_1022895
  have hstable : (prefixWord ++ tailWord_1022895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022895).length < 2 ^ (prefixWord ++ tailWord_1022895).sum := by decide
  have hdescent : baseEnd_1022895 < baseStart_1022895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022918 : List Nat := [6, 1, 3, 1, 1, 8]
def baseStart_1022918 : Nat := 118140960795 + 1022918 * 2 ^ 59
def prefixEnd_1022918 : Nat := 4983230072969 + 3 ^ 40 * 1022918 * 2
def baseEnd_1022918 : Nat := 17292135115586306578459

theorem tailTrace_1022918 : CollatzResearch.WordTrace tailWord_1022918 prefixEnd_1022918 17292135115586306578459 := by
  unfold tailWord_1022918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1165902640879695666590419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24872589672100174220595605 1165902640879695666590419)
  ·
    refine ⟨1748853961319543499885629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1165902640879695666590419 1748853961319543499885629)
    ·
      refine ⟨655820235494828812457111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1748853961319543499885629 655820235494828812457111)
      ·
        refine ⟨983730353242243218685667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655820235494828812457111 983730353242243218685667)
        ·
          refine ⟨1475595529863364828028501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983730353242243218685667 1475595529863364828028501)
          ·
            refine ⟨17292135115586306578459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1475595529863364828028501 17292135115586306578459)
            ·
              rfl

theorem cell20_1022918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 8].length) (baseStart_1022918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022918 prefixEnd_1022918 := by exact prefixLift 1022918
  have htrace : WordTrace (prefixWord ++ tailWord_1022918) baseStart_1022918 baseEnd_1022918 := by
    simpa [prefixWord, tailWord_1022918, baseEnd_1022918] using wordTrace_append hprefix tailTrace_1022918
  have hstable : (prefixWord ++ tailWord_1022918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022918).length < 2 ^ (prefixWord ++ tailWord_1022918).sum := by decide
  have hdescent : baseEnd_1022918 < baseStart_1022918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022926 : List Nat := [4, 1, 1, 1, 2, 11]
def baseStart_1022926 : Nat := 118140960795 + 1022926 * 2 ^ 59
def prefixEnd_1022926 : Nat := 4983230072969 + 3 ^ 40 * 1022926 * 2
def baseEnd_1022926 : Nat := 17292270353289548346359

theorem tailTrace_1022926 : CollatzResearch.WordTrace tailWord_1022926 prefixEnd_1022926 17292270353289548346359 := by
  unfold tailWord_1022926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4663647036515159837148079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24872784194747519131456421 4663647036515159837148079)
  ·
    refine ⟨6995470554772739755722119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4663647036515159837148079 6995470554772739755722119)
    ·
      refine ⟨10493205832159109633583179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6995470554772739755722119 10493205832159109633583179)
      ·
        refine ⟨15739808748238664450374769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10493205832159109633583179 15739808748238664450374769)
        ·
          refine ⟨11804856561178998337781077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15739808748238664450374769 11804856561178998337781077)
          ·
            refine ⟨17292270353289548346359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11804856561178998337781077 17292270353289548346359)
            ·
              rfl

theorem cell20_1022926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 11].length) (baseStart_1022926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022926 prefixEnd_1022926 := by exact prefixLift 1022926
  have htrace : WordTrace (prefixWord ++ tailWord_1022926) baseStart_1022926 baseEnd_1022926 := by
    simpa [prefixWord, tailWord_1022926, baseEnd_1022926] using wordTrace_append hprefix tailTrace_1022926
  have hstable : (prefixWord ++ tailWord_1022926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022926).length < 2 ^ (prefixWord ++ tailWord_1022926).sum := by decide
  have hdescent : baseEnd_1022926 < baseStart_1022926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022932 : List Nat := [2, 4, 1, 2, 1, 2, 4, 2, 2]
def baseStart_1022932 : Nat := 118140960795 + 1022932 * 2 ^ 59
def prefixEnd_1022932 : Nat := 4983230072969 + 3 ^ 40 * 1022932 * 2
def baseEnd_1022932 : Nat := 466894038102308451151669

theorem tailTrace_1022932 : CollatzResearch.WordTrace tailWord_1022932 prefixEnd_1022932 466894038102308451151669 := by
  unfold tailWord_1022932
  simp only [CollatzResearch.WordTrace]
  refine ⟨18654697565049770860951525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24872930086733027814602033 18654697565049770860951525)
  ·
    refine ⟨3497755793446832036428411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18654697565049770860951525 3497755793446832036428411)
    ·
      refine ⟨5246633690170248054642617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3497755793446832036428411 5246633690170248054642617)
      ·
        refine ⟨3934975267627686040981963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5246633690170248054642617 3934975267627686040981963)
        ·
          refine ⟨5902462901441529061472945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3934975267627686040981963 5902462901441529061472945)
          ·
            refine ⟨4426847176081146796104709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5902462901441529061472945 4426847176081146796104709)
            ·
              refine ⟨830033845515215024269633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4426847176081146796104709 830033845515215024269633)
              ·
                refine ⟨622525384136411268202225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 830033845515215024269633 622525384136411268202225)
                ·
                  refine ⟨466894038102308451151669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622525384136411268202225 466894038102308451151669)
                  ·
                    rfl

theorem cell20_1022932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_1022932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022932 prefixEnd_1022932 := by exact prefixLift 1022932
  have htrace : WordTrace (prefixWord ++ tailWord_1022932) baseStart_1022932 baseEnd_1022932 := by
    simpa [prefixWord, tailWord_1022932, baseEnd_1022932] using wordTrace_append hprefix tailTrace_1022932
  have hstable : (prefixWord ++ tailWord_1022932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022932).length < 2 ^ (prefixWord ++ tailWord_1022932).sum := by decide
  have hdescent : baseEnd_1022932 < baseStart_1022932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022946 : List Nat := [3, 3, 3, 1, 1, 1, 2, 3, 3]
def baseStart_1022946 : Nat := 118140960795 + 1022946 * 2 ^ 59
def prefixEnd_1022946 : Nat := 4983230072969 + 3 ^ 40 * 1022946 * 2
def baseEnd_1022946 : Nat := 466900428083786624684945

theorem tailTrace_1022946 : CollatzResearch.WordTrace tailWord_1022946 prefixEnd_1022946 466900428083786624684945 := by
  unfold tailWord_1022946
  simp only [CollatzResearch.WordTrace]
  refine ⟨9327476438012205528228173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24873270501365881408608461 9327476438012205528228173)
  ·
    refine ⟨3497803664254577073085565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9327476438012205528228173 3497803664254577073085565)
    ·
      refine ⟨1311676374095466402407087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3497803664254577073085565 1311676374095466402407087)
      ·
        refine ⟨1967514561143199603610631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311676374095466402407087 1967514561143199603610631)
        ·
          refine ⟨2951271841714799405415947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967514561143199603610631 2951271841714799405415947)
          ·
            refine ⟨4426907762572199108123921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2951271841714799405415947 4426907762572199108123921)
            ·
              refine ⟨3320180821929149331092941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4426907762572199108123921 3320180821929149331092941)
              ·
                refine ⟨1245067808223430999159853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3320180821929149331092941 1245067808223430999159853)
                ·
                  refine ⟨466900428083786624684945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1245067808223430999159853 466900428083786624684945)
                  ·
                    rfl

theorem cell20_1022946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_1022946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022946 prefixEnd_1022946 := by exact prefixLift 1022946
  have htrace : WordTrace (prefixWord ++ tailWord_1022946) baseStart_1022946 baseEnd_1022946 := by
    simpa [prefixWord, tailWord_1022946, baseEnd_1022946] using wordTrace_append hprefix tailTrace_1022946
  have hstable : (prefixWord ++ tailWord_1022946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022946).length < 2 ^ (prefixWord ++ tailWord_1022946).sum := by decide
  have hdescent : baseEnd_1022946 < baseStart_1022946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022971 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 5]
def baseStart_1022971 : Nat := 118140960795 + 1022971 * 2 ^ 59
def prefixEnd_1022971 : Nat := 4983230072969 + 3 ^ 40 * 1022971 * 2
def baseEnd_1022971 : Nat := 466911838764997648851509

theorem tailTrace_1022971 : CollatzResearch.WordTrace tailWord_1022971 prefixEnd_1022971 466911838764997648851509 := by
  unfold tailWord_1022971
  simp only [CollatzResearch.WordTrace]
  refine ⟨37310817576958251382572767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24873878384638834255048511 37310817576958251382572767)
  ·
    refine ⟨55966226365437377073859151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37310817576958251382572767 55966226365437377073859151)
    ·
      refine ⟨83949339548156065610788727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55966226365437377073859151 83949339548156065610788727)
      ·
        refine ⟨125924009322234098416183091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83949339548156065610788727 125924009322234098416183091)
        ·
          refine ⟨188886013983351147624274637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125924009322234098416183091 188886013983351147624274637)
          ·
            refine ⟨70832255243756680359102989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188886013983351147624274637 70832255243756680359102989)
            ·
              refine ⟨26562095716408755134663621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70832255243756680359102989 26562095716408755134663621)
              ·
                refine ⟨4980392946826641587749429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26562095716408755134663621 4980392946826641587749429)
                ·
                  refine ⟨466911838764997648851509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4980392946826641587749429 466911838764997648851509)
                  ·
                    rfl

theorem cell20_1022971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_1022971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022971 prefixEnd_1022971 := by exact prefixLift 1022971
  have htrace : WordTrace (prefixWord ++ tailWord_1022971) baseStart_1022971 baseEnd_1022971 := by
    simpa [prefixWord, tailWord_1022971, baseEnd_1022971] using wordTrace_append hprefix tailTrace_1022971
  have hstable : (prefixWord ++ tailWord_1022971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022971).length < 2 ^ (prefixWord ++ tailWord_1022971).sum := by decide
  have hdescent : baseEnd_1022971 < baseStart_1022971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022988 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 5]
def baseStart_1022988 : Nat := 118140960795 + 1022988 * 2 ^ 59
def prefixEnd_1022988 : Nat := 4983230072969 + 3 ^ 40 * 1022988 * 2
def baseEnd_1022988 : Nat := 466919598028221145284773

theorem tailTrace_1022988 : CollatzResearch.WordTrace tailWord_1022988 prefixEnd_1022988 466919598028221145284773 := by
  unfold tailWord_1022988
  simp only [CollatzResearch.WordTrace]
  refine ⟨18655718808948331642970809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24874291745264442190627745 18655718808948331642970809)
  ·
    refine ⟨13991789106711248732228107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18655718808948331642970809 13991789106711248732228107)
    ·
      refine ⟨20987683660066873098342161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13991789106711248732228107 20987683660066873098342161)
      ·
        refine ⟨15740762745050154823756621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20987683660066873098342161 15740762745050154823756621)
        ·
          refine ⟨5902786029393808058908733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15740762745050154823756621 5902786029393808058908733)
          ·
            refine ⟨2213544761022678022090775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5902786029393808058908733 2213544761022678022090775)
            ·
              refine ⟨3320317141534017033136163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2213544761022678022090775 3320317141534017033136163)
              ·
                refine ⟨4980475712301025549704245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3320317141534017033136163 4980475712301025549704245)
                ·
                  refine ⟨466919598028221145284773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4980475712301025549704245 466919598028221145284773)
                  ·
                    rfl

theorem cell20_1022988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_1022988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1022988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1022988 prefixEnd_1022988 := by exact prefixLift 1022988
  have htrace : WordTrace (prefixWord ++ tailWord_1022988) baseStart_1022988 baseEnd_1022988 := by
    simpa [prefixWord, tailWord_1022988, baseEnd_1022988] using wordTrace_append hprefix tailTrace_1022988
  have hstable : (prefixWord ++ tailWord_1022988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022988).length < 2 ^ (prefixWord ++ tailWord_1022988).sum := by decide
  have hdescent : baseEnd_1022988 < baseStart_1022988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023002 : List Nat := [3, 1, 1, 3, 1, 2, 2, 7]
def baseStart_1023002 : Nat := 118140960795 + 1023002 * 2 ^ 59
def prefixEnd_1023002 : Nat := 4983230072969 + 3 ^ 40 * 1023002 * 2
def baseEnd_1023002 : Nat := 155641996003233106272683

theorem tailTrace_1023002 : CollatzResearch.WordTrace tailWord_1023002 prefixEnd_1023002 155641996003233106272683 := by
  unfold tailWord_1023002
  simp only [CollatzResearch.WordTrace]
  refine ⟨9327987059961485919237815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24874632159897295784634173 9327987059961485919237815)
  ·
    refine ⟨13991980589942228878856723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9327987059961485919237815 13991980589942228878856723)
    ·
      refine ⟨20987970884913343318285085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13991980589942228878856723 20987970884913343318285085)
      ·
        refine ⟨7870489081842503744356907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20987970884913343318285085 7870489081842503744356907)
        ·
          refine ⟨11805733622763755616535361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7870489081842503744356907 11805733622763755616535361)
          ·
            refine ⟨8854300217072816712401521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11805733622763755616535361 8854300217072816712401521)
            ·
              refine ⟨6640725162804612534301141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8854300217072816712401521 6640725162804612534301141)
              ·
                refine ⟨155641996003233106272683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6640725162804612534301141 155641996003233106272683)
                ·
                  rfl

theorem cell20_1023002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_1023002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023002 prefixEnd_1023002 := by exact prefixLift 1023002
  have htrace : WordTrace (prefixWord ++ tailWord_1023002) baseStart_1023002 baseEnd_1023002 := by
    simpa [prefixWord, tailWord_1023002, baseEnd_1023002] using wordTrace_append hprefix tailTrace_1023002
  have hstable : (prefixWord ++ tailWord_1023002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023002).length < 2 ^ (prefixWord ++ tailWord_1023002).sum := by decide
  have hdescent : baseEnd_1023002 < baseStart_1023002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023012 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 4]
def baseStart_1023012 : Nat := 118140960795 + 1023012 * 2 ^ 59
def prefixEnd_1023012 : Nat := 4983230072969 + 3 ^ 40 * 1023012 * 2
def baseEnd_1023012 : Nat := 466930552282183728484675

theorem tailTrace_1023012 : CollatzResearch.WordTrace tailWord_1023012 prefixEnd_1023012 466930552282183728484675 := by
  unfold tailWord_1023012
  simp only [CollatzResearch.WordTrace]
  refine ⟨18656156484904857692407645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24874875313206476923210193 18656156484904857692407645)
  ·
    refine ⟨6996058681839321634652867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18656156484904857692407645 6996058681839321634652867)
    ·
      refine ⟨10494088022758982451979301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6996058681839321634652867 10494088022758982451979301)
      ·
        refine ⟨1967641504267309209746119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10494088022758982451979301 1967641504267309209746119)
        ·
          refine ⟨2951462256400963814619179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967641504267309209746119 2951462256400963814619179)
          ·
            refine ⟨4427193384601445721928769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2951462256400963814619179 4427193384601445721928769)
            ·
              refine ⟨3320395038451084291446577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4427193384601445721928769 3320395038451084291446577)
              ·
                refine ⟨2490296278838313218584933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3320395038451084291446577 2490296278838313218584933)
                ·
                  refine ⟨466930552282183728484675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2490296278838313218584933 466930552282183728484675)
                  ·
                    rfl

theorem cell20_1023012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_1023012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023012 prefixEnd_1023012 := by exact prefixLift 1023012
  have htrace : WordTrace (prefixWord ++ tailWord_1023012) baseStart_1023012 baseEnd_1023012 := by
    simpa [prefixWord, tailWord_1023012, baseEnd_1023012] using wordTrace_append hprefix tailTrace_1023012
  have hstable : (prefixWord ++ tailWord_1023012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023012).length < 2 ^ (prefixWord ++ tailWord_1023012).sum := by decide
  have hdescent : baseEnd_1023012 < baseStart_1023012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023015 : List Nat := [1, 1, 7, 1, 1, 3, 2, 4]
def baseStart_1023015 : Nat := 118140960795 + 1023015 * 2 ^ 59
def prefixEnd_1023015 : Nat := 4983230072969 + 3 ^ 40 * 1023015 * 2
def baseEnd_1023015 : Nat := 155643973854643017128221

theorem tailTrace_1023015 : CollatzResearch.WordTrace tailWord_1023015 prefixEnd_1023015 155643973854643017128221 := by
  unfold tailWord_1023015
  simp only [CollatzResearch.WordTrace]
  refine ⟨37312422388798846897174499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24874948259199231264782999 37312422388798846897174499)
  ·
    refine ⟨55968633583198270345761749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37312422388798846897174499 55968633583198270345761749)
    ·
      refine ⟨1311764849606209461228791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 55968633583198270345761749 1311764849606209461228791)
      ·
        refine ⟨1967647274409314191843187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311764849606209461228791 1967647274409314191843187)
        ·
          refine ⟨2951470911613971287764781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967647274409314191843187 2951470911613971287764781)
          ·
            refine ⟨1106801591855239232911793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2951470911613971287764781 1106801591855239232911793)
            ·
              refine ⟨830101193891429424683845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106801591855239232911793 830101193891429424683845)
              ·
                refine ⟨155643973854643017128221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 830101193891429424683845 155643973854643017128221)
                ·
                  rfl

theorem cell20_1023015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 4].length) (baseStart_1023015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023015 prefixEnd_1023015 := by exact prefixLift 1023015
  have htrace : WordTrace (prefixWord ++ tailWord_1023015) baseStart_1023015 baseEnd_1023015 := by
    simpa [prefixWord, tailWord_1023015, baseEnd_1023015] using wordTrace_append hprefix tailTrace_1023015
  have hstable : (prefixWord ++ tailWord_1023015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023015).length < 2 ^ (prefixWord ++ tailWord_1023015).sum := by decide
  have hdescent : baseEnd_1023015 < baseStart_1023015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023046 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_1023046 : Nat := 118140960795 + 1023046 * 2 ^ 59
def prefixEnd_1023046 : Nat := 4983230072969 + 3 ^ 40 * 1023046 * 2
def baseEnd_1023046 : Nat := 466946070808630721351203

theorem tailTrace_1023046 : CollatzResearch.WordTrace tailWord_1023046 prefixEnd_1023046 466946070808630721351203 := by
  unfold tailWord_1023046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1166048532865204349736031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24875702034457692794368661 1166048532865204349736031)
  ·
    refine ⟨1749072799297806524604047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1166048532865204349736031 1749072799297806524604047)
    ·
      refine ⟨2623609198946709786906071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1749072799297806524604047 2623609198946709786906071)
      ·
        refine ⟨3935413798420064680359107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2623609198946709786906071 3935413798420064680359107)
        ·
          refine ⟨5903120697630097020538661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3935413798420064680359107 5903120697630097020538661)
          ·
            refine ⟨1106835130805643191350999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5903120697630097020538661 1106835130805643191350999)
            ·
              refine ⟨1660252696208464787026499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1106835130805643191350999 1660252696208464787026499)
              ·
                refine ⟨2490379044312697180539749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1660252696208464787026499 2490379044312697180539749)
                ·
                  refine ⟨466946070808630721351203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2490379044312697180539749 466946070808630721351203)
                  ·
                    rfl

theorem cell20_1023046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_1023046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023046 prefixEnd_1023046 := by exact prefixLift 1023046
  have htrace : WordTrace (prefixWord ++ tailWord_1023046) baseStart_1023046 baseEnd_1023046 := by
    simpa [prefixWord, tailWord_1023046, baseEnd_1023046] using wordTrace_append hprefix tailTrace_1023046
  have hstable : (prefixWord ++ tailWord_1023046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023046).length < 2 ^ (prefixWord ++ tailWord_1023046).sum := by decide
  have hdescent : baseEnd_1023046 < baseStart_1023046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023050 : List Nat := [3, 1, 2, 1, 1, 2, 2, 6, 2]
def baseStart_1023050 : Nat := 118140960795 + 1023050 * 2 ^ 59
def prefixEnd_1023050 : Nat := 4983230072969 + 3 ^ 40 * 1023050 * 2
def baseEnd_1023050 : Nat := 466947896517624485217853

theorem tailTrace_1023050 : CollatzResearch.WordTrace tailWord_1023050 prefixEnd_1023050 466947896517624485217853 := by
  unfold tailWord_1023050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9328424735918011968674651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24875799295781365249799069 9328424735918011968674651)
  ·
    refine ⟨13992637103877017953011977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9328424735918011968674651 13992637103877017953011977)
    ·
      refine ⟨10494477827907763464758983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13992637103877017953011977 10494477827907763464758983)
      ·
        refine ⟨15741716741861645197138475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10494477827907763464758983 15741716741861645197138475)
        ·
          refine ⟨23612575112792467795707713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15741716741861645197138475 23612575112792467795707713)
          ·
            refine ⟨17709431334594350846780785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23612575112792467795707713 17709431334594350846780785)
            ·
              refine ⟨13282073500945763135085589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17709431334594350846780785 13282073500945763135085589)
              ·
                refine ⟨622597195356832646957137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13282073500945763135085589 622597195356832646957137)
                ·
                  refine ⟨466947896517624485217853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622597195356832646957137 466947896517624485217853)
                  ·
                    rfl

theorem cell20_1023050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_1023050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023050 prefixEnd_1023050 := by exact prefixLift 1023050
  have htrace : WordTrace (prefixWord ++ tailWord_1023050) baseStart_1023050 baseEnd_1023050 := by
    simpa [prefixWord, tailWord_1023050, baseEnd_1023050] using wordTrace_append hprefix tailTrace_1023050
  have hstable : (prefixWord ++ tailWord_1023050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023050).length < 2 ^ (prefixWord ++ tailWord_1023050).sum := by decide
  have hdescent : baseEnd_1023050 < baseStart_1023050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023064 : List Nat := [2, 1, 2, 2, 1, 3, 3, 3, 3]
def baseStart_1023064 : Nat := 118140960795 + 1023064 * 2 ^ 59
def prefixEnd_1023064 : Nat := 4983230072969 + 3 ^ 40 * 1023064 * 2
def baseEnd_1023064 : Nat := 466954286499102658751129

theorem tailTrace_1023064 : CollatzResearch.WordTrace tailWord_1023064 prefixEnd_1023064 466954286499102658751129 := by
  unfold tailWord_1023064
  simp only [CollatzResearch.WordTrace]
  refine ⟨18657104782810664132854123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24876139710414218843805497 18657104782810664132854123)
  ·
    refine ⟨27985657174215996199281185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18657104782810664132854123 27985657174215996199281185)
    ·
      refine ⟨20989242880661997149460889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27985657174215996199281185 20989242880661997149460889)
      ·
        refine ⟨15741932160496497862095667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20989242880661997149460889 15741932160496497862095667)
        ·
          refine ⟨23612898240744746793143501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15741932160496497862095667 23612898240744746793143501)
          ·
            refine ⟨8854836840279280047428813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23612898240744746793143501 8854836840279280047428813)
            ·
              refine ⟨3320563815104730017785805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8854836840279280047428813 3320563815104730017785805)
              ·
                refine ⟨1245211430664273756669677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3320563815104730017785805 1245211430664273756669677)
                ·
                  refine ⟨466954286499102658751129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1245211430664273756669677 466954286499102658751129)
                  ·
                    rfl

theorem cell20_1023064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_1023064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023064 prefixEnd_1023064 := by exact prefixLift 1023064
  have htrace : WordTrace (prefixWord ++ tailWord_1023064) baseStart_1023064 baseEnd_1023064 := by
    simpa [prefixWord, tailWord_1023064, baseEnd_1023064] using wordTrace_append hprefix tailTrace_1023064
  have hstable : (prefixWord ++ tailWord_1023064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023064).length < 2 ^ (prefixWord ++ tailWord_1023064).sum := by decide
  have hdescent : baseEnd_1023064 < baseStart_1023064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023088 : List Nat := [2, 1, 1, 1, 5, 1, 2, 5, 2]
def baseStart_1023088 : Nat := 118140960795 + 1023088 * 2 ^ 59
def prefixEnd_1023088 : Nat := 4983230072969 + 3 ^ 40 * 1023088 * 2
def baseEnd_1023088 : Nat := 466965240753065241951031

theorem tailTrace_1023088 : CollatzResearch.WordTrace tailWord_1023088 prefixEnd_1023088 466965240753065241951031 := by
  unfold tailWord_1023088
  simp only [CollatzResearch.WordTrace]
  refine ⟨18657542458767190182290959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24876723278356253576387945 18657542458767190182290959)
  ·
    refine ⟨27986313688150785273436439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18657542458767190182290959 27986313688150785273436439)
    ·
      refine ⟨41979470532226177910154659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27986313688150785273436439 41979470532226177910154659)
      ·
        refine ⟨62969205798339266865231989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41979470532226177910154659 62969205798339266865231989)
        ·
          refine ⟨5903363043594306268615499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62969205798339266865231989 5903363043594306268615499)
          ·
            refine ⟨8855044565391459402923249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5903363043594306268615499 8855044565391459402923249)
            ·
              refine ⟨6641283424043594552192437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8855044565391459402923249 6641283424043594552192437)
              ·
                refine ⟨622620321004086989268041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6641283424043594552192437 622620321004086989268041)
                ·
                  refine ⟨466965240753065241951031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622620321004086989268041 466965240753065241951031)
                  ·
                    rfl

theorem cell20_1023088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 2].length) (baseStart_1023088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023088 prefixEnd_1023088 := by exact prefixLift 1023088
  have htrace : WordTrace (prefixWord ++ tailWord_1023088) baseStart_1023088 baseEnd_1023088 := by
    simpa [prefixWord, tailWord_1023088, baseEnd_1023088] using wordTrace_append hprefix tailTrace_1023088
  have hstable : (prefixWord ++ tailWord_1023088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023088).length < 2 ^ (prefixWord ++ tailWord_1023088).sum := by decide
  have hdescent : baseEnd_1023088 < baseStart_1023088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023105 : List Nat := [1, 2, 4, 2, 2, 2, 1, 4, 2]
def baseStart_1023105 : Nat := 118140960795 + 1023105 * 2 ^ 59
def prefixEnd_1023105 : Nat := 4983230072969 + 3 ^ 40 * 1023105 * 2
def baseEnd_1023105 : Nat := 466973000016288738384295

theorem tailTrace_1023105 : CollatzResearch.WordTrace tailWord_1023105 prefixEnd_1023105 466973000016288738384295 := by
  unfold tailWord_1023105
  simp only [CollatzResearch.WordTrace]
  refine ⟨37315704958472792267950769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24877136638981861511967179 37315704958472792267950769)
  ·
    refine ⟨27986778718854594200963077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37315704958472792267950769 27986778718854594200963077)
    ·
      refine ⟨5247521009785236412680577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27986778718854594200963077 5247521009785236412680577)
      ·
        refine ⟨3935640757338927309510433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5247521009785236412680577 3935640757338927309510433)
        ·
          refine ⟨2951730568004195482132825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3935640757338927309510433 2951730568004195482132825)
          ·
            refine ⟨2213797926003146611599619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2951730568004195482132825 2213797926003146611599619)
            ·
              refine ⟨3320696889004719917399429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2213797926003146611599619 3320696889004719917399429)
              ·
                refine ⟨622630666688384984512393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3320696889004719917399429 622630666688384984512393)
                ·
                  refine ⟨466973000016288738384295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622630666688384984512393 466973000016288738384295)
                  ·
                    rfl

theorem cell20_1023105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 2].length) (baseStart_1023105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023105 prefixEnd_1023105 := by exact prefixLift 1023105
  have htrace : WordTrace (prefixWord ++ tailWord_1023105) baseStart_1023105 baseEnd_1023105 := by
    simpa [prefixWord, tailWord_1023105, baseEnd_1023105] using wordTrace_append hprefix tailTrace_1023105
  have hstable : (prefixWord ++ tailWord_1023105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023105).length < 2 ^ (prefixWord ++ tailWord_1023105).sum := by decide
  have hdescent : baseEnd_1023105 < baseStart_1023105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023112 : List Nat := [2, 1, 3, 4, 2, 2, 1, 5]
def baseStart_1023112 : Nat := 118140960795 + 1023112 * 2 ^ 59
def prefixEnd_1023112 : Nat := 4983230072969 + 3 ^ 40 * 1023112 * 2
def baseEnd_1023112 : Nat := 155658731669009275050311

theorem tailTrace_1023112 : CollatzResearch.WordTrace tailWord_1023112 prefixEnd_1023112 155658731669009275050311 := by
  unfold tailWord_1023112
  simp only [CollatzResearch.WordTrace]
  refine ⟨18657980134723716231727795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24877306846298288308970393 18657980134723716231727795)
  ·
    refine ⟨27986970202085574347591693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18657980134723716231727795 27986970202085574347591693)
    ·
      refine ⟨10495113825782090380346885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27986970202085574347591693 10495113825782090380346885)
      ·
        refine ⟨1967833842334141946315041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10495113825782090380346885 1967833842334141946315041)
        ·
          refine ⟨1475875381750606459736281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1967833842334141946315041 1475875381750606459736281)
          ·
            refine ⟨1106906536312954844802211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1475875381750606459736281 1106906536312954844802211)
            ·
              refine ⟨1660359804469432267203317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1106906536312954844802211 1660359804469432267203317)
              ·
                refine ⟨155658731669009275050311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1660359804469432267203317 155658731669009275050311)
                ·
                  rfl

theorem cell20_1023112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_1023112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023112 prefixEnd_1023112 := by exact prefixLift 1023112
  have htrace : WordTrace (prefixWord ++ tailWord_1023112) baseStart_1023112 baseEnd_1023112 := by
    simpa [prefixWord, tailWord_1023112, baseEnd_1023112] using wordTrace_append hprefix tailTrace_1023112
  have hstable : (prefixWord ++ tailWord_1023112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023112).length < 2 ^ (prefixWord ++ tailWord_1023112).sum := by decide
  have hdescent : baseEnd_1023112 < baseStart_1023112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023133 : List Nat := [1, 4, 2, 1, 1, 2, 5, 4]
def baseStart_1023133 : Nat := 118140960795 + 1023133 * 2 ^ 59
def prefixEnd_1023133 : Nat := 4983230072969 + 3 ^ 40 * 1023133 * 2
def baseEnd_1023133 : Nat := 155661926659748361816949

theorem tailTrace_1023133 : CollatzResearch.WordTrace tailWord_1023133 prefixEnd_1023133 155661926659748361816949 := by
  unfold tailWord_1023133
  simp only [CollatzResearch.WordTrace]
  refine ⟨37316726202371353049970053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24877817468247568699980035 37316726202371353049970053)
  ·
    refine ⟨6996886162944628696869385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37316726202371353049970053 6996886162944628696869385)
    ·
      refine ⟨5247664622208471522652039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6996886162944628696869385 5247664622208471522652039)
      ·
        refine ⟨7871496933312707283978059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5247664622208471522652039 7871496933312707283978059)
        ·
          refine ⟨11807245399969060925967089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7871496933312707283978059 11807245399969060925967089)
          ·
            refine ⟨8855434049976795694475317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11807245399969060925967089 8855434049976795694475317)
            ·
              refine ⟨830196942185324596357061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8855434049976795694475317 830196942185324596357061)
              ·
                refine ⟨155661926659748361816949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 830196942185324596357061 155661926659748361816949)
                ·
                  rfl

theorem cell20_1023133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 4].length) (baseStart_1023133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023133 prefixEnd_1023133 := by exact prefixLift 1023133
  have htrace : WordTrace (prefixWord ++ tailWord_1023133) baseStart_1023133 baseEnd_1023133 := by
    simpa [prefixWord, tailWord_1023133, baseEnd_1023133] using wordTrace_append hprefix tailTrace_1023133
  have hstable : (prefixWord ++ tailWord_1023133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023133).length < 2 ^ (prefixWord ++ tailWord_1023133).sum := by decide
  have hdescent : baseEnd_1023133 < baseStart_1023133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023143 : List Nat := [1, 1, 6, 2, 1, 1, 1, 5, 2]
def baseStart_1023143 : Nat := 118140960795 + 1023143 * 2 ^ 59
def prefixEnd_1023143 : Nat := 4983230072969 + 3 ^ 40 * 1023143 * 2
def baseEnd_1023143 : Nat := 466990344251729495117473

theorem tailTrace_1023143 : CollatzResearch.WordTrace tailWord_1023143 prefixEnd_1023143 466990344251729495117473 := by
  unfold tailWord_1023143
  simp only [CollatzResearch.WordTrace]
  refine ⟨37317090932335124757834083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24878060621556749838556055 37317090932335124757834083)
  ·
    refine ⟨55975636398502687136751125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37317090932335124757834083 55975636398502687136751125)
    ·
      refine ⟨2623857956179813459535209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55975636398502687136751125 2623857956179813459535209)
      ·
        refine ⟨1967893467134860094651407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2623857956179813459535209 1967893467134860094651407)
        ·
          refine ⟨2951840200702290141977111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967893467134860094651407 2951840200702290141977111)
          ·
            refine ⟨4427760301053435212965667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2951840200702290141977111 4427760301053435212965667)
            ·
              refine ⟨6641640451580152819448501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4427760301053435212965667 6641640451580152819448501)
              ·
                refine ⟨622653792335639326823297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6641640451580152819448501 622653792335639326823297)
                ·
                  refine ⟨466990344251729495117473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622653792335639326823297 466990344251729495117473)
                  ·
                    rfl

theorem cell20_1023143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 2].length) (baseStart_1023143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023143 prefixEnd_1023143 := by exact prefixLift 1023143
  have htrace : WordTrace (prefixWord ++ tailWord_1023143) baseStart_1023143 baseEnd_1023143 := by
    simpa [prefixWord, tailWord_1023143, baseEnd_1023143] using wordTrace_append hprefix tailTrace_1023143
  have hstable : (prefixWord ++ tailWord_1023143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023143).length < 2 ^ (prefixWord ++ tailWord_1023143).sum := by decide
  have hdescent : baseEnd_1023143 < baseStart_1023143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023154 : List Nat := [3, 2, 1, 1, 1, 5, 7]
def baseStart_1023154 : Nat := 118140960795 + 1023154 * 2 ^ 59
def prefixEnd_1023154 : Nat := 4983230072969 + 3 ^ 40 * 1023154 * 2
def baseEnd_1023154 : Nat := 51888373883495816194529

theorem tailTrace_1023154 : CollatzResearch.WordTrace tailWord_1023154 prefixEnd_1023154 51888373883495816194529 := by
  unfold tailWord_1023154
  simp only [CollatzResearch.WordTrace]
  refine ⟨9329373033823818409121129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24878328090196849090989677 9329373033823818409121129)
  ·
    refine ⟨6997029775367863806840847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9329373033823818409121129 6997029775367863806840847)
    ·
      refine ⟨10495544663051795710261271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6997029775367863806840847 10495544663051795710261271)
      ·
        refine ⟨15743316994577693565391907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10495544663051795710261271 15743316994577693565391907)
        ·
          refine ⟨23614975491866540348087861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15743316994577693565391907 23614975491866540348087861)
          ·
            refine ⟨2213903952362488157633237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23614975491866540348087861 2213903952362488157633237)
            ·
              refine ⟨51888373883495816194529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2213903952362488157633237 51888373883495816194529)
              ·
                rfl

theorem cell20_1023154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 7].length) (baseStart_1023154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023154 prefixEnd_1023154 := by exact prefixLift 1023154
  have htrace : WordTrace (prefixWord ++ tailWord_1023154) baseStart_1023154 baseEnd_1023154 := by
    simpa [prefixWord, tailWord_1023154, baseEnd_1023154] using wordTrace_append hprefix tailTrace_1023154
  have hstable : (prefixWord ++ tailWord_1023154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023154).length < 2 ^ (prefixWord ++ tailWord_1023154).sum := by decide
  have hdescent : baseEnd_1023154 < baseStart_1023154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023164 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 4]
def baseStart_1023164 : Nat := 118140960795 + 1023164 * 2 ^ 59
def prefixEnd_1023164 : Nat := 4983230072969 + 3 ^ 40 * 1023164 * 2
def baseEnd_1023164 : Nat := 466999929223946755417387

theorem tailTrace_1023164 : CollatzResearch.WordTrace tailWord_1023164 prefixEnd_1023164 466999929223946755417387 := by
  unfold tailWord_1023164
  simp only [CollatzResearch.WordTrace]
  refine ⟨18658928432629522672174273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24878571243506030229565697 18658928432629522672174273)
  ·
    refine ⟨13994196324472142004130705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18658928432629522672174273 13994196324472142004130705)
    ·
      refine ⟨10495647243354106503098029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13994196324472142004130705 10495647243354106503098029)
      ·
        refine ⟨3935867716257789938661761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10495647243354106503098029 3935867716257789938661761)
        ·
          refine ⟨2951900787193342453996321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3935867716257789938661761 2951900787193342453996321)
          ·
            refine ⟨2213925590395006840497241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2951900787193342453996321 2213925590395006840497241)
            ·
              refine ⟨1660444192796255130372931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213925590395006840497241 1660444192796255130372931)
              ·
                refine ⟨2490666289194382695559397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1660444192796255130372931 2490666289194382695559397)
                ·
                  refine ⟨466999929223946755417387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2490666289194382695559397 466999929223946755417387)
                  ·
                    rfl

theorem cell20_1023164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_1023164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023164 prefixEnd_1023164 := by exact prefixLift 1023164
  have htrace : WordTrace (prefixWord ++ tailWord_1023164) baseStart_1023164 baseEnd_1023164 := by
    simpa [prefixWord, tailWord_1023164, baseEnd_1023164] using wordTrace_append hprefix tailTrace_1023164
  have hstable : (prefixWord ++ tailWord_1023164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023164).length < 2 ^ (prefixWord ++ tailWord_1023164).sum := by decide
  have hdescent : baseEnd_1023164 < baseStart_1023164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023170 : List Nat := [3, 5, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1023170 : Nat := 118140960795 + 1023170 * 2 ^ 59
def prefixEnd_1023170 : Nat := 4983230072969 + 3 ^ 40 * 1023170 * 2
def baseEnd_1023170 : Nat := 467002667787437401217363

theorem tailTrace_1023170 : CollatzResearch.WordTrace tailWord_1023170 prefixEnd_1023170 467002667787437401217363 := by
  unfold tailWord_1023170
  simp only [CollatzResearch.WordTrace]
  refine ⟨9329518925809327092266741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24878717135491538912711309 9329518925809327092266741)
  ·
    refine ⟨874642399294624414900007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9329518925809327092266741 874642399294624414900007)
    ·
      refine ⟨1311963598941936622350011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 874642399294624414900007 1311963598941936622350011)
      ·
        refine ⟨1967945398412904933525017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311963598941936622350011 1967945398412904933525017)
        ·
          refine ⟨1475959048809678700143763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1967945398412904933525017 1475959048809678700143763)
          ·
            refine ⟨2213938573214518050215645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475959048809678700143763 2213938573214518050215645)
            ·
              refine ⟨830226964955444268830867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2213938573214518050215645 830226964955444268830867)
              ·
                refine ⟨1245340447433166403246301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830226964955444268830867 1245340447433166403246301)
                ·
                  refine ⟨467002667787437401217363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1245340447433166403246301 467002667787437401217363)
                  ·
                    rfl

theorem cell20_1023170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1023170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023170 prefixEnd_1023170 := by exact prefixLift 1023170
  have htrace : WordTrace (prefixWord ++ tailWord_1023170) baseStart_1023170 baseEnd_1023170 := by
    simpa [prefixWord, tailWord_1023170, baseEnd_1023170] using wordTrace_append hprefix tailTrace_1023170
  have hstable : (prefixWord ++ tailWord_1023170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023170).length < 2 ^ (prefixWord ++ tailWord_1023170).sum := by decide
  have hdescent : baseEnd_1023170 < baseStart_1023170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023188 : List Nat := [2, 4, 1, 4, 1, 1, 1, 6]
def baseStart_1023188 : Nat := 118140960795 + 1023188 * 2 ^ 59
def prefixEnd_1023188 : Nat := 4983230072969 + 3 ^ 40 * 1023188 * 2
def baseEnd_1023188 : Nat := 155670294492636446205763

theorem tailTrace_1023188 : CollatzResearch.WordTrace tailWord_1023188 prefixEnd_1023188 155670294492636446205763 := by
  unfold tailWord_1023188
  simp only [CollatzResearch.WordTrace]
  refine ⟨18659366108586048721611109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24879154811448064962148145 18659366108586048721611109)
  ·
    refine ⟨3498631145359884135302083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18659366108586048721611109 3498631145359884135302083)
    ·
      refine ⟨5247946718039826202953125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3498631145359884135302083 5247946718039826202953125)
      ·
        refine ⟨983990009632467413053711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5247946718039826202953125 983990009632467413053711)
        ·
          refine ⟨1475985014448701119580567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983990009632467413053711 1475985014448701119580567)
          ·
            refine ⟨2213977521673051679370851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475985014448701119580567 2213977521673051679370851)
            ·
              refine ⟨3320966282509577519056277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2213977521673051679370851 3320966282509577519056277)
              ·
                refine ⟨155670294492636446205763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3320966282509577519056277 155670294492636446205763)
                ·
                  rfl

theorem cell20_1023188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_1023188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023188 prefixEnd_1023188 := by exact prefixLift 1023188
  have htrace : WordTrace (prefixWord ++ tailWord_1023188) baseStart_1023188 baseEnd_1023188 := by
    simpa [prefixWord, tailWord_1023188, baseEnd_1023188] using wordTrace_append hprefix tailTrace_1023188
  have hstable : (prefixWord ++ tailWord_1023188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023188).length < 2 ^ (prefixWord ++ tailWord_1023188).sum := by decide
  have hdescent : baseEnd_1023188 < baseStart_1023188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023199 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 5]
def baseStart_1023199 : Nat := 118140960795 + 1023199 * 2 ^ 59
def prefixEnd_1023199 : Nat := 4983230072969 + 3 ^ 40 * 1023199 * 2
def baseEnd_1023199 : Nat := 467015904177642189250577

theorem tailTrace_1023199 : CollatzResearch.WordTrace tailWord_1023199 prefixEnd_1023199 467015904177642189250577 := by
  unfold tailWord_1023199
  simp only [CollatzResearch.WordTrace]
  refine ⟨37319133420132246321872651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24879422280088164214581767 37319133420132246321872651)
  ·
    refine ⟨55978700130198369482808977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37319133420132246321872651 55978700130198369482808977)
    ·
      refine ⟨41984025097648777112106733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55978700130198369482808977 41984025097648777112106733)
      ·
        refine ⟨15744009411618291417040025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41984025097648777112106733 15744009411618291417040025)
        ·
          refine ⟨11808007058713718562780019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15744009411618291417040025 11808007058713718562780019)
          ·
            refine ⟨17712010588070577844170029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11808007058713718562780019 17712010588070577844170029)
            ·
              refine ⟨6642003970526466691563761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17712010588070577844170029 6642003970526466691563761)
              ·
                refine ⟨4981502977894850018672821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6642003970526466691563761 4981502977894850018672821)
                ·
                  refine ⟨467015904177642189250577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4981502977894850018672821 467015904177642189250577)
                  ·
                    rfl

theorem cell20_1023199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_1023199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023199 prefixEnd_1023199 := by exact prefixLift 1023199
  have htrace : WordTrace (prefixWord ++ tailWord_1023199) baseStart_1023199 baseEnd_1023199 := by
    simpa [prefixWord, tailWord_1023199, baseEnd_1023199] using wordTrace_append hprefix tailTrace_1023199
  have hstable : (prefixWord ++ tailWord_1023199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023199).length < 2 ^ (prefixWord ++ tailWord_1023199).sum := by decide
  have hdescent : baseEnd_1023199 < baseStart_1023199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023219 : List Nat := [1, 1, 1, 2, 2, 6, 3, 2, 2]
def baseStart_1023219 : Nat := 118140960795 + 1023219 * 2 ^ 59
def prefixEnd_1023219 : Nat := 4983230072969 + 3 ^ 40 * 1023219 * 2
def baseEnd_1023219 : Nat := 467025032722611008583829

theorem tailTrace_1023219 : CollatzResearch.WordTrace tailWord_1023219 prefixEnd_1023219 467025032722611008583829 := by
  unfold tailWord_1023219
  simp only [CollatzResearch.WordTrace]
  refine ⟨37319862880059789737600711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24879908586706526491733807 37319862880059789737600711)
  ·
    refine ⟨55979794320089684606401067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37319862880059789737600711 55979794320089684606401067)
    ·
      refine ⟨83969691480134526909601601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55979794320089684606401067 83969691480134526909601601)
      ·
        refine ⟨62977268610100895182201201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83969691480134526909601601 62977268610100895182201201)
        ·
          refine ⟨47232951457575671386650901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62977268610100895182201201 47232951457575671386650901)
          ·
            refine ⟨2214044599573859596249261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47232951457575671386650901 2214044599573859596249261)
            ·
              refine ⟨830266724840197348593473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2214044599573859596249261 830266724840197348593473)
              ·
                refine ⟨622700043630148011445105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 830266724840197348593473 622700043630148011445105)
                ·
                  refine ⟨467025032722611008583829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622700043630148011445105 467025032722611008583829)
                  ·
                    rfl

theorem cell20_1023219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 2].length) (baseStart_1023219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023219 prefixEnd_1023219 := by exact prefixLift 1023219
  have htrace : WordTrace (prefixWord ++ tailWord_1023219) baseStart_1023219 baseEnd_1023219 := by
    simpa [prefixWord, tailWord_1023219, baseEnd_1023219] using wordTrace_append hprefix tailTrace_1023219
  have hstable : (prefixWord ++ tailWord_1023219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023219).length < 2 ^ (prefixWord ++ tailWord_1023219).sum := by decide
  have hdescent : baseEnd_1023219 < baseStart_1023219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023233 : List Nat := [1, 2, 4, 1, 1, 3, 4, 1, 3]
def baseStart_1023233 : Nat := 118140960795 + 1023233 * 2 ^ 59
def prefixEnd_1023233 : Nat := 4983230072969 + 3 ^ 40 * 1023233 * 2
def baseEnd_1023233 : Nat := 467031422704089182117105

theorem tailTrace_1023233 : CollatzResearch.WordTrace tailWord_1023233 prefixEnd_1023233 467031422704089182117105 := by
  unfold tailWord_1023233
  simp only [CollatzResearch.WordTrace]
  refine ⟨37320373502009070128610353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24880249001339380085740235 37320373502009070128610353)
  ·
    refine ⟨27990280126506802596457765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37320373502009070128610353 27990280126506802596457765)
    ·
      refine ⟨5248177523720025486835831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27990280126506802596457765 5248177523720025486835831)
      ·
        refine ⟨7872266285580038230253747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5248177523720025486835831 7872266285580038230253747)
        ·
          refine ⟨11808399428370057345380621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7872266285580038230253747 11808399428370057345380621)
          ·
            refine ⟨4428149785638771504517733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11808399428370057345380621 4428149785638771504517733)
            ·
              refine ⟨830278084807269657097075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4428149785638771504517733 830278084807269657097075)
              ·
                refine ⟨1245417127210904485645613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830278084807269657097075 1245417127210904485645613)
                ·
                  refine ⟨467031422704089182117105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1245417127210904485645613 467031422704089182117105)
                  ·
                    rfl

theorem cell20_1023233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_1023233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023233 prefixEnd_1023233 := by exact prefixLift 1023233
  have htrace : WordTrace (prefixWord ++ tailWord_1023233) baseStart_1023233 baseEnd_1023233 := by
    simpa [prefixWord, tailWord_1023233, baseEnd_1023233] using wordTrace_append hprefix tailTrace_1023233
  have hstable : (prefixWord ++ tailWord_1023233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023233).length < 2 ^ (prefixWord ++ tailWord_1023233).sum := by decide
  have hdescent : baseEnd_1023233 < baseStart_1023233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023274 : List Nat := [3, 1, 4, 2, 1, 1, 4, 2, 2]
def baseStart_1023274 : Nat := 118140960795 + 1023274 * 2 ^ 59
def prefixEnd_1023274 : Nat := 4983230072969 + 3 ^ 40 * 1023274 * 2
def baseEnd_1023274 : Nat := 467050136221275261750271

theorem tailTrace_1023274 : CollatzResearch.WordTrace tailWord_1023274 prefixEnd_1023274 467050136221275261750271 := by
  unfold tailWord_1023274
  simp only [CollatzResearch.WordTrace]
  refine ⟨9330467223715133532713219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24881245929907022753901917 9330467223715133532713219)
  ·
    refine ⟨13995700835572700299069829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9330467223715133532713219 13995700835572700299069829)
    ·
      refine ⟨2624193906669881306075593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13995700835572700299069829 2624193906669881306075593)
      ·
        refine ⟨1968145430002410979556695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2624193906669881306075593 1968145430002410979556695)
        ·
          refine ⟨2952218145003616469335043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1968145430002410979556695 2952218145003616469335043)
          ·
            refine ⟨4428327217505424704002565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2952218145003616469335043 4428327217505424704002565)
            ·
              refine ⟨830311353282267132000481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4428327217505424704002565 830311353282267132000481)
              ·
                refine ⟨622733514961700349000361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 830311353282267132000481 622733514961700349000361)
                ·
                  refine ⟨467050136221275261750271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622733514961700349000361 467050136221275261750271)
                  ·
                    rfl

theorem cell20_1023274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_1023274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023274 prefixEnd_1023274 := by exact prefixLift 1023274
  have htrace : WordTrace (prefixWord ++ tailWord_1023274) baseStart_1023274 baseEnd_1023274 := by
    simpa [prefixWord, tailWord_1023274, baseEnd_1023274] using wordTrace_append hprefix tailTrace_1023274
  have hstable : (prefixWord ++ tailWord_1023274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023274).length < 2 ^ (prefixWord ++ tailWord_1023274).sum := by decide
  have hdescent : baseEnd_1023274 < baseStart_1023274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023285 : List Nat := [1, 3, 3, 1, 2, 4, 1, 5]
def baseStart_1023285 : Nat := 118140960795 + 1023285 * 2 ^ 59
def prefixEnd_1023285 : Nat := 4983230072969 + 3 ^ 40 * 1023285 * 2
def baseEnd_1023285 : Nat := 155685052307002704127853

theorem tailTrace_1023285 : CollatzResearch.WordTrace tailWord_1023285 prefixEnd_1023285 155685052307002704127853 := by
  unfold tailWord_1023285
  simp only [CollatzResearch.WordTrace]
  refine ⟨37322270097820683009503309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24881513398547122006335539 37322270097820683009503309)
  ·
    refine ⟨13995851286682756128563741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37322270097820683009503309 13995851286682756128563741)
    ·
      refine ⟨5248444232506033548211403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13995851286682756128563741 5248444232506033548211403)
      ·
        refine ⟨7872666348759050322317105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5248444232506033548211403 7872666348759050322317105)
        ·
          refine ⟨5904499761569287741737829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7872666348759050322317105 5904499761569287741737829)
          ·
            refine ⟨1107093705294241451575843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5904499761569287741737829 1107093705294241451575843)
            ·
              refine ⟨1660640557941362177363765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107093705294241451575843 1660640557941362177363765)
              ·
                refine ⟨155685052307002704127853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1660640557941362177363765 155685052307002704127853)
                ·
                  rfl

theorem cell20_1023285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 5].length) (baseStart_1023285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023285 prefixEnd_1023285 := by exact prefixLift 1023285
  have htrace : WordTrace (prefixWord ++ tailWord_1023285) baseStart_1023285 baseEnd_1023285 := by
    simpa [prefixWord, tailWord_1023285, baseEnd_1023285] using wordTrace_append hprefix tailTrace_1023285
  have hstable : (prefixWord ++ tailWord_1023285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023285).length < 2 ^ (prefixWord ++ tailWord_1023285).sum := by decide
  have hdescent : baseEnd_1023285 < baseStart_1023285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023292 : List Nat := [2, 2, 2, 2, 1, 3, 2, 3, 3]
def baseStart_1023292 : Nat := 118140960795 + 1023292 * 2 ^ 59
def prefixEnd_1023292 : Nat := 4983230072969 + 3 ^ 40 * 1023292 * 2
def baseEnd_1023292 : Nat := 467058351911747199150197

theorem tailTrace_1023292 : CollatzResearch.WordTrace tailWord_1023292 prefixEnd_1023292 467058351911747199150197 := by
  unfold tailWord_1023292
  simp only [CollatzResearch.WordTrace]
  refine ⟨18661262704397661602504065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24881683605863548803338753 18661262704397661602504065)
  ·
    refine ⟨13995947028298246201878049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18661262704397661602504065 13995947028298246201878049)
    ·
      refine ⟨10496960271223684651408537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13995947028298246201878049 10496960271223684651408537)
      ·
        refine ⟨7872720203417763488556403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10496960271223684651408537 7872720203417763488556403)
        ·
          refine ⟨11809080305126645232834605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7872720203417763488556403 11809080305126645232834605)
          ·
            refine ⟨4428405114422491962312977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11809080305126645232834605 4428405114422491962312977)
            ·
              refine ⟨3321303835816868971734733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4428405114422491962312977 3321303835816868971734733)
              ·
                refine ⟨1245488938431325864400525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3321303835816868971734733 1245488938431325864400525)
                ·
                  refine ⟨467058351911747199150197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1245488938431325864400525 467058351911747199150197)
                  ·
                    rfl

theorem cell20_1023292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_1023292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023292 prefixEnd_1023292 := by exact prefixLift 1023292
  have htrace : WordTrace (prefixWord ++ tailWord_1023292) baseStart_1023292 baseEnd_1023292 := by
    simpa [prefixWord, tailWord_1023292, baseEnd_1023292] using wordTrace_append hprefix tailTrace_1023292
  have hstable : (prefixWord ++ tailWord_1023292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023292).length < 2 ^ (prefixWord ++ tailWord_1023292).sum := by decide
  have hdescent : baseEnd_1023292 < baseStart_1023292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023313 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 5]
def baseStart_1023313 : Nat := 118140960795 + 1023313 * 2 ^ 59
def prefixEnd_1023313 : Nat := 4983230072969 + 3 ^ 40 * 1023313 * 2
def baseEnd_1023313 : Nat := 467067936883964459450111

theorem tailTrace_1023313 : CollatzResearch.WordTrace tailWord_1023313 prefixEnd_1023313 467067936883964459450111 := by
  unfold tailWord_1023313
  simp only [CollatzResearch.WordTrace]
  refine ⟨37323291341719243791522593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24882194227812829194348395 37323291341719243791522593)
  ·
    refine ⟨27992468506289432843641945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37323291341719243791522593 27992468506289432843641945)
    ·
      refine ⟨20994351379717074632731459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27992468506289432843641945 20994351379717074632731459)
      ·
        refine ⟨31491527069575611949097189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20994351379717074632731459 31491527069575611949097189)
        ·
          refine ⟨5904661325545427240455723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31491527069575611949097189 5904661325545427240455723)
          ·
            refine ⟨8856991988318140860683585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5904661325545427240455723 8856991988318140860683585)
            ·
              refine ⟨6642743991238605645512689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8856991988318140860683585 6642743991238605645512689)
              ·
                refine ⟨4982057993428954234134517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6642743991238605645512689 4982057993428954234134517)
                ·
                  refine ⟨467067936883964459450111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4982057993428954234134517 467067936883964459450111)
                  ·
                    rfl

theorem cell20_1023313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_1023313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023313 prefixEnd_1023313 := by exact prefixLift 1023313
  have htrace : WordTrace (prefixWord ++ tailWord_1023313) baseStart_1023313 baseEnd_1023313 := by
    simpa [prefixWord, tailWord_1023313, baseEnd_1023313] using wordTrace_append hprefix tailTrace_1023313
  have hstable : (prefixWord ++ tailWord_1023313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023313).length < 2 ^ (prefixWord ++ tailWord_1023313).sum := by decide
  have hdescent : baseEnd_1023313 < baseStart_1023313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023320 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 6]
def baseStart_1023320 : Nat := 118140960795 + 1023320 * 2 ^ 59
def prefixEnd_1023320 : Nat := 4983230072969 + 3 ^ 40 * 1023320 * 2
def baseEnd_1023320 : Nat := 467071131874703546216749

theorem tailTrace_1023320 : CollatzResearch.WordTrace tailWord_1023320 prefixEnd_1023320 467071131874703546216749 := by
  unfold tailWord_1023320
  simp only [CollatzResearch.WordTrace]
  refine ⟨18661773326346941993513707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24882364435129255991351609 18661773326346941993513707)
  ·
    refine ⟨27992659989520412990270561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18661773326346941993513707 27992659989520412990270561)
    ·
      refine ⟨20994494992140309742702921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27992659989520412990270561 20994494992140309742702921)
      ·
        refine ⟨15745871244105232307027191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20994494992140309742702921 15745871244105232307027191)
        ·
          refine ⟨23618806866157848460540787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15745871244105232307027191 23618806866157848460540787)
          ·
            refine ⟨35428210299236772690811181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23618806866157848460540787 35428210299236772690811181)
            ·
              refine ⟨13285578862213789759054193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35428210299236772690811181 13285578862213789759054193)
              ·
                refine ⟨9964184146660342319290645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13285578862213789759054193 9964184146660342319290645)
                ·
                  refine ⟨467071131874703546216749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9964184146660342319290645 467071131874703546216749)
                  ·
                    rfl

theorem cell20_1023320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_1023320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023320 prefixEnd_1023320 := by exact prefixLift 1023320
  have htrace : WordTrace (prefixWord ++ tailWord_1023320) baseStart_1023320 baseEnd_1023320 := by
    simpa [prefixWord, tailWord_1023320, baseEnd_1023320] using wordTrace_append hprefix tailTrace_1023320
  have hstable : (prefixWord ++ tailWord_1023320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023320).length < 2 ^ (prefixWord ++ tailWord_1023320).sum := by decide
  have hdescent : baseEnd_1023320 < baseStart_1023320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023330 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1023330 : Nat := 118140960795 + 1023330 * 2 ^ 59
def prefixEnd_1023330 : Nat := 4983230072969 + 3 ^ 40 * 1023330 * 2
def baseEnd_1023330 : Nat := 467075696147187955883375

theorem tailTrace_1023330 : CollatzResearch.WordTrace tailWord_1023330 prefixEnd_1023330 467075696147187955883375 := by
  unfold tailWord_1023330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9330977845664413923722861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24882607588438437129927629 9330977845664413923722861)
  ·
    refine ⟨3499116692124155221396073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9330977845664413923722861 3499116692124155221396073)
    ·
      refine ⟨2624337519093116416047055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3499116692124155221396073 2624337519093116416047055)
      ·
        refine ⟨3936506278639674624070583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2624337519093116416047055 3936506278639674624070583)
        ·
          refine ⟨5904759417959511936105875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936506278639674624070583 5904759417959511936105875)
          ·
            refine ⟨8857139126939267904158813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5904759417959511936105875 8857139126939267904158813)
            ·
              refine ⟨3321427172602225464059555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8857139126939267904158813 3321427172602225464059555)
              ·
                refine ⟨4982140758903338196089333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3321427172602225464059555 4982140758903338196089333)
                ·
                  refine ⟨467075696147187955883375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4982140758903338196089333 467075696147187955883375)
                  ·
                    rfl

theorem cell20_1023330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1023330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023330 prefixEnd_1023330 := by exact prefixLift 1023330
  have htrace : WordTrace (prefixWord ++ tailWord_1023330) baseStart_1023330 baseEnd_1023330 := by
    simpa [prefixWord, tailWord_1023330, baseEnd_1023330] using wordTrace_append hprefix tailTrace_1023330
  have hstable : (prefixWord ++ tailWord_1023330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023330).length < 2 ^ (prefixWord ++ tailWord_1023330).sum := by decide
  have hdescent : baseEnd_1023330 < baseStart_1023330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023361 : List Nat := [1, 2, 4, 3, 2, 1, 1, 6]
def baseStart_1023361 : Nat := 118140960795 + 1023361 * 2 ^ 59
def prefixEnd_1023361 : Nat := 4983230072969 + 3 ^ 40 * 1023361 * 2
def baseEnd_1023361 : Nat := 155696615130629875283305

theorem tailTrace_1023361 : CollatzResearch.WordTrace tailWord_1023361 prefixEnd_1023361 155696615130629875283305 := by
  unfold tailWord_1023361
  simp only [CollatzResearch.WordTrace]
  refine ⟨37325042045545347989269937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24883361363696898659513291 37325042045545347989269937)
  ·
    refine ⟨27993781534159010991952453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37325042045545347989269937 27993781534159010991952453)
    ·
      refine ⟨5248834037654814560991085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27993781534159010991952453 5248834037654814560991085)
      ·
        refine ⟨1968312764120555460371657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5248834037654814560991085 1968312764120555460371657)
        ·
          refine ⟨1476234573090416595278743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1968312764120555460371657 1476234573090416595278743)
          ·
            refine ⟨2214351859635624892918115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476234573090416595278743 2214351859635624892918115)
            ·
              refine ⟨3321527789453437339377173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214351859635624892918115 3321527789453437339377173)
              ·
                refine ⟨155696615130629875283305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3321527789453437339377173 155696615130629875283305)
                ·
                  rfl

theorem cell20_1023361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 6].length) (baseStart_1023361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023361 prefixEnd_1023361 := by exact prefixLift 1023361
  have htrace : WordTrace (prefixWord ++ tailWord_1023361) baseStart_1023361 baseEnd_1023361 := by
    simpa [prefixWord, tailWord_1023361, baseEnd_1023361] using wordTrace_append hprefix tailTrace_1023361
  have hstable : (prefixWord ++ tailWord_1023361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023361).length < 2 ^ (prefixWord ++ tailWord_1023361).sum := by decide
  have hdescent : baseEnd_1023361 < baseStart_1023361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023378 : List Nat := [3, 2, 3, 3, 1, 2, 6]
def baseStart_1023378 : Nat := 118140960795 + 1023378 * 2 ^ 59
def prefixEnd_1023378 : Nat := 4983230072969 + 3 ^ 40 * 1023378 * 2
def baseEnd_1023378 : Nat := 51899733850568124698131

theorem tailTrace_1023378 : CollatzResearch.WordTrace tailWord_1023378 prefixEnd_1023378 51899733850568124698131 := by
  unfold tailWord_1023378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9331415521620939973159697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24883774724322506595092525 9331415521620939973159697)
  ·
    refine ⟨6998561641215704979869773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9331415521620939973159697 6998561641215704979869773)
    ·
      refine ⟨2624460615455889367451165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6998561641215704979869773 2624460615455889367451165)
      ·
        refine ⟨984172730795958512794187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2624460615455889367451165 984172730795958512794187)
        ·
          refine ⟨1476259096193937769191281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984172730795958512794187 1476259096193937769191281)
          ·
            refine ⟨1107194322145453326893461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1476259096193937769191281 1107194322145453326893461)
            ·
              refine ⟨51899733850568124698131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1107194322145453326893461 51899733850568124698131)
              ·
                rfl

theorem cell20_1023378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 6].length) (baseStart_1023378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023378 prefixEnd_1023378 := by exact prefixLift 1023378
  have htrace : WordTrace (prefixWord ++ tailWord_1023378) baseStart_1023378 baseEnd_1023378 := by
    simpa [prefixWord, tailWord_1023378, baseEnd_1023378] using wordTrace_append hprefix tailTrace_1023378
  have hstable : (prefixWord ++ tailWord_1023378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023378).length < 2 ^ (prefixWord ++ tailWord_1023378).sum := by decide
  have hdescent : baseEnd_1023378 < baseStart_1023378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023388 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 4]
def baseStart_1023388 : Nat := 118140960795 + 1023388 * 2 ^ 59
def prefixEnd_1023388 : Nat := 4983230072969 + 3 ^ 40 * 1023388 * 2
def baseEnd_1023388 : Nat := 467102168927597531949805

theorem tailTrace_1023388 : CollatzResearch.WordTrace tailWord_1023388 prefixEnd_1023388 467102168927597531949805 := by
  unfold tailWord_1023388
  simp only [CollatzResearch.WordTrace]
  refine ⟨18663013408223765800251409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24884017877631687733668545 18663013408223765800251409)
  ·
    refine ⟨13997260056167824350188557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18663013408223765800251409 13997260056167824350188557)
    ·
      refine ⟨5248972521062934131320709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13997260056167824350188557 5248972521062934131320709)
      ·
        refine ⟨984182347699300149622633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5248972521062934131320709 984182347699300149622633)
        ·
          refine ⟨738136760774475112216975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 984182347699300149622633 738136760774475112216975)
          ·
            refine ⟨1107205141161712668325463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738136760774475112216975 1107205141161712668325463)
            ·
              refine ⟨1660807711742569002488195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107205141161712668325463 1660807711742569002488195)
              ·
                refine ⟨2491211567613853503732293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1660807711742569002488195 2491211567613853503732293)
                ·
                  refine ⟨467102168927597531949805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2491211567613853503732293 467102168927597531949805)
                  ·
                    rfl

theorem cell20_1023388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_1023388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023388 prefixEnd_1023388 := by exact prefixLift 1023388
  have htrace : WordTrace (prefixWord ++ tailWord_1023388) baseStart_1023388 baseEnd_1023388 := by
    simpa [prefixWord, tailWord_1023388, baseEnd_1023388] using wordTrace_append hprefix tailTrace_1023388
  have hstable : (prefixWord ++ tailWord_1023388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023388).length < 2 ^ (prefixWord ++ tailWord_1023388).sum := by decide
  have hdescent : baseEnd_1023388 < baseStart_1023388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023472 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 6]
def baseStart_1023472 : Nat := 118140960795 + 1023472 * 2 ^ 59
def prefixEnd_1023472 : Nat := 4983230072969 + 3 ^ 40 * 1023472 * 2
def baseEnd_1023472 : Nat := 467140508816466573149461

theorem tailTrace_1023472 : CollatzResearch.WordTrace tailWord_1023472 prefixEnd_1023472 467140508816466573149461 := by
  unfold tailWord_1023472
  simp only [CollatzResearch.WordTrace]
  refine ⟨18664545274071606973280335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24886060365428809297707113 18664545274071606973280335)
  ·
    refine ⟨27996817911107410459920503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18664545274071606973280335 27996817911107410459920503)
    ·
      refine ⟨41995226866661115689880755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27996817911107410459920503 41995226866661115689880755)
      ·
        refine ⟨62992840299991673534821133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41995226866661115689880755 62992840299991673534821133)
        ·
          refine ⟨23622315112496877575557925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62992840299991673534821133 23622315112496877575557925)
          ·
            refine ⟨4429184083593164545417111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23622315112496877575557925 4429184083593164545417111)
            ·
              refine ⟨6643776125389746818125667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4429184083593164545417111 6643776125389746818125667)
              ·
                refine ⟨9965664188084620227188501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6643776125389746818125667 9965664188084620227188501)
                ·
                  refine ⟨467140508816466573149461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9965664188084620227188501 467140508816466573149461)
                  ·
                    rfl

theorem cell20_1023472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_1023472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023472 prefixEnd_1023472 := by exact prefixLift 1023472
  have htrace : WordTrace (prefixWord ++ tailWord_1023472) baseStart_1023472 baseEnd_1023472 := by
    simpa [prefixWord, tailWord_1023472, baseEnd_1023472] using wordTrace_append hprefix tailTrace_1023472
  have hstable : (prefixWord ++ tailWord_1023472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023472).length < 2 ^ (prefixWord ++ tailWord_1023472).sum := by decide
  have hdescent : baseEnd_1023472 < baseStart_1023472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023499 : List Nat := [1, 1, 1, 1, 8, 2, 1, 2, 3]
def baseStart_1023499 : Nat := 118140960795 + 1023499 * 2 ^ 59
def prefixEnd_1023499 : Nat := 4983230072969 + 3 ^ 40 * 1023499 * 2
def baseEnd_1023499 : Nat := 467152832352174479249351

theorem tailTrace_1023499 : CollatzResearch.WordTrace tailWord_1023499 prefixEnd_1023499 467152832352174479249351 := by
  unfold tailWord_1023499
  simp only [CollatzResearch.WordTrace]
  refine ⟨37330075319045397557793551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24886716879363598371862367 37330075319045397557793551)
  ·
    refine ⟨55995112978568096336690327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37330075319045397557793551 55995112978568096336690327)
    ·
      refine ⟨83992669467852144505035491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55995112978568096336690327 83992669467852144505035491)
      ·
        refine ⟨125989004201778216757553237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83992669467852144505035491 125989004201778216757553237)
        ·
          refine ⟨1476433642989588477627577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 125989004201778216757553237 1476433642989588477627577)
          ·
            refine ⟨1107325232242191358220683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1476433642989588477627577 1107325232242191358220683)
            ·
              refine ⟨1660987848363287037331025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107325232242191358220683 1660987848363287037331025)
              ·
                refine ⟨1245740886272465277998269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660987848363287037331025 1245740886272465277998269)
                ·
                  refine ⟨467152832352174479249351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1245740886272465277998269 467152832352174479249351)
                  ·
                    rfl

theorem cell20_1023499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 3].length) (baseStart_1023499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023499 prefixEnd_1023499 := by exact prefixLift 1023499
  have htrace : WordTrace (prefixWord ++ tailWord_1023499) baseStart_1023499 baseEnd_1023499 := by
    simpa [prefixWord, tailWord_1023499, baseEnd_1023499] using wordTrace_append hprefix tailTrace_1023499
  have hstable : (prefixWord ++ tailWord_1023499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023499).length < 2 ^ (prefixWord ++ tailWord_1023499).sum := by decide
  have hdescent : baseEnd_1023499 < baseStart_1023499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023541 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 5]
def baseStart_1023541 : Nat := 118140960795 + 1023541 * 2 ^ 59
def prefixEnd_1023541 : Nat := 4983230072969 + 3 ^ 40 * 1023541 * 2
def baseEnd_1023541 : Nat := 467172002296608999849179

theorem tailTrace_1023541 : CollatzResearch.WordTrace tailWord_1023541 prefixEnd_1023541 467172002296608999849179 := by
  unfold tailWord_1023541
  simp only [CollatzResearch.WordTrace]
  refine ⟨37331607184893238730822477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24887738123262159153881651 37331607184893238730822477)
  ·
    refine ⟨13999352694334964524058429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37331607184893238730822477 13999352694334964524058429)
    ·
      refine ⟨5249757260375611696521911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13999352694334964524058429 5249757260375611696521911)
      ·
        refine ⟨7874635890563417544782867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5249757260375611696521911 7874635890563417544782867)
        ·
          refine ⟨11811953835845126317174301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7874635890563417544782867 11811953835845126317174301)
          ·
            refine ⟨4429482688441922368940363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11811953835845126317174301 4429482688441922368940363)
            ·
              refine ⟨6644224032662883553410545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4429482688441922368940363 6644224032662883553410545)
              ·
                refine ⟨4983168024497162665057909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6644224032662883553410545 4983168024497162665057909)
                ·
                  refine ⟨467172002296608999849179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4983168024497162665057909 467172002296608999849179)
                  ·
                    rfl

theorem cell20_1023541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_1023541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023541 prefixEnd_1023541 := by exact prefixLift 1023541
  have htrace : WordTrace (prefixWord ++ tailWord_1023541) baseStart_1023541 baseEnd_1023541 := by
    simpa [prefixWord, tailWord_1023541, baseEnd_1023541] using wordTrace_append hprefix tailTrace_1023541
  have hstable : (prefixWord ++ tailWord_1023541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023541).length < 2 ^ (prefixWord ++ tailWord_1023541).sum := by decide
  have hdescent : baseEnd_1023541 < baseStart_1023541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023544 : List Nat := [2, 1, 2, 1, 4, 2, 3, 3, 2]
def baseStart_1023544 : Nat := 118140960795 + 1023544 * 2 ^ 59
def prefixEnd_1023544 : Nat := 4983230072969 + 3 ^ 40 * 1023544 * 2
def baseEnd_1023544 : Nat := 467173371578354322749167

theorem tailTrace_1023544 : CollatzResearch.WordTrace tailWord_1023544 prefixEnd_1023544 467173371578354322749167 := by
  unfold tailWord_1023544
  simp only [CollatzResearch.WordTrace]
  refine ⟨18665858301941185121590843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24887811069254913495454457 18665858301941185121590843)
  ·
    refine ⟨27998787452911777682386265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18665858301941185121590843 27998787452911777682386265)
    ·
      refine ⟨20999090589683833261789699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27998787452911777682386265 20999090589683833261789699)
      ·
        refine ⟨31498635884525749892684549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20999090589683833261789699 31498635884525749892684549)
        ·
          refine ⟨5905994228348578104878353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31498635884525749892684549 5905994228348578104878353)
          ·
            refine ⟨4429495671261433578658765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5905994228348578104878353 4429495671261433578658765)
            ·
              refine ⟨1661060876723037591997037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4429495671261433578658765 1661060876723037591997037)
              ·
                refine ⟨622897828771139096998889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1661060876723037591997037 622897828771139096998889)
                ·
                  refine ⟨467173371578354322749167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622897828771139096998889 467173371578354322749167)
                  ·
                    rfl

theorem cell20_1023544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 2].length) (baseStart_1023544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023544 prefixEnd_1023544 := by exact prefixLift 1023544
  have htrace : WordTrace (prefixWord ++ tailWord_1023544) baseStart_1023544 baseEnd_1023544 := by
    simpa [prefixWord, tailWord_1023544, baseEnd_1023544] using wordTrace_append hprefix tailTrace_1023544
  have hstable : (prefixWord ++ tailWord_1023544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023544).length < 2 ^ (prefixWord ++ tailWord_1023544).sum := by decide
  have hdescent : baseEnd_1023544 < baseStart_1023544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023572 : List Nat := [2, 4, 1, 1, 1, 2, 4, 5]
def baseStart_1023572 : Nat := 118140960795 + 1023572 * 2 ^ 59
def prefixEnd_1023572 : Nat := 4983230072969 + 3 ^ 40 * 1023572 * 2
def baseEnd_1023572 : Nat := 155728717180436889938573

theorem tailTrace_1023572 : CollatzResearch.WordTrace tailWord_1023572 prefixEnd_1023572 155728717180436889938573 := by
  unfold tailWord_1023572
  simp only [CollatzResearch.WordTrace]
  refine ⟨18666368923890465512600485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24888491898520620683467313 18666368923890465512600485)
  ·
    refine ⟨3499944173229462283612591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18666368923890465512600485 3499944173229462283612591)
    ·
      refine ⟨5249916259844193425418887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3499944173229462283612591 5249916259844193425418887)
      ·
        refine ⟨7874874389766290138128331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5249916259844193425418887 7874874389766290138128331)
        ·
          refine ⟨11812311584649435207192497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7874874389766290138128331 11812311584649435207192497)
          ·
            refine ⟨8859233688487076405394373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11812311584649435207192497 8859233688487076405394373)
            ·
              refine ⟨1661106316591326826011445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8859233688487076405394373 1661106316591326826011445)
              ·
                refine ⟨155728717180436889938573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1661106316591326826011445 155728717180436889938573)
                ·
                  rfl

theorem cell20_1023572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_1023572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023572 prefixEnd_1023572 := by exact prefixLift 1023572
  have htrace : WordTrace (prefixWord ++ tailWord_1023572) baseStart_1023572 baseEnd_1023572 := by
    simpa [prefixWord, tailWord_1023572, baseEnd_1023572] using wordTrace_append hprefix tailTrace_1023572
  have hstable : (prefixWord ++ tailWord_1023572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023572).length < 2 ^ (prefixWord ++ tailWord_1023572).sum := by decide
  have hdescent : baseEnd_1023572 < baseStart_1023572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023575 : List Nat := [1, 1, 3, 2, 2, 5, 2, 1, 3]
def baseStart_1023575 : Nat := 118140960795 + 1023575 * 2 ^ 59
def prefixEnd_1023575 : Nat := 4983230072969 + 3 ^ 40 * 1023575 * 2
def baseEnd_1023575 : Nat := 467187520823055992715707

theorem tailTrace_1023575 : CollatzResearch.WordTrace tailWord_1023575 prefixEnd_1023575 467187520823055992715707 := by
  unfold tailWord_1023575
  simp only [CollatzResearch.WordTrace]
  refine ⟨37332847266770062537560179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24888564844513375025040119 37332847266770062537560179)
  ·
    refine ⟨55999270900155093806340269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37332847266770062537560179 55999270900155093806340269)
    ·
      refine ⟨20999726587558160177377601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55999270900155093806340269 20999726587558160177377601)
      ·
        refine ⟨15749794940668620133033201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20999726587558160177377601 15749794940668620133033201)
        ·
          refine ⟨11812346205501465099774901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15749794940668620133033201 11812346205501465099774901)
          ·
            refine ⟨1107407456765762353103897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11812346205501465099774901 1107407456765762353103897)
            ·
              refine ⟨830555592574321764827923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107407456765762353103897 830555592574321764827923)
              ·
                refine ⟨1245833388861482647241885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830555592574321764827923 1245833388861482647241885)
                ·
                  refine ⟨467187520823055992715707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1245833388861482647241885 467187520823055992715707)
                  ·
                    rfl

theorem cell20_1023575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 3].length) (baseStart_1023575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023575 prefixEnd_1023575 := by exact prefixLift 1023575
  have htrace : WordTrace (prefixWord ++ tailWord_1023575) baseStart_1023575 baseEnd_1023575 := by
    simpa [prefixWord, tailWord_1023575, baseEnd_1023575] using wordTrace_append hprefix tailTrace_1023575
  have hstable : (prefixWord ++ tailWord_1023575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023575).length < 2 ^ (prefixWord ++ tailWord_1023575).sum := by decide
  have hdescent : baseEnd_1023575 < baseStart_1023575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023593 : List Nat := [1, 2, 1, 1, 1, 4, 4, 6]
def baseStart_1023593 : Nat := 118140960795 + 1023593 * 2 ^ 59
def prefixEnd_1023593 : Nat := 4983230072969 + 3 ^ 40 * 1023593 * 2
def baseEnd_1023593 : Nat := 155731912171175976705211

theorem tailTrace_1023593 : CollatzResearch.WordTrace tailWord_1023593 prefixEnd_1023593 155731912171175976705211 := by
  unfold tailWord_1023593
  simp only [CollatzResearch.WordTrace]
  refine ⟨37333503780704851611715433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24889002520469901074476955 37333503780704851611715433)
  ·
    refine ⟨28000127835528638708786575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37333503780704851611715433 28000127835528638708786575)
    ·
      refine ⟨42000191753292958063179863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28000127835528638708786575 42000191753292958063179863)
      ·
        refine ⟨63000287629939437094769795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42000191753292958063179863 63000287629939437094769795)
        ·
          refine ⟨94500431444909155642154693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63000287629939437094769795 94500431444909155642154693)
          ·
            refine ⟨17718830895920466682904005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94500431444909155642154693 17718830895920466682904005)
            ·
              refine ⟨3322280792985087503044501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17718830895920466682904005 3322280792985087503044501)
              ·
                refine ⟨155731912171175976705211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3322280792985087503044501 155731912171175976705211)
                ·
                  rfl

theorem cell20_1023593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 6].length) (baseStart_1023593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023593 prefixEnd_1023593 := by exact prefixLift 1023593
  have htrace : WordTrace (prefixWord ++ tailWord_1023593) baseStart_1023593 baseEnd_1023593 := by
    simpa [prefixWord, tailWord_1023593, baseEnd_1023593] using wordTrace_append hprefix tailTrace_1023593
  have hstable : (prefixWord ++ tailWord_1023593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023593).length < 2 ^ (prefixWord ++ tailWord_1023593).sum := by decide
  have hdescent : baseEnd_1023593 < baseStart_1023593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023679 : List Nat := [1, 1, 2, 2, 2, 3, 1, 6, 2]
def baseStart_1023679 : Nat := 118140960795 + 1023679 * 2 ^ 59
def prefixEnd_1023679 : Nat := 4983230072969 + 3 ^ 40 * 1023679 * 2
def baseEnd_1023679 : Nat := 467234989256893853248615

theorem tailTrace_1023679 : CollatzResearch.WordTrace tailWord_1023679 prefixEnd_1023679 467234989256893853248615 := by
  unfold tailWord_1023679
  simp only [CollatzResearch.WordTrace]
  refine ⟨37336640458393288299346091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24891093638928858866230727 37336640458393288299346091)
  ·
    refine ⟨56004960687589932449019137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37336640458393288299346091 56004960687589932449019137)
    ·
      refine ⟨42003720515692449336764353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56004960687589932449019137 42003720515692449336764353)
      ·
        refine ⟨31502790386769337002573265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42003720515692449336764353 31502790386769337002573265)
        ·
          refine ⟨23627092790077002751929949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31502790386769337002573265 23627092790077002751929949)
          ·
            refine ⟨8860159796278876031973731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23627092790077002751929949 8860159796278876031973731)
            ·
              refine ⟨13290239694418314047960597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8860159796278876031973731 13290239694418314047960597)
              ·
                refine ⟨622979985675858470998153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13290239694418314047960597 622979985675858470998153)
                ·
                  refine ⟨467234989256893853248615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622979985675858470998153 467234989256893853248615)
                  ·
                    rfl

theorem cell20_1023679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 2].length) (baseStart_1023679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023679 prefixEnd_1023679 := by exact prefixLift 1023679
  have htrace : WordTrace (prefixWord ++ tailWord_1023679) baseStart_1023679 baseEnd_1023679 := by
    simpa [prefixWord, tailWord_1023679, baseEnd_1023679] using wordTrace_append hprefix tailTrace_1023679
  have hstable : (prefixWord ++ tailWord_1023679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023679).length < 2 ^ (prefixWord ++ tailWord_1023679).sum := by decide
  have hdescent : baseEnd_1023679 < baseStart_1023679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023709 : List Nat := [1, 4, 3, 3, 2, 1, 1, 3, 2]
def baseStart_1023709 : Nat := 118140960795 + 1023709 * 2 ^ 59
def prefixEnd_1023709 : Nat := 4983230072969 + 3 ^ 40 * 1023709 * 2
def baseEnd_1023709 : Nat := 467248682074347082248493

theorem tailTrace_1023709 : CollatzResearch.WordTrace tailWord_1023709 prefixEnd_1023709 467248682074347082248493 := by
  unfold tailWord_1023709
  simp only [CollatzResearch.WordTrace]
  refine ⟨37337734648284603422938181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24891823098856402281958787 37337734648284603422938181)
  ·
    refine ⟨7000825246553363141800909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37337734648284603422938181 7000825246553363141800909)
    ·
      refine ⟨2625309467457511178175341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7000825246553363141800909 2625309467457511178175341)
      ·
        refine ⟨984491050296566691815753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2625309467457511178175341 984491050296566691815753)
        ·
          refine ⟨738368287722425018861815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 984491050296566691815753 738368287722425018861815)
          ·
            refine ⟨1107552431583637528292723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738368287722425018861815 1107552431583637528292723)
            ·
              refine ⟨1661328647375456292439085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107552431583637528292723 1661328647375456292439085)
              ·
                refine ⟨622998242765796109664657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1661328647375456292439085 622998242765796109664657)
                ·
                  refine ⟨467248682074347082248493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622998242765796109664657 467248682074347082248493)
                  ·
                    rfl

theorem cell20_1023709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_1023709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023709 prefixEnd_1023709 := by exact prefixLift 1023709
  have htrace : WordTrace (prefixWord ++ tailWord_1023709) baseStart_1023709 baseEnd_1023709 := by
    simpa [prefixWord, tailWord_1023709, baseEnd_1023709] using wordTrace_append hprefix tailTrace_1023709
  have hstable : (prefixWord ++ tailWord_1023709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023709).length < 2 ^ (prefixWord ++ tailWord_1023709).sum := by decide
  have hdescent : baseEnd_1023709 < baseStart_1023709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023713 : List Nat := [1, 2, 3, 1, 5, 2, 1, 3, 2]
def baseStart_1023713 : Nat := 118140960795 + 1023713 * 2 ^ 59
def prefixEnd_1023713 : Nat := 4983230072969 + 3 ^ 40 * 1023713 * 2
def baseEnd_1023713 : Nat := 467250507783340846115143

theorem tailTrace_1023713 : CollatzResearch.WordTrace tailWord_1023713 prefixEnd_1023713 467250507783340846115143 := by
  unfold tailWord_1023713
  simp only [CollatzResearch.WordTrace]
  refine ⟨37337880540270112106083793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24891920360180074737389195 37337880540270112106083793)
  ·
    refine ⟨28003410405202584079562845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37337880540270112106083793 28003410405202584079562845)
    ·
      refine ⟨10501278901950969029836067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28003410405202584079562845 10501278901950969029836067)
      ·
        refine ⟨15751918352926453544754101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10501278901950969029836067 15751918352926453544754101)
        ·
          refine ⟨1476742345586855019820697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15751918352926453544754101 1476742345586855019820697)
          ·
            refine ⟨1107556759190141264865523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1476742345586855019820697 1107556759190141264865523)
            ·
              refine ⟨1661335138785211897298285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107556759190141264865523 1661335138785211897298285)
              ·
                refine ⟨623000677044454461486857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1661335138785211897298285 623000677044454461486857)
                ·
                  refine ⟨467250507783340846115143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623000677044454461486857 467250507783340846115143)
                  ·
                    rfl

theorem cell20_1023713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 2].length) (baseStart_1023713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023713 prefixEnd_1023713 := by exact prefixLift 1023713
  have htrace : WordTrace (prefixWord ++ tailWord_1023713) baseStart_1023713 baseEnd_1023713 := by
    simpa [prefixWord, tailWord_1023713, baseEnd_1023713] using wordTrace_append hprefix tailTrace_1023713
  have hstable : (prefixWord ++ tailWord_1023713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023713).length < 2 ^ (prefixWord ++ tailWord_1023713).sum := by decide
  have hdescent : baseEnd_1023713 < baseStart_1023713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023734 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_1023734 : Nat := 118140960795 + 1023734 * 2 ^ 59
def prefixEnd_1023734 : Nat := 4983230072969 + 3 ^ 40 * 1023734 * 2
def baseEnd_1023734 : Nat := 467260092755558106415057

theorem tailTrace_1023734 : CollatzResearch.WordTrace tailWord_1023734 prefixEnd_1023734 467260092755558106415057 := by
  unfold tailWord_1023734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333665404574627043287391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24892430982129355128398837 2333665404574627043287391)
  ·
    refine ⟨3500498106861940564931087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2333665404574627043287391 3500498106861940564931087)
    ·
      refine ⟨5250747160292910847396631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3500498106861940564931087 5250747160292910847396631)
      ·
        refine ⟨7876120740439366271094947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5250747160292910847396631 7876120740439366271094947)
        ·
          refine ⟨11814181110659049406642421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7876120740439366271094947 11814181110659049406642421)
          ·
            refine ⟨1107579479124285881872727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11814181110659049406642421 1107579479124285881872727)
            ·
              refine ⟨1661369218686428822809091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107579479124285881872727 1661369218686428822809091)
              ·
                refine ⟨2492053828029643234213637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661369218686428822809091 2492053828029643234213637)
                ·
                  refine ⟨467260092755558106415057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2492053828029643234213637 467260092755558106415057)
                  ·
                    rfl

theorem cell20_1023734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_1023734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023734 prefixEnd_1023734 := by exact prefixLift 1023734
  have htrace : WordTrace (prefixWord ++ tailWord_1023734) baseStart_1023734 baseEnd_1023734 := by
    simpa [prefixWord, tailWord_1023734, baseEnd_1023734] using wordTrace_append hprefix tailTrace_1023734
  have hstable : (prefixWord ++ tailWord_1023734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023734).length < 2 ^ (prefixWord ++ tailWord_1023734).sum := by decide
  have hdescent : baseEnd_1023734 < baseStart_1023734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023745 : List Nat := [1, 2, 4, 1, 1, 1, 3, 7]
def baseStart_1023745 : Nat := 118140960795 + 1023745 * 2 ^ 59
def prefixEnd_1023745 : Nat := 4983230072969 + 3 ^ 40 * 1023745 * 2
def baseEnd_1023745 : Nat := 155755037818430319016115

theorem tailTrace_1023745 : CollatzResearch.WordTrace tailWord_1023745 prefixEnd_1023745 155755037818430319016115 := by
  unfold tailWord_1023745
  simp only [CollatzResearch.WordTrace]
  refine ⟨37339047676154181571248689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24892698450769454380832459 37339047676154181571248689)
  ·
    refine ⟨28004285757115636178436517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37339047676154181571248689 28004285757115636178436517)
    ·
      refine ⟨5250803579459181783456847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28004285757115636178436517 5250803579459181783456847)
      ·
        refine ⟨7876205369188772675185271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5250803579459181783456847 7876205369188772675185271)
        ·
          refine ⟨11814308053783159012777907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7876205369188772675185271 11814308053783159012777907)
          ·
            refine ⟨17721462080674738519166861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11814308053783159012777907 17721462080674738519166861)
            ·
              refine ⟨6645548280253026944687573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17721462080674738519166861 6645548280253026944687573)
              ·
                refine ⟨155755037818430319016115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6645548280253026944687573 155755037818430319016115)
                ·
                  rfl

theorem cell20_1023745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 7].length) (baseStart_1023745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023745 prefixEnd_1023745 := by exact prefixLift 1023745
  have htrace : WordTrace (prefixWord ++ tailWord_1023745) baseStart_1023745 baseEnd_1023745 := by
    simpa [prefixWord, tailWord_1023745, baseEnd_1023745] using wordTrace_append hprefix tailTrace_1023745
  have hstable : (prefixWord ++ tailWord_1023745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023745).length < 2 ^ (prefixWord ++ tailWord_1023745).sum := by decide
  have hdescent : baseEnd_1023745 < baseStart_1023745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023748 : List Nat := [2, 3, 2, 2, 1, 3, 1, 3, 3]
def baseStart_1023748 : Nat := 118140960795 + 1023748 * 2 ^ 59
def prefixEnd_1023748 : Nat := 4983230072969 + 3 ^ 40 * 1023748 * 2
def baseEnd_1023748 : Nat := 467266482737036279948333

theorem tailTrace_1023748 : CollatzResearch.WordTrace tailWord_1023748 prefixEnd_1023748 467266482737036279948333 := by
  unfold tailWord_1023748
  simp only [CollatzResearch.WordTrace]
  refine ⟨18669578547571656541803949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24892771396762208722405265 18669578547571656541803949)
  ·
    refine ⟨7001091955339371203176481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18669578547571656541803949 7001091955339371203176481)
    ·
      refine ⟨5250818966504528402382361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7001091955339371203176481 5250818966504528402382361)
      ·
        refine ⟨3938114224878396301786771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5250818966504528402382361 3938114224878396301786771)
        ·
          refine ⟨5907171337317594452680157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3938114224878396301786771 5907171337317594452680157)
          ·
            refine ⟨2215189251494097919755059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5907171337317594452680157 2215189251494097919755059)
            ·
              refine ⟨3322783877241146879632589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215189251494097919755059 3322783877241146879632589)
              ·
                refine ⟨1246043953965430079862221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3322783877241146879632589 1246043953965430079862221)
                ·
                  refine ⟨467266482737036279948333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1246043953965430079862221 467266482737036279948333)
                  ·
                    rfl

theorem cell20_1023748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_1023748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023748 prefixEnd_1023748 := by exact prefixLift 1023748
  have htrace : WordTrace (prefixWord ++ tailWord_1023748) baseStart_1023748 baseEnd_1023748 := by
    simpa [prefixWord, tailWord_1023748, baseEnd_1023748] using wordTrace_append hprefix tailTrace_1023748
  have hstable : (prefixWord ++ tailWord_1023748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023748).length < 2 ^ (prefixWord ++ tailWord_1023748).sum := by decide
  have hdescent : baseEnd_1023748 < baseStart_1023748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023800 : List Nat := [2, 1, 2, 1, 3, 5, 1, 5]
def baseStart_1023800 : Nat := 118140960795 + 1023800 * 2 ^ 59
def prefixEnd_1023800 : Nat := 4983230072969 + 3 ^ 40 * 1023800 * 2
def baseEnd_1023800 : Nat := 155763405651318403404929

theorem tailTrace_1023800 : CollatzResearch.WordTrace tailWord_1023800 prefixEnd_1023800 155763405651318403404929 := by
  unfold tailWord_1023800
  simp only [CollatzResearch.WordTrace]
  refine ⟨18670526845477462982250427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24894035793969950643000569 18670526845477462982250427)
  ·
    refine ⟨28005790268216194473375641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18670526845477462982250427 28005790268216194473375641)
    ·
      refine ⟨21004342701162145855031731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28005790268216194473375641 21004342701162145855031731)
      ·
        refine ⟨31506514051743218782547597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21004342701162145855031731 31506514051743218782547597)
        ·
          refine ⟨11814942769403707043455349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31506514051743218782547597 11814942769403707043455349)
          ·
            refine ⟨1107650884631597535323939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11814942769403707043455349 1107650884631597535323939)
            ·
              refine ⟨1661476326947396302985909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107650884631597535323939 1661476326947396302985909)
              ·
                refine ⟨155763405651318403404929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1661476326947396302985909 155763405651318403404929)
                ·
                  rfl

theorem cell20_1023800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_1023800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023800 prefixEnd_1023800 := by exact prefixLift 1023800
  have htrace : WordTrace (prefixWord ++ tailWord_1023800) baseStart_1023800 baseEnd_1023800 := by
    simpa [prefixWord, tailWord_1023800, baseEnd_1023800] using wordTrace_append hprefix tailTrace_1023800
  have hstable : (prefixWord ++ tailWord_1023800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023800).length < 2 ^ (prefixWord ++ tailWord_1023800).sum := by decide
  have hdescent : baseEnd_1023800 < baseStart_1023800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023852 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 4]
def baseStart_1023852 : Nat := 118140960795 + 1023852 * 2 ^ 59
def prefixEnd_1023852 : Nat := 4983230072969 + 3 ^ 40 * 1023852 * 2
def baseEnd_1023852 : Nat := 467313951170874140481241

theorem tailTrace_1023852 : CollatzResearch.WordTrace tailWord_1023852 prefixEnd_1023852 467313951170874140481241 := by
  unfold tailWord_1023852
  simp only [CollatzResearch.WordTrace]
  refine ⟨18671475143383269422696905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24895300191177692563595873 18671475143383269422696905)
  ·
    refine ⟨14003606357537452067022679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18671475143383269422696905 14003606357537452067022679)
    ·
      refine ⟨21005409536306178100534019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14003606357537452067022679 21005409536306178100534019)
      ·
        refine ⟨31508114304459267150801029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21005409536306178100534019 31508114304459267150801029)
        ·
          refine ⟨5907771432086112590775193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31508114304459267150801029 5907771432086112590775193)
          ·
            refine ⟨4430828574064584443081395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5907771432086112590775193 4430828574064584443081395)
            ·
              refine ⟨6646242861096876664622093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4430828574064584443081395 6646242861096876664622093)
              ·
                refine ⟨2492341072911328749233285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6646242861096876664622093 2492341072911328749233285)
                ·
                  refine ⟨467313951170874140481241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2492341072911328749233285 467313951170874140481241)
                  ·
                    rfl

theorem cell20_1023852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_1023852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023852 prefixEnd_1023852 := by exact prefixLift 1023852
  have htrace : WordTrace (prefixWord ++ tailWord_1023852) baseStart_1023852 baseEnd_1023852 := by
    simpa [prefixWord, tailWord_1023852, baseEnd_1023852] using wordTrace_append hprefix tailTrace_1023852
  have hstable : (prefixWord ++ tailWord_1023852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023852).length < 2 ^ (prefixWord ++ tailWord_1023852).sum := by decide
  have hdescent : baseEnd_1023852 < baseStart_1023852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023876 : List Nat := [2, 3, 2, 1, 1, 1, 6, 4]
def baseStart_1023876 : Nat := 118140960795 + 1023876 * 2 ^ 59
def prefixEnd_1023876 : Nat := 4983230072969 + 3 ^ 40 * 1023876 * 2
def baseEnd_1023876 : Nat := 155774968474945574560381

theorem tailTrace_1023876 : CollatzResearch.WordTrace tailWord_1023876 prefixEnd_1023876 155774968474945574560381 := by
  unfold tailWord_1023876
  simp only [CollatzResearch.WordTrace]
  refine ⟨18671912819339795472133741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24895883759119727296178321 18671912819339795472133741)
  ·
    refine ⟨7001967307252423302050153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18671912819339795472133741 7001967307252423302050153)
    ·
      refine ⟨5251475480439317476537615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7001967307252423302050153 5251475480439317476537615)
      ·
        refine ⟨7877213220658976214806423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5251475480439317476537615 7877213220658976214806423)
        ·
          refine ⟨11815819830988464322209635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7877213220658976214806423 11815819830988464322209635)
          ·
            refine ⟨17723729746482696483314453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11815819830988464322209635 17723729746482696483314453)
            ·
              refine ⟨830799831866376397655365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17723729746482696483314453 830799831866376397655365)
              ·
                refine ⟨155774968474945574560381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 830799831866376397655365 155774968474945574560381)
                ·
                  rfl

theorem cell20_1023876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_1023876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023876 prefixEnd_1023876 := by exact prefixLift 1023876
  have htrace : WordTrace (prefixWord ++ tailWord_1023876) baseStart_1023876 baseEnd_1023876 := by
    simpa [prefixWord, tailWord_1023876, baseEnd_1023876] using wordTrace_append hprefix tailTrace_1023876
  have hstable : (prefixWord ++ tailWord_1023876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023876).length < 2 ^ (prefixWord ++ tailWord_1023876).sum := by decide
  have hdescent : baseEnd_1023876 < baseStart_1023876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023882 : List Nat := [3, 1, 2, 4, 3, 1, 1, 3, 2]
def baseStart_1023882 : Nat := 118140960795 + 1023882 * 2 ^ 59
def prefixEnd_1023882 : Nat := 4983230072969 + 3 ^ 40 * 1023882 * 2
def baseEnd_1023882 : Nat := 467327643988327369481119

theorem tailTrace_1023882 : CollatzResearch.WordTrace tailWord_1023882 prefixEnd_1023882 467327643988327369481119 := by
  unfold tailWord_1023882
  simp only [CollatzResearch.WordTrace]
  refine ⟨9336011119164463492246475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24896029651105235979323933 9336011119164463492246475)
  ·
    refine ⟨14004016678746695238369713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9336011119164463492246475 14004016678746695238369713)
    ·
      refine ⟨10503012509060021428777285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14004016678746695238369713 10503012509060021428777285)
      ·
        refine ⟨1969314845448754017895741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10503012509060021428777285 1969314845448754017895741)
        ·
          refine ⟨738493067043282756710903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1969314845448754017895741 738493067043282756710903)
          ·
            refine ⟨1107739600564924135066355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738493067043282756710903 1107739600564924135066355)
            ·
              refine ⟨1661609400847386202599533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107739600564924135066355 1661609400847386202599533)
              ·
                refine ⟨623103525317769825974825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1661609400847386202599533 623103525317769825974825)
                ·
                  refine ⟨467327643988327369481119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623103525317769825974825 467327643988327369481119)
                  ·
                    rfl

theorem cell20_1023882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_1023882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023882 prefixEnd_1023882 := by exact prefixLift 1023882
  have htrace : WordTrace (prefixWord ++ tailWord_1023882) baseStart_1023882 baseEnd_1023882 := by
    simpa [prefixWord, tailWord_1023882, baseEnd_1023882] using wordTrace_append hprefix tailTrace_1023882
  have hstable : (prefixWord ++ tailWord_1023882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023882).length < 2 ^ (prefixWord ++ tailWord_1023882).sum := by decide
  have hdescent : baseEnd_1023882 < baseStart_1023882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023903 : List Nat := [1, 1, 2, 5, 3, 1, 3, 2, 2]
def baseStart_1023903 : Nat := 118140960795 + 1023903 * 2 ^ 59
def prefixEnd_1023903 : Nat := 4983230072969 + 3 ^ 40 * 1023903 * 2
def baseEnd_1023903 : Nat := 467337228960544629781033

theorem tailTrace_1023903 : CollatzResearch.WordTrace tailWord_1023903 prefixEnd_1023903 467337228960544629781033 := by
  unfold tailWord_1023903
  simp only [CollatzResearch.WordTrace]
  refine ⟨37344810409581774555500363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24896540273054516370333575 37344810409581774555500363)
  ·
    refine ⟨56017215614372661833250545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37344810409581774555500363 56017215614372661833250545)
    ·
      refine ⟨42012911710779496374937909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56017215614372661833250545 42012911710779496374937909)
      ·
        refine ⟨3938710472885577785150429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42012911710779496374937909 3938710472885577785150429)
        ·
          refine ⟨1477016427332091669431411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3938710472885577785150429 1477016427332091669431411)
          ·
            refine ⟨2215524640998137504147117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477016427332091669431411 2215524640998137504147117)
            ·
              refine ⟨830821740374301564055169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2215524640998137504147117 830821740374301564055169)
              ·
                refine ⟨623116305280726173041377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 830821740374301564055169 623116305280726173041377)
                ·
                  refine ⟨467337228960544629781033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623116305280726173041377 467337228960544629781033)
                  ·
                    rfl

theorem cell20_1023903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 2].length) (baseStart_1023903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023903 prefixEnd_1023903 := by exact prefixLift 1023903
  have htrace : WordTrace (prefixWord ++ tailWord_1023903) baseStart_1023903 baseEnd_1023903 := by
    simpa [prefixWord, tailWord_1023903, baseEnd_1023903] using wordTrace_append hprefix tailTrace_1023903
  have hstable : (prefixWord ++ tailWord_1023903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023903).length < 2 ^ (prefixWord ++ tailWord_1023903).sum := by decide
  have hdescent : baseEnd_1023903 < baseStart_1023903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023959 : List Nat := [1, 1, 3, 2, 1, 1, 6, 2, 3]
def baseStart_1023959 : Nat := 118140960795 + 1023959 * 2 ^ 59
def prefixEnd_1023959 : Nat := 4983230072969 + 3 ^ 40 * 1023959 * 2
def baseEnd_1023959 : Nat := 467362788886457323914137

theorem tailTrace_1023959 : CollatzResearch.WordTrace tailWord_1023959 prefixEnd_1023959 467362788886457323914137 := by
  unfold tailWord_1023959
  simp only [CollatzResearch.WordTrace]
  refine ⟨37346852897378896119538931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24897901931585930746359287 37346852897378896119538931)
  ·
    refine ⟨56020279346068344179308397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37346852897378896119538931 56020279346068344179308397)
    ·
      refine ⟨21007604754775629067240649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56020279346068344179308397 21007604754775629067240649)
      ·
        refine ⟨15755703566081721800430487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21007604754775629067240649 15755703566081721800430487)
        ·
          refine ⟨23633555349122582700645731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15755703566081721800430487 23633555349122582700645731)
          ·
            refine ⟨35450333023683874050968597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23633555349122582700645731 35450333023683874050968597)
            ·
              refine ⟨1661734360485181596139153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35450333023683874050968597 1661734360485181596139153)
              ·
                refine ⟨1246300770363886197104365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1661734360485181596139153 1246300770363886197104365)
                ·
                  refine ⟨467362788886457323914137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1246300770363886197104365 467362788886457323914137)
                  ·
                    rfl

theorem cell20_1023959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 3].length) (baseStart_1023959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023959 prefixEnd_1023959 := by exact prefixLift 1023959
  have htrace : WordTrace (prefixWord ++ tailWord_1023959) baseStart_1023959 baseEnd_1023959 := by
    simpa [prefixWord, tailWord_1023959, baseEnd_1023959] using wordTrace_append hprefix tailTrace_1023959
  have hstable : (prefixWord ++ tailWord_1023959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023959).length < 2 ^ (prefixWord ++ tailWord_1023959).sum := by decide
  have hdescent : baseEnd_1023959 < baseStart_1023959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023962 : List Nat := [3, 1, 1, 2, 5, 1, 1, 4, 2]
def baseStart_1023962 : Nat := 118140960795 + 1023962 * 2 ^ 59
def prefixEnd_1023962 : Nat := 4983230072969 + 3 ^ 40 * 1023962 * 2
def baseEnd_1023962 : Nat := 467364158168202646814125

theorem tailTrace_1023962 : CollatzResearch.WordTrace tailWord_1023962 prefixEnd_1023962 467364158168202646814125 := by
  unfold tailWord_1023962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9336740579092006907974535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24897974877578685087932093 9336740579092006907974535)
  ·
    refine ⟨14005110868638010361961803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9336740579092006907974535 14005110868638010361961803)
    ·
      refine ⟨21007666302957015542942705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14005110868638010361961803 21007666302957015542942705)
      ·
        refine ⟨15755749727217761657207029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21007666302957015542942705 15755749727217761657207029)
        ·
          refine ⟨1477101536926665155363159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15755749727217761657207029 1477101536926665155363159)
          ·
            refine ⟨2215652305389997733044739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477101536926665155363159 2215652305389997733044739)
            ·
              refine ⟨3323478458084996599567109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215652305389997733044739 3323478458084996599567109)
              ·
                refine ⟨623152210890936862418833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3323478458084996599567109 623152210890936862418833)
                ·
                  refine ⟨467364158168202646814125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623152210890936862418833 467364158168202646814125)
                  ·
                    rfl

theorem cell20_1023962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_1023962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1023962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1023962 prefixEnd_1023962 := by exact prefixLift 1023962
  have htrace : WordTrace (prefixWord ++ tailWord_1023962) baseStart_1023962 baseEnd_1023962 := by
    simpa [prefixWord, tailWord_1023962, baseEnd_1023962] using wordTrace_append hprefix tailTrace_1023962
  have hstable : (prefixWord ++ tailWord_1023962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023962).length < 2 ^ (prefixWord ++ tailWord_1023962).sum := by decide
  have hdescent : baseEnd_1023962 < baseStart_1023962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024006 : List Nat := [6, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1024006 : Nat := 118140960795 + 1024006 * 2 ^ 59
def prefixEnd_1024006 : Nat := 4983230072969 + 3 ^ 40 * 1024006 * 2
def baseEnd_1024006 : Nat := 467384240967134049347279

theorem tailTrace_1024006 : CollatzResearch.WordTrace tailWord_1024006 prefixEnd_1024006 467384240967134049347279 := by
  unfold tailWord_1024006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1167142722756519473328121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24899044752139082097666581 1167142722756519473328121)
  ·
    refine ⟨875357042067389604996091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1167142722756519473328121 875357042067389604996091)
    ·
      refine ⟨1313035563101084407494137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 875357042067389604996091 1313035563101084407494137)
      ·
        refine ⟨984776672325813305620603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1313035563101084407494137 984776672325813305620603)
        ·
          refine ⟨1477165008488719958430905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984776672325813305620603 1477165008488719958430905)
          ·
            refine ⟨1107873756366539968823179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1477165008488719958430905 1107873756366539968823179)
            ·
              refine ⟨1661810634549809953234769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107873756366539968823179 1661810634549809953234769)
              ·
                refine ⟨1246357975912357464926077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1661810634549809953234769 1246357975912357464926077)
                ·
                  refine ⟨467384240967134049347279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1246357975912357464926077 467384240967134049347279)
                  ·
                    rfl

theorem cell20_1024006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1024006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024006 prefixEnd_1024006 := by exact prefixLift 1024006
  have htrace : WordTrace (prefixWord ++ tailWord_1024006) baseStart_1024006 baseEnd_1024006 := by
    simpa [prefixWord, tailWord_1024006, baseEnd_1024006] using wordTrace_append hprefix tailTrace_1024006
  have hstable : (prefixWord ++ tailWord_1024006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024006).length < 2 ^ (prefixWord ++ tailWord_1024006).sum := by decide
  have hdescent : baseEnd_1024006 < baseStart_1024006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024021 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 4]
def baseStart_1024021 : Nat := 118140960795 + 1024021 * 2 ^ 59
def prefixEnd_1024021 : Nat := 4983230072969 + 3 ^ 40 * 1024021 * 2
def baseEnd_1024021 : Nat := 467391087375860663847217

theorem tailTrace_1024021 : CollatzResearch.WordTrace tailWord_1024021 prefixEnd_1024021 467391087375860663847217 := by
  unfold tailWord_1024021
  simp only [CollatzResearch.WordTrace]
  refine ⟨37349114223154280708295917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24899409482102853805530611 37349114223154280708295917)
  ·
    refine ⟨14005917833682855265610969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37349114223154280708295917 14005917833682855265610969)
    ·
      refine ⟨10504438375262141449208227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14005917833682855265610969 10504438375262141449208227)
      ·
        refine ⟨15756657562893212173812341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10504438375262141449208227 15756657562893212173812341)
        ·
          refine ⟨1477186646521238641294907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15756657562893212173812341 1477186646521238641294907)
          ·
            refine ⟨2215779969781857961942361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477186646521238641294907 2215779969781857961942361)
            ·
              refine ⟨1661834977336393471456771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2215779969781857961942361 1661834977336393471456771)
              ·
                refine ⟨2492752466004590207185157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661834977336393471456771 2492752466004590207185157)
                ·
                  refine ⟨467391087375860663847217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2492752466004590207185157 467391087375860663847217)
                  ·
                    rfl

theorem cell20_1024021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_1024021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024021 prefixEnd_1024021 := by exact prefixLift 1024021
  have htrace : WordTrace (prefixWord ++ tailWord_1024021) baseStart_1024021 baseEnd_1024021 := by
    simpa [prefixWord, tailWord_1024021, baseEnd_1024021] using wordTrace_append hprefix tailTrace_1024021
  have hstable : (prefixWord ++ tailWord_1024021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024021).length < 2 ^ (prefixWord ++ tailWord_1024021).sum := by decide
  have hdescent : baseEnd_1024021 < baseStart_1024021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024049 : List Nat := [1, 2, 2, 3, 1, 4, 1, 6]
def baseStart_1024049 : Nat := 118140960795 + 1024049 * 2 ^ 59
def prefixEnd_1024049 : Nat := 4983230072969 + 3 ^ 40 * 1024049 * 2
def baseEnd_1024049 : Nat := 155801289112939003637923

theorem tailTrace_1024049 : CollatzResearch.WordTrace tailWord_1024049 prefixEnd_1024049 155801289112939003637923 := by
  unfold tailWord_1024049
  simp only [CollatzResearch.WordTrace]
  refine ⟨37350135467052841490315201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24900090311368560993543467 37350135467052841490315201)
  ·
    refine ⟨28012601600289631117736401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37350135467052841490315201 28012601600289631117736401)
    ·
      refine ⟨21009451200217223338302301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28012601600289631117736401 21009451200217223338302301)
      ·
        refine ⟨7878544200081458751863363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21009451200217223338302301 7878544200081458751863363)
        ·
          refine ⟨11817816300122188127795045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7878544200081458751863363 11817816300122188127795045)
          ·
            refine ⟨2215840556272910273961571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11817816300122188127795045 2215840556272910273961571)
            ·
              refine ⟨3323760834409365410942357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215840556272910273961571 3323760834409365410942357)
              ·
                refine ⟨155801289112939003637923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3323760834409365410942357 155801289112939003637923)
                ·
                  rfl

theorem cell20_1024049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 6].length) (baseStart_1024049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024049 prefixEnd_1024049 := by exact prefixLift 1024049
  have htrace : WordTrace (prefixWord ++ tailWord_1024049) baseStart_1024049 baseEnd_1024049 := by
    simpa [prefixWord, tailWord_1024049, baseEnd_1024049] using wordTrace_append hprefix tailTrace_1024049
  have hstable : (prefixWord ++ tailWord_1024049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024049).length < 2 ^ (prefixWord ++ tailWord_1024049).sum := by decide
  have hdescent : baseEnd_1024049 < baseStart_1024049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024063 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 6]
def baseStart_1024063 : Nat := 118140960795 + 1024063 * 2 ^ 59
def prefixEnd_1024063 : Nat := 4983230072969 + 3 ^ 40 * 1024063 * 2
def baseEnd_1024063 : Nat := 467410257320295184447045

theorem tailTrace_1024063 : CollatzResearch.WordTrace tailWord_1024063 prefixEnd_1024063 467410257320295184447045 := by
  unfold tailWord_1024063
  simp only [CollatzResearch.WordTrace]
  refine ⟨37350646089002121881324843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24900430726001414587549895 37350646089002121881324843)
  ·
    refine ⟨56025969133503182821987265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37350646089002121881324843 56025969133503182821987265)
    ·
      refine ⟨42019476850127387116490449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56025969133503182821987265 42019476850127387116490449)
      ·
        refine ⟨31514607637595540337367837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42019476850127387116490449 31514607637595540337367837)
        ·
          refine ⟨11817977864098327626512939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31514607637595540337367837 11817977864098327626512939)
          ·
            refine ⟨17726966796147491439769409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11817977864098327626512939 17726966796147491439769409)
            ·
              refine ⟨13295225097110618579827057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17726966796147491439769409 13295225097110618579827057)
              ·
                refine ⟨9971418822832963934870293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13295225097110618579827057 9971418822832963934870293)
                ·
                  refine ⟨467410257320295184447045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9971418822832963934870293 467410257320295184447045)
                  ·
                    rfl

theorem cell20_1024063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_1024063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024063 prefixEnd_1024063 := by exact prefixLift 1024063
  have htrace : WordTrace (prefixWord ++ tailWord_1024063) baseStart_1024063 baseEnd_1024063 := by
    simpa [prefixWord, tailWord_1024063, baseEnd_1024063] using wordTrace_append hprefix tailTrace_1024063
  have hstable : (prefixWord ++ tailWord_1024063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024063).length < 2 ^ (prefixWord ++ tailWord_1024063).sum := by decide
  have hdescent : baseEnd_1024063 < baseStart_1024063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024086 : List Nat := [5, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_1024086 : Nat := 118140960795 + 1024086 * 2 ^ 59
def prefixEnd_1024086 : Nat := 4983230072969 + 3 ^ 40 * 1024086 * 2
def baseEnd_1024086 : Nat := 467420755147009326680285

theorem tailTrace_1024086 : CollatzResearch.WordTrace tailWord_1024086 prefixEnd_1024086 467420755147009326680285 := by
  unfold tailWord_1024086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2334467810494924800588257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24900989978612531206274741 2334467810494924800588257)
  ·
    refine ⟨1750850857871193600441193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2334467810494924800588257 1750850857871193600441193)
    ·
      refine ⟨1313138143403395200330895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1750850857871193600441193 1313138143403395200330895)
      ·
        refine ⟨1969707215105092800496343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313138143403395200330895 1969707215105092800496343)
        ·
          refine ⟨2954560822657639200744515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969707215105092800496343 2954560822657639200744515)
          ·
            refine ⟨4431841233986458801116773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954560822657639200744515 4431841233986458801116773)
            ·
              refine ⟨830970231372461025209395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4431841233986458801116773 830970231372461025209395)
              ·
                refine ⟨1246455347058691537814093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830970231372461025209395 1246455347058691537814093)
                ·
                  refine ⟨467420755147009326680285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1246455347058691537814093 467420755147009326680285)
                  ·
                    rfl

theorem cell20_1024086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_1024086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024086 prefixEnd_1024086 := by exact prefixLift 1024086
  have htrace : WordTrace (prefixWord ++ tailWord_1024086) baseStart_1024086 baseEnd_1024086 := by
    simpa [prefixWord, tailWord_1024086, baseEnd_1024086] using wordTrace_append hprefix tailTrace_1024086
  have hstable : (prefixWord ++ tailWord_1024086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024086).length < 2 ^ (prefixWord ++ tailWord_1024086).sum := by decide
  have hdescent : baseEnd_1024086 < baseStart_1024086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024156 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 4]
def baseStart_1024156 : Nat := 118140960795 + 1024156 * 2 ^ 59
def prefixEnd_1024156 : Nat := 4983230072969 + 3 ^ 40 * 1024156 * 2
def baseEnd_1024156 : Nat := 467452705054400194346665

theorem tailTrace_1024156 : CollatzResearch.WordTrace tailWord_1024156 prefixEnd_1024156 467452705054400194346665 := by
  unfold tailWord_1024156
  simp only [CollatzResearch.WordTrace]
  refine ⟨18677019038832599382230161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24902692051776799176306881 18677019038832599382230161)
  ·
    refine ⟨14007764279124449536672621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18677019038832599382230161 14007764279124449536672621)
    ·
      refine ⟨5252911604671668576252233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14007764279124449536672621 5252911604671668576252233)
      ·
        refine ⟨3939683703503751432189175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5252911604671668576252233 3939683703503751432189175)
        ·
          refine ⟨5909525555255627148283763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3939683703503751432189175 5909525555255627148283763)
          ·
            refine ⟨8864288332883440722425645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5909525555255627148283763 8864288332883440722425645)
            ·
              refine ⟨3324108124831290270909617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8864288332883440722425645 3324108124831290270909617)
              ·
                refine ⟨2493081093623467703182213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3324108124831290270909617 2493081093623467703182213)
                ·
                  refine ⟨467452705054400194346665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2493081093623467703182213 467452705054400194346665)
                  ·
                    rfl

theorem cell20_1024156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_1024156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024156 prefixEnd_1024156 := by exact prefixLift 1024156
  have htrace : WordTrace (prefixWord ++ tailWord_1024156) baseStart_1024156 baseEnd_1024156 := by
    simpa [prefixWord, tailWord_1024156, baseEnd_1024156] using wordTrace_append hprefix tailTrace_1024156
  have hstable : (prefixWord ++ tailWord_1024156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024156).length < 2 ^ (prefixWord ++ tailWord_1024156).sum := by decide
  have hdescent : baseEnd_1024156 < baseStart_1024156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024184 : List Nat := [2, 1, 2, 1, 2, 1, 11]
def baseStart_1024184 : Nat := 118140960795 + 1024184 * 2 ^ 59
def prefixEnd_1024184 : Nat := 4983230072969 + 3 ^ 40 * 1024184 * 2
def baseEnd_1024184 : Nat := 51940609446372949045913

theorem tailTrace_1024184 : CollatzResearch.WordTrace tailWord_1024184 prefixEnd_1024184 51940609446372949045913 := by
  unfold tailWord_1024184
  simp only [CollatzResearch.WordTrace]
  refine ⟨18677529660781879773239803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24903372881042506364319737 18677529660781879773239803)
  ·
    refine ⟨28016294491172819659859705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18677529660781879773239803 28016294491172819659859705)
    ·
      refine ⟨21012220868379614744894779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28016294491172819659859705 21012220868379614744894779)
      ·
        refine ⟨31518331302569422117342169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21012220868379614744894779 31518331302569422117342169)
        ·
          refine ⟨23638748476927066588006627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31518331302569422117342169 23638748476927066588006627)
          ·
            refine ⟨35458122715390599882009941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23638748476927066588006627 35458122715390599882009941)
            ·
              refine ⟨51940609446372949045913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35458122715390599882009941 51940609446372949045913)
              ·
                rfl

theorem cell20_1024184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 11].length) (baseStart_1024184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024184 prefixEnd_1024184 := by exact prefixLift 1024184
  have htrace : WordTrace (prefixWord ++ tailWord_1024184) baseStart_1024184 baseEnd_1024184 := by
    simpa [prefixWord, tailWord_1024184, baseEnd_1024184] using wordTrace_append hprefix tailTrace_1024184
  have hstable : (prefixWord ++ tailWord_1024184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024184).length < 2 ^ (prefixWord ++ tailWord_1024184).sum := by decide
  have hdescent : baseEnd_1024184 < baseStart_1024184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024214 : List Nat := [5, 2, 1, 2, 1, 3, 2, 4]
def baseStart_1024214 : Nat := 118140960795 + 1024214 * 2 ^ 59
def prefixEnd_1024214 : Nat := 4983230072969 + 3 ^ 40 * 1024214 * 2
def baseEnd_1024214 : Nat := 155826392611603256804365

theorem tailTrace_1024214 : CollatzResearch.WordTrace tailWord_1024214 prefixEnd_1024214 155826392611603256804365 := by
  unfold tailWord_1024214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2334759594465942166879481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24904102340970049780047797 2334759594465942166879481)
  ·
    refine ⟨1751069695849456625159611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2334759594465942166879481 1751069695849456625159611)
    ·
      refine ⟨2626604543774184937739417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1751069695849456625159611 2626604543774184937739417)
      ·
        refine ⟨1969953407830638703304563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2626604543774184937739417 1969953407830638703304563)
        ·
          refine ⟨2954930111745958054956845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969953407830638703304563 2954930111745958054956845)
          ·
            refine ⟨1108098791904734270608817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2954930111745958054956845 1108098791904734270608817)
            ·
              refine ⟨831074093928550702956613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108098791904734270608817 831074093928550702956613)
              ·
                refine ⟨155826392611603256804365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 831074093928550702956613 155826392611603256804365)
                ·
                  rfl

theorem cell20_1024214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_1024214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024214 prefixEnd_1024214 := by exact prefixLift 1024214
  have htrace : WordTrace (prefixWord ++ tailWord_1024214) baseStart_1024214 baseEnd_1024214 := by
    simpa [prefixWord, tailWord_1024214, baseEnd_1024214] using wordTrace_append hprefix tailTrace_1024214
  have hstable : (prefixWord ++ tailWord_1024214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024214).length < 2 ^ (prefixWord ++ tailWord_1024214).sum := by decide
  have hdescent : baseEnd_1024214 < baseStart_1024214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024239 : List Nat := [1, 1, 2, 1, 6, 3, 6]
def baseStart_1024239 : Nat := 118140960795 + 1024239 * 2 ^ 59
def prefixEnd_1024239 : Nat := 4983230072969 + 3 ^ 40 * 1024239 * 2
def baseEnd_1024239 : Nat := 51943398724002310508851

theorem tailTrace_1024239 : CollatzResearch.WordTrace tailWord_1024239 prefixEnd_1024239 51943398724002310508851 := by
  unfold tailWord_1024239
  simp only [CollatzResearch.WordTrace]
  refine ⟨37357065336364503939731771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24904710224243002626487847 37357065336364503939731771)
  ·
    refine ⟨56035598004546755909597657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37357065336364503939731771 56035598004546755909597657)
    ·
      refine ⟨42026698503410066932198243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56035598004546755909597657 42026698503410066932198243)
      ·
        refine ⟨63040047755115100398297365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42026698503410066932198243 63040047755115100398297365)
        ·
          refine ⟨2955002238521020331170189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63040047755115100398297365 2955002238521020331170189)
          ·
            refine ⟨1108125839445382624188821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2955002238521020331170189 1108125839445382624188821)
            ·
              refine ⟨51943398724002310508851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1108125839445382624188821 51943398724002310508851)
              ·
                rfl

theorem cell20_1024239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 6].length) (baseStart_1024239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024239 prefixEnd_1024239 := by exact prefixLift 1024239
  have htrace : WordTrace (prefixWord ++ tailWord_1024239) baseStart_1024239 baseEnd_1024239 := by
    simpa [prefixWord, tailWord_1024239, baseEnd_1024239] using wordTrace_append hprefix tailTrace_1024239
  have hstable : (prefixWord ++ tailWord_1024239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024239).length < 2 ^ (prefixWord ++ tailWord_1024239).sum := by decide
  have hdescent : baseEnd_1024239 < baseStart_1024239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024387 : List Nat := [1, 1, 1, 3, 7, 1, 2, 4]
def baseStart_1024387 : Nat := 118140960795 + 1024387 * 2 ^ 59
def prefixEnd_1024387 : Nat := 4983230072969 + 3 ^ 40 * 1024387 * 2
def baseEnd_1024387 : Nat := 155852713249596685881907

theorem tailTrace_1024387 : CollatzResearch.WordTrace tailWord_1024387 prefixEnd_1024387 155852713249596685881907 := by
  unfold tailWord_1024387
  simp only [CollatzResearch.WordTrace]
  refine ⟨37362463339828325216119415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24908308893218883477412943 37362463339828325216119415)
  ·
    refine ⟨56043695009742487824179123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37362463339828325216119415 56043695009742487824179123)
    ·
      refine ⟨84065542514613731736268685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56043695009742487824179123 84065542514613731736268685)
      ·
        refine ⟨31524578442980149401100757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84065542514613731736268685 31524578442980149401100757)
        ·
          refine ⟨738857307257347251588299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 31524578442980149401100757 738857307257347251588299)
          ·
            refine ⟨1108285960886020877382449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738857307257347251588299 1108285960886020877382449)
            ·
              refine ⟨831214470664515658036837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108285960886020877382449 831214470664515658036837)
              ·
                refine ⟨155852713249596685881907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 831214470664515658036837 155852713249596685881907)
                ·
                  rfl

theorem cell20_1024387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 4].length) (baseStart_1024387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024387 prefixEnd_1024387 := by exact prefixLift 1024387
  have htrace : WordTrace (prefixWord ++ tailWord_1024387) baseStart_1024387 baseEnd_1024387 := by
    simpa [prefixWord, tailWord_1024387, baseEnd_1024387] using wordTrace_append hprefix tailTrace_1024387
  have hstable : (prefixWord ++ tailWord_1024387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024387).length < 2 ^ (prefixWord ++ tailWord_1024387).sum := by decide
  have hdescent : baseEnd_1024387 < baseStart_1024387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024418 : List Nat := [3, 3, 1, 2, 1, 1, 5, 2, 2]
def baseStart_1024418 : Nat := 118140960795 + 1024418 * 2 ^ 59
def prefixEnd_1024418 : Nat := 4983230072969 + 3 ^ 40 * 1024418 * 2
def baseEnd_1024418 : Nat := 467572288993491727612261

theorem tailTrace_1024418 : CollatzResearch.WordTrace tailWord_1024418 prefixEnd_1024418 467572288993491727612261 := by
  unfold tailWord_1024418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9340898500679004377624477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24909062668477345006998605 9340898500679004377624477)
  ·
    refine ⟨3502836937754626641609179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9340898500679004377624477 3502836937754626641609179)
    ·
      refine ⟨5254255406631939962413769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3502836937754626641609179 5254255406631939962413769)
      ·
        refine ⟨3940691554973954971810327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5254255406631939962413769 3940691554973954971810327)
        ·
          refine ⟨5911037332460932457715491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3940691554973954971810327 5911037332460932457715491)
          ·
            refine ⟨8866555998691398686573237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911037332460932457715491 8866555998691398686573237)
            ·
              refine ⟨831239624877318626866241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8866555998691398686573237 831239624877318626866241)
              ·
                refine ⟨623429718657988970149681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831239624877318626866241 623429718657988970149681)
                ·
                  refine ⟨467572288993491727612261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623429718657988970149681 467572288993491727612261)
                  ·
                    rfl

theorem cell20_1024418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_1024418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024418 prefixEnd_1024418 := by exact prefixLift 1024418
  have htrace : WordTrace (prefixWord ++ tailWord_1024418) baseStart_1024418 baseEnd_1024418 := by
    simpa [prefixWord, tailWord_1024418, baseEnd_1024418] using wordTrace_append hprefix tailTrace_1024418
  have hstable : (prefixWord ++ tailWord_1024418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024418).length < 2 ^ (prefixWord ++ tailWord_1024418).sum := by decide
  have hdescent : baseEnd_1024418 < baseStart_1024418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024457 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 7]
def baseStart_1024457 : Nat := 118140960795 + 1024457 * 2 ^ 59
def prefixEnd_1024457 : Nat := 4983230072969 + 3 ^ 40 * 1024457 * 2
def baseEnd_1024457 : Nat := 467590089656180925312101

theorem tailTrace_1024457 : CollatzResearch.WordTrace tailWord_1024457 prefixEnd_1024457 467590089656180925312101 := by
  unfold tailWord_1024457
  simp only [CollatzResearch.WordTrace]
  refine ⟨37365016449574727171167625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24910010966383151447445083 37365016449574727171167625)
  ·
    refine ⟨28023762337181045378375719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37365016449574727171167625 28023762337181045378375719)
    ·
      refine ⟨42035643505771568067563579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28023762337181045378375719 42035643505771568067563579)
      ·
        refine ⟨63053465258657352101345369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42035643505771568067563579 63053465258657352101345369)
        ·
          refine ⟨47290098943993014076009027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63053465258657352101345369 47290098943993014076009027)
          ·
            refine ⟨70935148415989521114013541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47290098943993014076009027 70935148415989521114013541)
            ·
              refine ⟨13300340327998035208877539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70935148415989521114013541 13300340327998035208877539)
              ·
                refine ⟨19950510491997052813316309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13300340327998035208877539 19950510491997052813316309)
                ·
                  refine ⟨467590089656180925312101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19950510491997052813316309 467590089656180925312101)
                  ·
                    rfl

theorem cell20_1024457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_1024457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024457 prefixEnd_1024457 := by exact prefixLift 1024457
  have htrace : WordTrace (prefixWord ++ tailWord_1024457) baseStart_1024457 baseEnd_1024457 := by
    simpa [prefixWord, tailWord_1024457, baseEnd_1024457] using wordTrace_append hprefix tailTrace_1024457
  have hstable : (prefixWord ++ tailWord_1024457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024457).length < 2 ^ (prefixWord ++ tailWord_1024457).sum := by decide
  have hdescent : baseEnd_1024457 < baseStart_1024457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024470 : List Nat := [5, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1024470 : Nat := 118140960795 + 1024470 * 2 ^ 59
def prefixEnd_1024470 : Nat := 4983230072969 + 3 ^ 40 * 1024470 * 2
def baseEnd_1024470 : Nat := 467596023210410657878715

theorem tailTrace_1024470 : CollatzResearch.WordTrace tailWord_1024470 prefixEnd_1024470 467596023210410657878715 := by
  unfold tailWord_1024470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2335343162407976899461929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24910327065685086927593909 2335343162407976899461929)
  ·
    refine ⟨1751507371805982674596447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2335343162407976899461929 1751507371805982674596447)
    ·
      refine ⟨2627261057708974011894671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1751507371805982674596447 2627261057708974011894671)
      ·
        refine ⟨3940891586563461017842007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2627261057708974011894671 3940891586563461017842007)
        ·
          refine ⟨5911337379845191526763011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3940891586563461017842007 5911337379845191526763011)
          ·
            refine ⟨8867006069767787290144517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911337379845191526763011 8867006069767787290144517)
            ·
              refine ⟨1662563638081460116902097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8867006069767787290144517 1662563638081460116902097)
              ·
                refine ⟨1246922728561095087676573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1662563638081460116902097 1246922728561095087676573)
                ·
                  refine ⟨467596023210410657878715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1246922728561095087676573 467596023210410657878715)
                  ·
                    rfl

theorem cell20_1024470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1024470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024470 prefixEnd_1024470 := by exact prefixLift 1024470
  have htrace : WordTrace (prefixWord ++ tailWord_1024470) baseStart_1024470 baseEnd_1024470 := by
    simpa [prefixWord, tailWord_1024470, baseEnd_1024470] using wordTrace_append hprefix tailTrace_1024470
  have hstable : (prefixWord ++ tailWord_1024470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024470).length < 2 ^ (prefixWord ++ tailWord_1024470).sum := by decide
  have hdescent : baseEnd_1024470 < baseStart_1024470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024477 : List Nat := [1, 4, 3, 1, 1, 1, 3, 4, 2]
def baseStart_1024477 : Nat := 118140960795 + 1024477 * 2 ^ 59
def prefixEnd_1024477 : Nat := 4983230072969 + 3 ^ 40 * 1024477 * 2
def baseEnd_1024477 : Nat := 467599218201149744645353

theorem tailTrace_1024477 : CollatzResearch.WordTrace tailWord_1024477 prefixEnd_1024477 467599218201149744645353 := by
  unfold tailWord_1024477
  simp only [CollatzResearch.WordTrace]
  refine ⟨37365745909502270586895685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24910497273001513724597123 37365745909502270586895685)
  ·
    refine ⟨7006077358031675735042941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37365745909502270586895685 7006077358031675735042941)
    ·
      refine ⟨2627279009261878400641103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7006077358031675735042941 2627279009261878400641103)
      ·
        refine ⟨3940918513892817600961655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2627279009261878400641103 3940918513892817600961655)
        ·
          refine ⟨5911377770839226401442483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3940918513892817600961655 5911377770839226401442483)
          ·
            refine ⟨8867066656258839602163725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911377770839226401442483 8867066656258839602163725)
            ·
              refine ⟨3325149996097064850811397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8867066656258839602163725 3325149996097064850811397)
              ·
                refine ⟨623465624268199659527137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3325149996097064850811397 623465624268199659527137)
                ·
                  refine ⟨467599218201149744645353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623465624268199659527137 467599218201149744645353)
                  ·
                    rfl

theorem cell20_1024477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_1024477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024477 prefixEnd_1024477 := by exact prefixLift 1024477
  have htrace : WordTrace (prefixWord ++ tailWord_1024477) baseStart_1024477 baseEnd_1024477 := by
    simpa [prefixWord, tailWord_1024477, baseEnd_1024477] using wordTrace_append hprefix tailTrace_1024477
  have hstable : (prefixWord ++ tailWord_1024477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024477).length < 2 ^ (prefixWord ++ tailWord_1024477).sum := by decide
  have hdescent : baseEnd_1024477 < baseStart_1024477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024481 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 4]
def baseStart_1024481 : Nat := 118140960795 + 1024481 * 2 ^ 59
def prefixEnd_1024481 : Nat := 4983230072969 + 3 ^ 40 * 1024481 * 2
def baseEnd_1024481 : Nat := 467601043910143508512003

theorem tailTrace_1024481 : CollatzResearch.WordTrace tailWord_1024481 prefixEnd_1024481 467601043910143508512003 := by
  unfold tailWord_1024481
  simp only [CollatzResearch.WordTrace]
  refine ⟨37365891801487779270041297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24910594534325186180027531 37365891801487779270041297)
  ·
    refine ⟨28024418851115834452530973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37365891801487779270041297 28024418851115834452530973)
    ·
      refine ⟨10509157069168437919699115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28024418851115834452530973 10509157069168437919699115)
      ·
        refine ⟨15763735603752656879548673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10509157069168437919699115 15763735603752656879548673)
        ·
          refine ⟨11822801702814492659661505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15763735603752656879548673 11822801702814492659661505)
          ·
            refine ⟨8867101277110869494746129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11822801702814492659661505 8867101277110869494746129)
            ·
              refine ⟨6650325957833152121059597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8867101277110869494746129 6650325957833152121059597)
              ·
                refine ⟨2493872234187432045397349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6650325957833152121059597 2493872234187432045397349)
                ·
                  refine ⟨467601043910143508512003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2493872234187432045397349 467601043910143508512003)
                  ·
                    rfl

theorem cell20_1024481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_1024481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024481 prefixEnd_1024481 := by exact prefixLift 1024481
  have htrace : WordTrace (prefixWord ++ tailWord_1024481) baseStart_1024481 baseEnd_1024481 := by
    simpa [prefixWord, tailWord_1024481, baseEnd_1024481] using wordTrace_append hprefix tailTrace_1024481
  have hstable : (prefixWord ++ tailWord_1024481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024481).length < 2 ^ (prefixWord ++ tailWord_1024481).sum := by decide
  have hdescent : baseEnd_1024481 < baseStart_1024481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024495 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 7]
def baseStart_1024495 : Nat := 118140960795 + 1024495 * 2 ^ 59
def prefixEnd_1024495 : Nat := 4983230072969 + 3 ^ 40 * 1024495 * 2
def baseEnd_1024495 : Nat := 467607433891621682045279

theorem tailTrace_1024495 : CollatzResearch.WordTrace tailWord_1024495 prefixEnd_1024495 467607433891621682045279 := by
  unfold tailWord_1024495
  simp only [CollatzResearch.WordTrace]
  refine ⟨37366402423437059661050939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24910934948958039774033959 37366402423437059661050939)
  ·
    refine ⟨56049603635155589491576409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37366402423437059661050939 56049603635155589491576409)
    ·
      refine ⟨42037202726366692118682307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56049603635155589491576409 42037202726366692118682307)
      ·
        refine ⟨63055804089550038178023461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42037202726366692118682307 63055804089550038178023461)
        ·
          refine ⟨11822963266790632158379399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63055804089550038178023461 11822963266790632158379399)
          ·
            refine ⟨17734444900185948237569099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11822963266790632158379399 17734444900185948237569099)
            ·
              refine ⟨26601667350278922356353649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17734444900185948237569099 26601667350278922356353649)
              ·
                refine ⟨19951250512709191767265237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26601667350278922356353649 19951250512709191767265237)
                ·
                  refine ⟨467607433891621682045279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19951250512709191767265237 467607433891621682045279)
                  ·
                    rfl

theorem cell20_1024495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_1024495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024495 prefixEnd_1024495 := by exact prefixLift 1024495
  have htrace : WordTrace (prefixWord ++ tailWord_1024495) baseStart_1024495 baseEnd_1024495 := by
    simpa [prefixWord, tailWord_1024495, baseEnd_1024495] using wordTrace_append hprefix tailTrace_1024495
  have hstable : (prefixWord ++ tailWord_1024495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024495).length < 2 ^ (prefixWord ++ tailWord_1024495).sum := by decide
  have hdescent : baseEnd_1024495 < baseStart_1024495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024501 : List Nat := [1, 3, 5, 1, 2, 1, 3, 4]
def baseStart_1024501 : Nat := 118140960795 + 1024501 * 2 ^ 59
def prefixEnd_1024501 : Nat := 4983230072969 + 3 ^ 40 * 1024501 * 2
def baseEnd_1024501 : Nat := 155870057485037442615085

theorem tailTrace_1024501 : CollatzResearch.WordTrace tailWord_1024501 prefixEnd_1024501 155870057485037442615085 := by
  unfold tailWord_1024501
  simp only [CollatzResearch.WordTrace]
  refine ⟨37366621261415322685769357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24911080840943548457179571 37366621261415322685769357)
  ·
    refine ⟨14012482973030746007163509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37366621261415322685769357 14012482973030746007163509)
    ·
      refine ⟨1313670278721632438171579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14012482973030746007163509 1313670278721632438171579)
      ·
        refine ⟨1970505418082448657257369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313670278721632438171579 1970505418082448657257369)
        ·
          refine ⟨1477879063561836492943027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1970505418082448657257369 1477879063561836492943027)
          ·
            refine ⟨2216818595342754739414541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477879063561836492943027 2216818595342754739414541)
            ·
              refine ⟨831306973253533027280453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2216818595342754739414541 831306973253533027280453)
              ·
                refine ⟨155870057485037442615085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 831306973253533027280453 155870057485037442615085)
                ·
                  rfl

theorem cell20_1024501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 4].length) (baseStart_1024501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024501 prefixEnd_1024501 := by exact prefixLift 1024501
  have htrace : WordTrace (prefixWord ++ tailWord_1024501) baseStart_1024501 baseEnd_1024501 := by
    simpa [prefixWord, tailWord_1024501, baseEnd_1024501] using wordTrace_append hprefix tailTrace_1024501
  have hstable : (prefixWord ++ tailWord_1024501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024501).length < 2 ^ (prefixWord ++ tailWord_1024501).sum := by decide
  have hdescent : baseEnd_1024501 < baseStart_1024501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024525 : List Nat := [1, 7, 1, 1, 1, 1, 3, 2, 3]
def baseStart_1024525 : Nat := 118140960795 + 1024525 * 2 ^ 59
def prefixEnd_1024525 : Nat := 4983230072969 + 3 ^ 40 * 1024525 * 2
def baseEnd_1024525 : Nat := 467621126709074911045157

theorem tailTrace_1024525 : CollatzResearch.WordTrace tailWord_1024525 prefixEnd_1024525 467621126709074911045157 := by
  unfold tailWord_1024525
  simp only [CollatzResearch.WordTrace]
  refine ⟨37367496613328374784643029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24911664408885583189762019 37367496613328374784643029)
  ·
    refine ⟨875800701874883784015071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 37367496613328374784643029 875800701874883784015071)
    ·
      refine ⟨1313701052812325676022607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 875800701874883784015071 1313701052812325676022607)
      ·
        refine ⟨1970551579218488514033911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313701052812325676022607 1970551579218488514033911)
        ·
          refine ⟨2955827368827732771050867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1970551579218488514033911 2955827368827732771050867)
          ·
            refine ⟨4433741053241599156576301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2955827368827732771050867 4433741053241599156576301)
            ·
              refine ⟨1662652894965599683716113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4433741053241599156576301 1662652894965599683716113)
              ·
                refine ⟨1246989671224199762787085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1662652894965599683716113 1246989671224199762787085)
                ·
                  refine ⟨467621126709074911045157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1246989671224199762787085 467621126709074911045157)
                  ·
                    rfl

theorem cell20_1024525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_1024525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024525 prefixEnd_1024525 := by exact prefixLift 1024525
  have htrace : WordTrace (prefixWord ++ tailWord_1024525) baseStart_1024525 baseEnd_1024525 := by
    simpa [prefixWord, tailWord_1024525, baseEnd_1024525] using wordTrace_append hprefix tailTrace_1024525
  have hstable : (prefixWord ++ tailWord_1024525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024525).length < 2 ^ (prefixWord ++ tailWord_1024525).sum := by decide
  have hdescent : baseEnd_1024525 < baseStart_1024525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024532 : List Nat := [2, 4, 3, 1, 1, 1, 2, 4, 2]
def baseStart_1024532 : Nat := 118140960795 + 1024532 * 2 ^ 59
def prefixEnd_1024532 : Nat := 4983230072969 + 3 ^ 40 * 1024532 * 2
def baseEnd_1024532 : Nat := 467624321699813997811795

theorem tailTrace_1024532 : CollatzResearch.WordTrace tailWord_1024532 prefixEnd_1024532 467624321699813997811795 := by
  unfold tailWord_1024532
  simp only [CollatzResearch.WordTrace]
  refine ⟨18683875962151507490073925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24911834616202009986765233 18683875962151507490073925)
  ·
    refine ⟨3503226742903407654388861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18683875962151507490073925 3503226742903407654388861)
    ·
      refine ⟨1313710028588777870395823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3503226742903407654388861 1313710028588777870395823)
      ·
        refine ⟨1970565042883166805593735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313710028588777870395823 1970565042883166805593735)
        ·
          refine ⟨2955847564324750208390603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1970565042883166805593735 2955847564324750208390603)
          ·
            refine ⟨4433771346487125312585905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2955847564324750208390603 4433771346487125312585905)
            ·
              refine ⟨3325328509865343984439429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4433771346487125312585905 3325328509865343984439429)
              ·
                refine ⟨623499095599751997082393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3325328509865343984439429 623499095599751997082393)
                ·
                  refine ⟨467624321699813997811795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623499095599751997082393 467624321699813997811795)
                  ·
                    rfl

theorem cell20_1024532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_1024532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024532 prefixEnd_1024532 := by exact prefixLift 1024532
  have htrace : WordTrace (prefixWord ++ tailWord_1024532) baseStart_1024532 baseEnd_1024532 := by
    simpa [prefixWord, tailWord_1024532, baseEnd_1024532] using wordTrace_append hprefix tailTrace_1024532
  have hstable : (prefixWord ++ tailWord_1024532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024532).length < 2 ^ (prefixWord ++ tailWord_1024532).sum := by decide
  have hdescent : baseEnd_1024532 < baseStart_1024532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024536 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 4]
def baseStart_1024536 : Nat := 118140960795 + 1024536 * 2 ^ 59
def prefixEnd_1024536 : Nat := 4983230072969 + 3 ^ 40 * 1024536 * 2
def baseEnd_1024536 : Nat := 467626147408807761678445

theorem tailTrace_1024536 : CollatzResearch.WordTrace tailWord_1024536 prefixEnd_1024536 467626147408807761678445 := by
  unfold tailWord_1024536
  simp only [CollatzResearch.WordTrace]
  refine ⟨18683948908144261831646731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24911931877525682442195641 18683948908144261831646731)
  ·
    refine ⟨28025923362216392747470097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18683948908144261831646731 28025923362216392747470097)
    ·
      refine ⟨21019442521662294560602573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28025923362216392747470097 21019442521662294560602573)
      ·
        refine ⟨7882290945623360460225965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21019442521662294560602573 7882290945623360460225965)
        ·
          refine ⟨2955859104608760172584737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7882290945623360460225965 2955859104608760172584737)
          ·
            refine ⟨2216894328456570129438553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2955859104608760172584737 2216894328456570129438553)
            ·
              refine ⟨1662670746342427597078915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2216894328456570129438553 1662670746342427597078915)
              ·
                refine ⟨2494006119513641395618373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662670746342427597078915 2494006119513641395618373)
                ·
                  refine ⟨467626147408807761678445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2494006119513641395618373 467626147408807761678445)
                  ·
                    rfl

theorem cell20_1024536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_1024536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024536 prefixEnd_1024536 := by exact prefixLift 1024536
  have htrace : WordTrace (prefixWord ++ tailWord_1024536) baseStart_1024536 baseEnd_1024536 := by
    simpa [prefixWord, tailWord_1024536, baseEnd_1024536] using wordTrace_append hprefix tailTrace_1024536
  have hstable : (prefixWord ++ tailWord_1024536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024536).length < 2 ^ (prefixWord ++ tailWord_1024536).sum := by decide
  have hdescent : baseEnd_1024536 < baseStart_1024536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024588 : List Nat := [2, 2, 1, 3, 1, 2, 2, 4, 3]
def baseStart_1024588 : Nat := 118140960795 + 1024588 * 2 ^ 59
def prefixEnd_1024588 : Nat := 4983230072969 + 3 ^ 40 * 1024588 * 2
def baseEnd_1024588 : Nat := 467649881625726691944899

theorem tailTrace_1024588 : CollatzResearch.WordTrace tailWord_1024588 prefixEnd_1024588 467649881625726691944899 := by
  unfold tailWord_1024588
  simp only [CollatzResearch.WordTrace]
  refine ⟨18684897206050068272093209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24913196274733424362790945 18684897206050068272093209)
  ·
    refine ⟨14013672904537551204069907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18684897206050068272093209 14013672904537551204069907)
    ·
      refine ⟨21020509356806326806104861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14013672904537551204069907 21020509356806326806104861)
      ·
        refine ⟨7882691008802372552289323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21020509356806326806104861 7882691008802372552289323)
        ·
          refine ⟨11824036513203558828433985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7882691008802372552289323 11824036513203558828433985)
          ·
            refine ⟨8868027384902669121325489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11824036513203558828433985 8868027384902669121325489)
            ·
              refine ⟨6651020538677001840994117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8868027384902669121325489 6651020538677001840994117)
              ·
                refine ⟨1247066351001937845186397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6651020538677001840994117 1247066351001937845186397)
                ·
                  refine ⟨467649881625726691944899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247066351001937845186397 467649881625726691944899)
                  ·
                    rfl

theorem cell20_1024588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_1024588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024588 prefixEnd_1024588 := by exact prefixLift 1024588
  have htrace : WordTrace (prefixWord ++ tailWord_1024588) baseStart_1024588 baseEnd_1024588 := by
    simpa [prefixWord, tailWord_1024588, baseEnd_1024588] using wordTrace_append hprefix tailTrace_1024588
  have hstable : (prefixWord ++ tailWord_1024588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024588).length < 2 ^ (prefixWord ++ tailWord_1024588).sum := by decide
  have hdescent : baseEnd_1024588 < baseStart_1024588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024642 : List Nat := [3, 4, 3, 1, 1, 1, 1, 4, 2]
def baseStart_1024642 : Nat := 118140960795 + 1024642 * 2 ^ 59
def prefixEnd_1024642 : Nat := 4983230072969 + 3 ^ 40 * 1024642 * 2
def baseEnd_1024642 : Nat := 467674528697142504144679

theorem tailTrace_1024642 : CollatzResearch.WordTrace tailWord_1024642 prefixEnd_1024642 467674528697142504144679 := by
  unfold tailWord_1024642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9342940988476125941663045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24914509302603002511101453 9342940988476125941663045)
  ·
    refine ⟨1751801435339273614061821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9342940988476125941663045 1751801435339273614061821)
    ·
      refine ⟨656925538252227605273183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1751801435339273614061821 656925538252227605273183)
      ·
        refine ⟨985388307378341407909775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656925538252227605273183 985388307378341407909775)
        ·
          refine ⟨1478082461067512111864663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985388307378341407909775 1478082461067512111864663)
          ·
            refine ⟨2217123691601268167796995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478082461067512111864663 2217123691601268167796995)
            ·
              refine ⟨3325685537401902251695493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217123691601268167796995 3325685537401902251695493)
              ·
                refine ⟨623566038262856672192905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3325685537401902251695493 623566038262856672192905)
                ·
                  refine ⟨467674528697142504144679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623566038262856672192905 467674528697142504144679)
                  ·
                    rfl

theorem cell20_1024642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_1024642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024642 prefixEnd_1024642 := by exact prefixLift 1024642
  have htrace : WordTrace (prefixWord ++ tailWord_1024642) baseStart_1024642 baseEnd_1024642 := by
    simpa [prefixWord, tailWord_1024642, baseEnd_1024642] using wordTrace_append hprefix tailTrace_1024642
  have hstable : (prefixWord ++ tailWord_1024642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024642).length < 2 ^ (prefixWord ++ tailWord_1024642).sum := by decide
  have hdescent : baseEnd_1024642 < baseStart_1024642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024664 : List Nat := [2, 1, 2, 4, 1, 1, 1, 5, 3]
def baseStart_1024664 : Nat := 118140960795 + 1024664 * 2 ^ 59
def prefixEnd_1024664 : Nat := 4983230072969 + 3 ^ 40 * 1024664 * 2
def baseEnd_1024664 : Nat := 467684570096608205411255

theorem tailTrace_1024664 : CollatzResearch.WordTrace tailWord_1024664 prefixEnd_1024664 467684570096608205411255 := by
  unfold tailWord_1024664
  simp only [CollatzResearch.WordTrace]
  refine ⟨18686283179912400761976523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24915044239883201015968697 18686283179912400761976523)
  ·
    refine ⟨28029424769868601142964785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18686283179912400761976523 28029424769868601142964785)
    ·
      refine ⟨21022068577401450857223589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28029424769868601142964785 21022068577401450857223589)
      ·
        refine ⟨3941637858262772035729423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21022068577401450857223589 3941637858262772035729423)
        ·
          refine ⟨5912456787394158053594135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3941637858262772035729423 5912456787394158053594135)
          ·
            refine ⟨8868685181091237080391203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5912456787394158053594135 8868685181091237080391203)
            ·
              refine ⟨13303027771636855620586805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8868685181091237080391203 13303027771636855620586805)
              ·
                refine ⟨1247158853590955214430013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13303027771636855620586805 1247158853590955214430013)
                ·
                  refine ⟨467684570096608205411255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247158853590955214430013 467684570096608205411255)
                  ·
                    rfl

theorem cell20_1024664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_1024664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024664 prefixEnd_1024664 := by exact prefixLift 1024664
  have htrace : WordTrace (prefixWord ++ tailWord_1024664) baseStart_1024664 baseEnd_1024664 := by
    simpa [prefixWord, tailWord_1024664, baseEnd_1024664] using wordTrace_append hprefix tailTrace_1024664
  have hstable : (prefixWord ++ tailWord_1024664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024664).length < 2 ^ (prefixWord ++ tailWord_1024664).sum := by decide
  have hdescent : baseEnd_1024664 < baseStart_1024664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024694 : List Nat := [5, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_1024694 : Nat := 118140960795 + 1024694 * 2 ^ 59
def prefixEnd_1024694 : Nat := 4983230072969 + 3 ^ 40 * 1024694 * 2
def baseEnd_1024694 : Nat := 467698262914061434411133

theorem tailTrace_1024694 : CollatzResearch.WordTrace tailWord_1024694 prefixEnd_1024694 467698262914061434411133 := by
  unfold tailWord_1024694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2335853784357257290471571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24915773699810744431696757 2335853784357257290471571)
  ·
    refine ⟨3503780676535885935707357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2335853784357257290471571 3503780676535885935707357)
    ·
      refine ⟨1313917753700957225890259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3503780676535885935707357 1313917753700957225890259)
      ·
        refine ⟨1970876630551435838835389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313917753700957225890259 1970876630551435838835389)
        ·
          refine ⟨739078736456788439563271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1970876630551435838835389 739078736456788439563271)
          ·
            refine ⟨1108618104685182659344907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739078736456788439563271 1108618104685182659344907)
            ·
              refine ⟨1662927157027773989017361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108618104685182659344907 1662927157027773989017361)
              ·
                refine ⟨1247195367770830491763021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1662927157027773989017361 1247195367770830491763021)
                ·
                  refine ⟨467698262914061434411133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247195367770830491763021 467698262914061434411133)
                  ·
                    rfl

theorem cell20_1024694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_1024694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024694 prefixEnd_1024694 := by exact prefixLift 1024694
  have htrace : WordTrace (prefixWord ++ tailWord_1024694) baseStart_1024694 baseEnd_1024694 := by
    simpa [prefixWord, tailWord_1024694, baseEnd_1024694] using wordTrace_append hprefix tailTrace_1024694
  have hstable : (prefixWord ++ tailWord_1024694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024694).length < 2 ^ (prefixWord ++ tailWord_1024694).sum := by decide
  have hdescent : baseEnd_1024694 < baseStart_1024694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024702 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1024702 : Nat := 118140960795 + 1024702 * 2 ^ 59
def prefixEnd_1024702 : Nat := 4983230072969 + 3 ^ 40 * 1024702 * 2
def baseEnd_1024702 : Nat := 467701914332048962144433

theorem tailTrace_1024702 : CollatzResearch.WordTrace tailWord_1024702 prefixEnd_1024702 467701914332048962144433 := by
  unfold tailWord_1024702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4671744041710891751729545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24915968222458089342557573 4671744041710891751729545)
  ·
    refine ⟨3503808031283168813797159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4671744041710891751729545 3503808031283168813797159)
    ·
      refine ⟨5255712046924753220695739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3503808031283168813797159 5255712046924753220695739)
      ·
        refine ⟨7883568070387129831043609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5255712046924753220695739 7883568070387129831043609)
        ·
          refine ⟨5912676052790347373282707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7883568070387129831043609 5912676052790347373282707)
          ·
            refine ⟨8869014079185521059924061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5912676052790347373282707 8869014079185521059924061)
            ·
              refine ⟨3325880279694570397471523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8869014079185521059924061 3325880279694570397471523)
              ·
                refine ⟨4988820419541855596207285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3325880279694570397471523 4988820419541855596207285)
                ·
                  refine ⟨467701914332048962144433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4988820419541855596207285 467701914332048962144433)
                  ·
                    rfl

theorem cell20_1024702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1024702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024702 prefixEnd_1024702 := by exact prefixLift 1024702
  have htrace : WordTrace (prefixWord ++ tailWord_1024702) baseStart_1024702 baseEnd_1024702 := by
    simpa [prefixWord, tailWord_1024702, baseEnd_1024702] using wordTrace_append hprefix tailTrace_1024702
  have hstable : (prefixWord ++ tailWord_1024702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024702).length < 2 ^ (prefixWord ++ tailWord_1024702).sum := by decide
  have hdescent : baseEnd_1024702 < baseStart_1024702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024754 : List Nat := [3, 2, 1, 3, 1, 2, 8]
def baseStart_1024754 : Nat := 118140960795 + 1024754 * 2 ^ 59
def prefixEnd_1024754 : Nat := 4983230072969 + 3 ^ 40 * 1024754 * 2
def baseEnd_1024754 : Nat := 51969516505440876934543

theorem tailTrace_1024754 : CollatzResearch.WordTrace tailWord_1024754 prefixEnd_1024754 51969516505440876934543 := by
  unfold tailWord_1024754
  simp only [CollatzResearch.WordTrace]
  refine ⟨9343962232374686723682329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24917232619665831263152877 9343962232374686723682329)
  ·
    refine ⟨7007971674281015042761747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9343962232374686723682329 7007971674281015042761747)
    ·
      refine ⟨10511957511421522564142621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7007971674281015042761747 10511957511421522564142621)
      ·
        refine ⟨3941984066783070961553483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10511957511421522564142621 3941984066783070961553483)
        ·
          refine ⟨5912976100174606442330225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3941984066783070961553483 5912976100174606442330225)
          ·
            refine ⟨4434732075130954831747669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5912976100174606442330225 4434732075130954831747669)
            ·
              refine ⟨51969516505440876934543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4434732075130954831747669 51969516505440876934543)
              ·
                rfl

theorem cell20_1024754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 8].length) (baseStart_1024754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024754 prefixEnd_1024754 := by exact prefixLift 1024754
  have htrace : WordTrace (prefixWord ++ tailWord_1024754) baseStart_1024754 baseEnd_1024754 := by
    simpa [prefixWord, tailWord_1024754, baseEnd_1024754] using wordTrace_append hprefix tailTrace_1024754
  have hstable : (prefixWord ++ tailWord_1024754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024754).length < 2 ^ (prefixWord ++ tailWord_1024754).sum := by decide
  have hdescent : baseEnd_1024754 < baseStart_1024754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024756 : List Nat := [2, 6, 1, 1, 2, 1, 3, 2, 2]
def baseStart_1024756 : Nat := 118140960795 + 1024756 * 2 ^ 59
def prefixEnd_1024756 : Nat := 4983230072969 + 3 ^ 40 * 1024756 * 2
def baseEnd_1024756 : Nat := 467726561403464774344213

theorem tailTrace_1024756 : CollatzResearch.WordTrace tailWord_1024756 prefixEnd_1024756 467726561403464774344213 := by
  unfold tailWord_1024756
  simp only [CollatzResearch.WordTrace]
  refine ⟨18687960937745750618151061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24917281250327667490868081 18687960937745750618151061)
  ·
    refine ⟨875998168956832060225831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18687960937745750618151061 875998168956832060225831)
    ·
      refine ⟨1313997253435248090338747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 875998168956832060225831 1313997253435248090338747)
      ·
        refine ⟨1970995880152872135508121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313997253435248090338747 1970995880152872135508121)
        ·
          refine ⟨1478246910114654101631091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1970995880152872135508121 1478246910114654101631091)
          ·
            refine ⟨2217370365171981152446637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478246910114654101631091 2217370365171981152446637)
            ·
              refine ⟨831513886939492932167489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2217370365171981152446637 831513886939492932167489)
              ·
                refine ⟨623635415204619699125617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831513886939492932167489 623635415204619699125617)
                ·
                  refine ⟨467726561403464774344213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623635415204619699125617 467726561403464774344213)
                  ·
                    rfl

theorem cell20_1024756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_1024756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024756 prefixEnd_1024756 := by exact prefixLift 1024756
  have htrace : WordTrace (prefixWord ++ tailWord_1024756) baseStart_1024756 baseEnd_1024756 := by
    simpa [prefixWord, tailWord_1024756, baseEnd_1024756] using wordTrace_append hprefix tailTrace_1024756
  have hstable : (prefixWord ++ tailWord_1024756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024756).length < 2 ^ (prefixWord ++ tailWord_1024756).sum := by decide
  have hdescent : baseEnd_1024756 < baseStart_1024756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024764 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 4]
def baseStart_1024764 : Nat := 118140960795 + 1024764 * 2 ^ 59
def prefixEnd_1024764 : Nat := 4983230072969 + 3 ^ 40 * 1024764 * 2
def baseEnd_1024764 : Nat := 467730212821452302077513

theorem tailTrace_1024764 : CollatzResearch.WordTrace tailWord_1024764 prefixEnd_1024764 467730212821452302077513 := by
  unfold tailWord_1024764
  simp only [CollatzResearch.WordTrace]
  refine ⟨18688106829731259301296673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24917475772975012401728897 18688106829731259301296673)
  ·
    refine ⟨14016080122298444475972505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18688106829731259301296673 14016080122298444475972505)
    ·
      refine ⟨10512060091723833356979379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14016080122298444475972505 10512060091723833356979379)
      ·
        refine ⟨15768090137585750035469069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10512060091723833356979379 15768090137585750035469069)
        ·
          refine ⟨5913033801594656263300901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15768090137585750035469069 5913033801594656263300901)
          ·
            refine ⟨1108693837798998049368919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5913033801594656263300901 1108693837798998049368919)
            ·
              refine ⟨1663040756698497074053379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108693837798998049368919 1663040756698497074053379)
              ·
                refine ⟨2494561135047745611080069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663040756698497074053379 2494561135047745611080069)
                ·
                  refine ⟨467730212821452302077513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2494561135047745611080069 467730212821452302077513)
                  ·
                    rfl

theorem cell20_1024764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_1024764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024764 prefixEnd_1024764 := by exact prefixLift 1024764
  have htrace : WordTrace (prefixWord ++ tailWord_1024764) baseStart_1024764 baseEnd_1024764 := by
    simpa [prefixWord, tailWord_1024764, baseEnd_1024764] using wordTrace_append hprefix tailTrace_1024764
  have hstable : (prefixWord ++ tailWord_1024764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024764).length < 2 ^ (prefixWord ++ tailWord_1024764).sum := by decide
  have hdescent : baseEnd_1024764 < baseStart_1024764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024778 : List Nat := [3, 1, 2, 2, 1, 2, 3, 3, 3]
def baseStart_1024778 : Nat := 118140960795 + 1024778 * 2 ^ 59
def prefixEnd_1024778 : Nat := 4983230072969 + 3 ^ 40 * 1024778 * 2
def baseEnd_1024778 : Nat := 467736602802930475610789

theorem tailTrace_1024778 : CollatzResearch.WordTrace tailWord_1024778 prefixEnd_1024778 467736602802930475610789 := by
  unfold tailWord_1024778
  simp only [CollatzResearch.WordTrace]
  refine ⟨9344181070352949748400747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24917816187607865995735325 9344181070352949748400747)
  ·
    refine ⟨14016271605529424622601121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9344181070352949748400747 14016271605529424622601121)
    ·
      refine ⟨10512203704147068466950841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14016271605529424622601121 10512203704147068466950841)
      ·
        refine ⟨7884152778110301350213131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10512203704147068466950841 7884152778110301350213131)
        ·
          refine ⟨11826229167165452025319697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7884152778110301350213131 11826229167165452025319697)
          ·
            refine ⟨8869671875374089018989773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11826229167165452025319697 8869671875374089018989773)
            ·
              refine ⟨3326126953265283382121165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8869671875374089018989773 3326126953265283382121165)
              ·
                refine ⟨1247297607474481268295437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3326126953265283382121165 1247297607474481268295437)
                ·
                  refine ⟨467736602802930475610789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247297607474481268295437 467736602802930475610789)
                  ·
                    rfl

theorem cell20_1024778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_1024778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024778 prefixEnd_1024778 := by exact prefixLift 1024778
  have htrace : WordTrace (prefixWord ++ tailWord_1024778) baseStart_1024778 baseEnd_1024778 := by
    simpa [prefixWord, tailWord_1024778, baseEnd_1024778] using wordTrace_append hprefix tailTrace_1024778
  have hstable : (prefixWord ++ tailWord_1024778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024778).length < 2 ^ (prefixWord ++ tailWord_1024778).sum := by decide
  have hdescent : baseEnd_1024778 < baseStart_1024778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024819 : List Nat := [1, 1, 1, 2, 6, 1, 4, 2, 2]
def baseStart_1024819 : Nat := 118140960795 + 1024819 * 2 ^ 59
def prefixEnd_1024819 : Nat := 4983230072969 + 3 ^ 40 * 1024819 * 2
def baseEnd_1024819 : Nat := 467755316320116555243955

theorem tailTrace_1024819 : CollatzResearch.WordTrace tailWord_1024819 prefixEnd_1024819 467755316320116555243955 := by
  unfold tailWord_1024819
  simp only [CollatzResearch.WordTrace]
  refine ⟨37378219674263262995845511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24918813116175508663897007 37378219674263262995845511)
  ·
    refine ⟨56067329511394894493768267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37378219674263262995845511 56067329511394894493768267)
    ·
      refine ⟨84100994267092341740652401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56067329511394894493768267 84100994267092341740652401)
      ·
        refine ⟨63075745700319256305489301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84100994267092341740652401 63075745700319256305489301)
        ·
          refine ⟨2956675579702465139319811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63075745700319256305489301 2956675579702465139319811)
          ·
            refine ⟨4435013369553697708979717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956675579702465139319811 4435013369553697708979717)
            ·
              refine ⟨831565006791318320433697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4435013369553697708979717 831565006791318320433697)
              ·
                refine ⟨623673755093488740325273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831565006791318320433697 623673755093488740325273)
                ·
                  refine ⟨467755316320116555243955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623673755093488740325273 467755316320116555243955)
                  ·
                    rfl

theorem cell20_1024819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 2].length) (baseStart_1024819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024819 prefixEnd_1024819 := by exact prefixLift 1024819
  have htrace : WordTrace (prefixWord ++ tailWord_1024819) baseStart_1024819 baseEnd_1024819 := by
    simpa [prefixWord, tailWord_1024819, baseEnd_1024819] using wordTrace_append hprefix tailTrace_1024819
  have hstable : (prefixWord ++ tailWord_1024819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024819).length < 2 ^ (prefixWord ++ tailWord_1024819).sum := by decide
  have hdescent : baseEnd_1024819 < baseStart_1024819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024826 : List Nat := [3, 1, 1, 1, 7, 1, 1, 5]
def baseStart_1024826 : Nat := 118140960795 + 1024826 * 2 ^ 59
def prefixEnd_1024826 : Nat := 4983230072969 + 3 ^ 40 * 1024826 * 2
def baseEnd_1024826 : Nat := 155919503770285214003531

theorem tailTrace_1024826 : CollatzResearch.WordTrace tailWord_1024826 prefixEnd_1024826 155919503770285214003531 := by
  unfold tailWord_1024826
  simp only [CollatzResearch.WordTrace]
  refine ⟨9344618746309475797837583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24918983323491935460900221 9344618746309475797837583)
  ·
    refine ⟨14016928119464213696756375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9344618746309475797837583 14016928119464213696756375)
    ·
      refine ⟨21025392179196320545134563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14016928119464213696756375 21025392179196320545134563)
      ·
        refine ⟨31538088268794480817701845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21025392179196320545134563 31538088268794480817701845)
        ·
          refine ⟨739173943799870644164887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 31538088268794480817701845 739173943799870644164887)
          ·
            refine ⟨1108760915699805966247331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739173943799870644164887 1108760915699805966247331)
            ·
              refine ⟨1663141373549708949370997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108760915699805966247331 1663141373549708949370997)
              ·
                refine ⟨155919503770285214003531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1663141373549708949370997 155919503770285214003531)
                ·
                  rfl

theorem cell20_1024826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_1024826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024826 prefixEnd_1024826 := by exact prefixLift 1024826
  have htrace : WordTrace (prefixWord ++ tailWord_1024826) baseStart_1024826 baseEnd_1024826 := by
    simpa [prefixWord, tailWord_1024826, baseEnd_1024826] using wordTrace_append hprefix tailTrace_1024826
  have hstable : (prefixWord ++ tailWord_1024826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024826).length < 2 ^ (prefixWord ++ tailWord_1024826).sum := by decide
  have hdescent : baseEnd_1024826 < baseStart_1024826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024851 : List Nat := [1, 1, 1, 2, 1, 1, 3, 10]
def baseStart_1024851 : Nat := 118140960795 + 1024851 * 2 ^ 59
def prefixEnd_1024851 : Nat := 4983230072969 + 3 ^ 40 * 1024851 * 2
def baseEnd_1024851 : Nat := 155923307330688888725719

theorem tailTrace_1024851 : CollatzResearch.WordTrace tailWord_1024851 prefixEnd_1024851 155923307330688888725719 := by
  unfold tailWord_1024851
  simp only [CollatzResearch.WordTrace]
  refine ⟨37379386810147332461010407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24919591206764888307340271 37379386810147332461010407)
  ·
    refine ⟨56069080215220998691515611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37379386810147332461010407 56069080215220998691515611)
    ·
      refine ⟨84103620322831498037273417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56069080215220998691515611 84103620322831498037273417)
      ·
        refine ⟨63077715242123623527955063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84103620322831498037273417 63077715242123623527955063)
        ·
          refine ⟨94616572863185435291932595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63077715242123623527955063 94616572863185435291932595)
          ·
            refine ⟨141924859294778152937898893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94616572863185435291932595 141924859294778152937898893)
            ·
              refine ⟨53221822235541807351712085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141924859294778152937898893 53221822235541807351712085)
              ·
                refine ⟨155923307330688888725719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53221822235541807351712085 155923307330688888725719)
                ·
                  rfl

theorem cell20_1024851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 10].length) (baseStart_1024851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024851 prefixEnd_1024851 := by exact prefixLift 1024851
  have htrace : WordTrace (prefixWord ++ tailWord_1024851) baseStart_1024851 baseEnd_1024851 := by
    simpa [prefixWord, tailWord_1024851, baseEnd_1024851] using wordTrace_append hprefix tailTrace_1024851
  have hstable : (prefixWord ++ tailWord_1024851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024851).length < 2 ^ (prefixWord ++ tailWord_1024851).sum := by decide
  have hdescent : baseEnd_1024851 < baseStart_1024851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024868 : List Nat := [2, 3, 1, 1, 4, 2, 7]
def baseStart_1024868 : Nat := 118140960795 + 1024868 * 2 ^ 59
def prefixEnd_1024868 : Nat := 4983230072969 + 3 ^ 40 * 1024868 * 2
def baseEnd_1024868 : Nat := 51975297917254462512269

theorem tailTrace_1024868 : CollatzResearch.WordTrace tailWord_1024868 prefixEnd_1024868 51975297917254462512269 := by
  unfold tailWord_1024868
  simp only [CollatzResearch.WordTrace]
  refine ⟨18690003425542872182189629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24920004567390496242919505 18690003425542872182189629)
  ·
    refine ⟨7008751284578577068321111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18690003425542872182189629 7008751284578577068321111)
    ·
      refine ⟨10513126926867865602481667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7008751284578577068321111 10513126926867865602481667)
      ·
        refine ⟨15769690390301798403722501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10513126926867865602481667 15769690390301798403722501)
        ·
          refine ⟨2956816948181587200697969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15769690390301798403722501 2956816948181587200697969)
          ·
            refine ⟨2217612711136190400523477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2956816948181587200697969 2217612711136190400523477)
            ·
              refine ⟨51975297917254462512269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2217612711136190400523477 51975297917254462512269)
              ·
                rfl

theorem cell20_1024868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 7].length) (baseStart_1024868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024868 prefixEnd_1024868 := by exact prefixLift 1024868
  have htrace : WordTrace (prefixWord ++ tailWord_1024868) baseStart_1024868 baseEnd_1024868 := by
    simpa [prefixWord, tailWord_1024868, baseEnd_1024868] using wordTrace_append hprefix tailTrace_1024868
  have hstable : (prefixWord ++ tailWord_1024868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024868).length < 2 ^ (prefixWord ++ tailWord_1024868).sum := by decide
  have hdescent : baseEnd_1024868 < baseStart_1024868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024871 : List Nat := [1, 1, 5, 1, 2, 4, 1, 2, 3]
def baseStart_1024871 : Nat := 118140960795 + 1024871 * 2 ^ 59
def prefixEnd_1024871 : Nat := 4983230072969 + 3 ^ 40 * 1024871 * 2
def baseEnd_1024871 : Nat := 467779050537035485510409

theorem tailTrace_1024871 : CollatzResearch.WordTrace tailWord_1024871 prefixEnd_1024871 467779050537035485510409 := by
  unfold tailWord_1024871
  simp only [CollatzResearch.WordTrace]
  refine ⟨37380116270074875876738467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24920077513383250584492311 37380116270074875876738467)
  ·
    refine ⟨56070174405112313815107701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37380116270074875876738467 56070174405112313815107701)
    ·
      refine ⟨5256578850479279420166347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56070174405112313815107701 5256578850479279420166347)
      ·
        refine ⟨7884868275718919130249521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5256578850479279420166347 7884868275718919130249521)
        ·
          refine ⟨5913651206789189347687141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7884868275718919130249521 5913651206789189347687141)
          ·
            refine ⟨1108809601272973002691339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5913651206789189347687141 1108809601272973002691339)
            ·
              refine ⟨1663214401909459504037009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108809601272973002691339 1663214401909459504037009)
              ·
                refine ⟨1247410801432094628027757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1663214401909459504037009 1247410801432094628027757)
                ·
                  refine ⟨467779050537035485510409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247410801432094628027757 467779050537035485510409)
                  ·
                    rfl

theorem cell20_1024871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 3].length) (baseStart_1024871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024871 prefixEnd_1024871 := by exact prefixLift 1024871
  have htrace : WordTrace (prefixWord ++ tailWord_1024871) baseStart_1024871 baseEnd_1024871 := by
    simpa [prefixWord, tailWord_1024871, baseEnd_1024871] using wordTrace_append hprefix tailTrace_1024871
  have hstable : (prefixWord ++ tailWord_1024871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024871).length < 2 ^ (prefixWord ++ tailWord_1024871).sum := by decide
  have hdescent : baseEnd_1024871 < baseStart_1024871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024898 : List Nat := [3, 4, 2, 2, 1, 2, 2, 4]
def baseStart_1024898 : Nat := 118140960795 + 1024898 * 2 ^ 59
def prefixEnd_1024898 : Nat := 4983230072969 + 3 ^ 40 * 1024898 * 2
def baseEnd_1024898 : Nat := 155930458024247797203433

theorem tailTrace_1024898 : CollatzResearch.WordTrace tailWord_1024898 prefixEnd_1024898 155930458024247797203433 := by
  unfold tailWord_1024898
  simp only [CollatzResearch.WordTrace]
  refine ⟨9345275260244264871992837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24920734027318039658647565 9345275260244264871992837)
  ·
    refine ⟨1752239111295799663498657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9345275260244264871992837 1752239111295799663498657)
    ·
      refine ⟨1314179333471849747623993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1752239111295799663498657 1314179333471849747623993)
      ·
        refine ⟨985634500103887310717995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1314179333471849747623993 985634500103887310717995)
        ·
          refine ⟨1478451750155830966076993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985634500103887310717995 1478451750155830966076993)
          ·
            refine ⟨1108838812616873224557745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1478451750155830966076993 1108838812616873224557745)
            ·
              refine ⟨831629109462654918418309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108838812616873224557745 831629109462654918418309)
              ·
                refine ⟨155930458024247797203433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 831629109462654918418309 155930458024247797203433)
                ·
                  rfl

theorem cell20_1024898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_1024898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024898 prefixEnd_1024898 := by exact prefixLift 1024898
  have htrace : WordTrace (prefixWord ++ tailWord_1024898) baseStart_1024898 baseEnd_1024898 := by
    simpa [prefixWord, tailWord_1024898, baseEnd_1024898] using wordTrace_append hprefix tailTrace_1024898
  have hstable : (prefixWord ++ tailWord_1024898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024898).length < 2 ^ (prefixWord ++ tailWord_1024898).sum := by decide
  have hdescent : baseEnd_1024898 < baseStart_1024898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024930 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1024930 : Nat := 118140960795 + 1024930 * 2 ^ 59
def prefixEnd_1024930 : Nat := 4983230072969 + 3 ^ 40 * 1024930 * 2
def baseEnd_1024930 : Nat := 467805979744693502543501

theorem tailTrace_1024930 : CollatzResearch.WordTrace tailWord_1024930 prefixEnd_1024930 467805979744693502543501 := by
  unfold tailWord_1024930
  simp only [CollatzResearch.WordTrace]
  refine ⟨9345567044215282238284061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24921512117907419302090829 9345567044215282238284061)
  ·
    refine ⟨3504587641580730839356523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9345567044215282238284061 3504587641580730839356523)
    ·
      refine ⟨5256881462371096259034785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3504587641580730839356523 5256881462371096259034785)
      ·
        refine ⟨3942661096778322194276089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5256881462371096259034785 3942661096778322194276089)
        ·
          refine ⟨2956995822583741645707067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3942661096778322194276089 2956995822583741645707067)
          ·
            refine ⟨4435493733875612468560601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956995822583741645707067 4435493733875612468560601)
            ·
              refine ⟨3326620300406709351420451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4435493733875612468560601 3326620300406709351420451)
              ·
                refine ⟨4989930450610064027130677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3326620300406709351420451 4989930450610064027130677)
                ·
                  refine ⟨467805979744693502543501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4989930450610064027130677 467805979744693502543501)
                  ·
                    rfl

theorem cell20_1024930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1024930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024930 prefixEnd_1024930 := by exact prefixLift 1024930
  have htrace : WordTrace (prefixWord ++ tailWord_1024930) baseStart_1024930 baseEnd_1024930 := by
    simpa [prefixWord, tailWord_1024930, baseEnd_1024930] using wordTrace_append hprefix tailTrace_1024930
  have hstable : (prefixWord ++ tailWord_1024930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024930).length < 2 ^ (prefixWord ++ tailWord_1024930).sum := by decide
  have hdescent : baseEnd_1024930 < baseStart_1024930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1024999 : List Nat := [1, 1, 5, 2, 2, 3, 1, 5]
def baseStart_1024999 : Nat := 118140960795 + 1024999 * 2 ^ 59
def prefixEnd_1024999 : Nat := 4983230072969 + 3 ^ 40 * 1024999 * 2
def baseEnd_1024999 : Nat := 155945824408278643081073

theorem tailTrace_1024999 : CollatzResearch.WordTrace tailWord_1024999 prefixEnd_1024999 155945824408278643081073 := by
  unfold tailWord_1024999
  simp only [CollatzResearch.WordTrace]
  refine ⟨37384784813611153737398051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24923189875740769158265367 37384784813611153737398051)
  ·
    refine ⟨56077177220416730606097077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37384784813611153737398051 56077177220416730606097077)
    ·
      refine ⟨5257235364414068494321601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56077177220416730606097077 5257235364414068494321601)
      ·
        refine ⟨3942926523310551370741201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5257235364414068494321601 3942926523310551370741201)
        ·
          refine ⟨2957194892482913528055901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3942926523310551370741201 2957194892482913528055901)
          ·
            refine ⟨1108948084681092573020963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2957194892482913528055901 1108948084681092573020963)
            ·
              refine ⟨1663422127021638859531445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108948084681092573020963 1663422127021638859531445)
              ·
                refine ⟨155945824408278643081073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1663422127021638859531445 155945824408278643081073)
                ·
                  rfl

theorem cell20_1024999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 5].length) (baseStart_1024999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1024999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1024999 prefixEnd_1024999 := by exact prefixLift 1024999
  have htrace : WordTrace (prefixWord ++ tailWord_1024999) baseStart_1024999 baseEnd_1024999 := by
    simpa [prefixWord, tailWord_1024999, baseEnd_1024999] using wordTrace_append hprefix tailTrace_1024999
  have hstable : (prefixWord ++ tailWord_1024999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1024999).length < 2 ^ (prefixWord ++ tailWord_1024999).sum := by decide
  have hdescent : baseEnd_1024999 < baseStart_1024999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1024999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025072 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 4]
def baseStart_1025072 : Nat := 118140960795 + 1025072 * 2 ^ 59
def prefixEnd_1025072 : Nat := 4983230072969 + 3 ^ 40 * 1025072 * 2
def baseEnd_1025072 : Nat := 467870792413972119809587

theorem tailTrace_1025072 : CollatzResearch.WordTrace tailWord_1025072 prefixEnd_1025072 467870792413972119809587 := by
  unfold tailWord_1025072
  simp only [CollatzResearch.WordTrace]
  refine ⟨18693723671173343602402735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24924964894897791469870313 18693723671173343602402735)
  ·
    refine ⟨28040585506760015403604103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18693723671173343602402735 28040585506760015403604103)
    ·
      refine ⟨42060878260140023105406155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28040585506760015403604103 42060878260140023105406155)
      ·
        refine ⟨63091317390210034658109233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42060878260140023105406155 63091317390210034658109233)
        ·
          refine ⟨47318488042657525993581925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63091317390210034658109233 47318488042657525993581925)
          ·
            refine ⟨8872216507998286123796611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47318488042657525993581925 8872216507998286123796611)
            ·
              refine ⟨13308324761997429185694917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8872216507998286123796611 13308324761997429185694917)
              ·
                refine ⟨2495310892874517972317797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13308324761997429185694917 2495310892874517972317797)
                ·
                  refine ⟨467870792413972119809587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2495310892874517972317797 467870792413972119809587)
                  ·
                    rfl

theorem cell20_1025072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_1025072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025072 prefixEnd_1025072 := by exact prefixLift 1025072
  have htrace : WordTrace (prefixWord ++ tailWord_1025072) baseStart_1025072 baseEnd_1025072 := by
    simpa [prefixWord, tailWord_1025072, baseEnd_1025072] using wordTrace_append hprefix tailTrace_1025072
  have hstable : (prefixWord ++ tailWord_1025072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025072).length < 2 ^ (prefixWord ++ tailWord_1025072).sum := by decide
  have hdescent : baseEnd_1025072 < baseStart_1025072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025085 : List Nat := [1, 4, 1, 3, 1, 4, 1, 3, 2]
def baseStart_1025085 : Nat := 118140960795 + 1025085 * 2 ^ 59
def prefixEnd_1025085 : Nat := 4983230072969 + 3 ^ 40 * 1025085 * 2
def baseEnd_1025085 : Nat := 467876725968201852376201

theorem tailTrace_1025085 : CollatzResearch.WordTrace tailWord_1025085 prefixEnd_1025085 467876725968201852376201 := by
  unfold tailWord_1025085
  simp only [CollatzResearch.WordTrace]
  refine ⟨37387921491299590425028709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24925280994199726950019139 37387921491299590425028709)
  ·
    refine ⟨7010235279618673204692883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37387921491299590425028709 7010235279618673204692883)
    ·
      refine ⟨10515352919428009807039325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7010235279618673204692883 10515352919428009807039325)
      ·
        refine ⟨3943257344785503677639747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10515352919428009807039325 3943257344785503677639747)
        ·
          refine ⟨5914886017178255516459621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3943257344785503677639747 5914886017178255516459621)
          ·
            refine ⟨1109041128220922909336179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5914886017178255516459621 1109041128220922909336179)
            ·
              refine ⟨1663561692331384364004269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109041128220922909336179 1663561692331384364004269)
              ·
                refine ⟨623835634624269136501601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1663561692331384364004269 623835634624269136501601)
                ·
                  refine ⟨467876725968201852376201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623835634624269136501601 467876725968201852376201)
                  ·
                    rfl

theorem cell20_1025085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_1025085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025085 prefixEnd_1025085 := by exact prefixLift 1025085
  have htrace : WordTrace (prefixWord ++ tailWord_1025085) baseStart_1025085 baseEnd_1025085 := by
    simpa [prefixWord, tailWord_1025085, baseEnd_1025085] using wordTrace_append hprefix tailTrace_1025085
  have hstable : (prefixWord ++ tailWord_1025085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025085).length < 2 ^ (prefixWord ++ tailWord_1025085).sum := by decide
  have hdescent : baseEnd_1025085 < baseStart_1025085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025106 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 4]
def baseStart_1025106 : Nat := 118140960795 + 1025106 * 2 ^ 59
def prefixEnd_1025106 : Nat := 4983230072969 + 3 ^ 40 * 1025106 * 2
def baseEnd_1025106 : Nat := 467886310940419112676115

theorem tailTrace_1025106 : CollatzResearch.WordTrace tailWord_1025106 prefixEnd_1025106 467886310940419112676115 := by
  unfold tailWord_1025106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9347171856055877752885793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24925791616149007341028781 9347171856055877752885793)
  ·
    refine ⟨7010378892041908314664345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9347171856055877752885793 7010378892041908314664345)
    ·
      refine ⟨5257784169031431235998259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7010378892041908314664345 5257784169031431235998259)
      ·
        refine ⟨7886676253547146853997389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5257784169031431235998259 7886676253547146853997389)
        ·
          refine ⟨2957503595080180070249021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7886676253547146853997389 2957503595080180070249021)
          ·
            refine ⟨1109063848155067526343383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2957503595080180070249021 1109063848155067526343383)
            ·
              refine ⟨1663595772232601289515075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109063848155067526343383 1663595772232601289515075)
              ·
                refine ⟨2495393658348901934272613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663595772232601289515075 2495393658348901934272613)
                ·
                  refine ⟨467886310940419112676115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2495393658348901934272613 467886310940419112676115)
                  ·
                    rfl

theorem cell20_1025106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_1025106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025106 prefixEnd_1025106 := by exact prefixLift 1025106
  have htrace : WordTrace (prefixWord ++ tailWord_1025106) baseStart_1025106 baseEnd_1025106 := by
    simpa [prefixWord, tailWord_1025106, baseEnd_1025106] using wordTrace_append hprefix tailTrace_1025106
  have hstable : (prefixWord ++ tailWord_1025106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025106).length < 2 ^ (prefixWord ++ tailWord_1025106).sum := by decide
  have hdescent : baseEnd_1025106 < baseStart_1025106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025134 : List Nat := [4, 1, 2, 2, 1, 2, 2, 6]
def baseStart_1025134 : Nat := 118140960795 + 1025134 * 2 ^ 59
def prefixEnd_1025134 : Nat := 4983230072969 + 3 ^ 40 * 1025134 * 2
def baseEnd_1025134 : Nat := 155966363634458486580889

theorem tailTrace_1025134 : CollatzResearch.WordTrace tailWord_1025134 prefixEnd_1025134 155966363634458486580889 := by
  unfold tailWord_1025134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4673713583515258974195307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24926472445414714529041637 4673713583515258974195307)
  ·
    refine ⟨7010570375272888461292961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4673713583515258974195307 7010570375272888461292961)
    ·
      refine ⟨5257927781454666345969721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7010570375272888461292961 5257927781454666345969721)
      ·
        refine ⟨3943445836090999759477291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5257927781454666345969721 3943445836090999759477291)
        ·
          refine ⟨5915168754136499639215937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3943445836090999759477291 5915168754136499639215937)
          ·
            refine ⟨4436376565602374729411953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5915168754136499639215937 4436376565602374729411953)
            ·
              refine ⟨3327282424201781047058965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4436376565602374729411953 3327282424201781047058965)
              ·
                refine ⟨155966363634458486580889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3327282424201781047058965 155966363634458486580889)
                ·
                  rfl

theorem cell20_1025134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_1025134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025134 prefixEnd_1025134 := by exact prefixLift 1025134
  have htrace : WordTrace (prefixWord ++ tailWord_1025134) baseStart_1025134 baseEnd_1025134 := by
    simpa [prefixWord, tailWord_1025134, baseEnd_1025134] using wordTrace_append hprefix tailTrace_1025134
  have hstable : (prefixWord ++ tailWord_1025134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025134).length < 2 ^ (prefixWord ++ tailWord_1025134).sum := by decide
  have hdescent : baseEnd_1025134 < baseStart_1025134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025161 : List Nat := [1, 2, 1, 1, 4, 5, 2, 2, 2]
def baseStart_1025161 : Nat := 118140960795 + 1025161 * 2 ^ 59
def prefixEnd_1025161 : Nat := 4983230072969 + 3 ^ 40 * 1025161 * 2
def baseEnd_1025161 : Nat := 467911414439083365842557

theorem tailTrace_1025161 : CollatzResearch.WordTrace tailWord_1025161 prefixEnd_1025161 467911414439083365842557 := by
  unfold tailWord_1025161
  simp only [CollatzResearch.WordTrace]
  refine ⟨37390693439024255404795337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24927128959349503603196891 37390693439024255404795337)
  ·
    refine ⟨28043020079268191553596503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37390693439024255404795337 28043020079268191553596503)
    ·
      refine ⟨42064530118902287330394755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28043020079268191553596503 42064530118902287330394755)
      ·
        refine ⟨63096795178353430995592133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42064530118902287330394755 63096795178353430995592133)
        ·
          refine ⟨11830649095941268311673525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63096795178353430995592133 11830649095941268311673525)
          ·
            refine ⟨1109123352744493904219393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11830649095941268311673525 1109123352744493904219393)
            ·
              refine ⟨831842514558370428164545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1109123352744493904219393 831842514558370428164545)
              ·
                refine ⟨623881885918777821123409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831842514558370428164545 623881885918777821123409)
                ·
                  refine ⟨467911414439083365842557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623881885918777821123409 467911414439083365842557)
                  ·
                    rfl

theorem cell20_1025161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 2].length) (baseStart_1025161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025161 prefixEnd_1025161 := by exact prefixLift 1025161
  have htrace : WordTrace (prefixWord ++ tailWord_1025161) baseStart_1025161 baseEnd_1025161 := by
    simpa [prefixWord, tailWord_1025161, baseEnd_1025161] using wordTrace_append hprefix tailTrace_1025161
  have hstable : (prefixWord ++ tailWord_1025161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025161).length < 2 ^ (prefixWord ++ tailWord_1025161).sum := by decide
  have hdescent : baseEnd_1025161 < baseStart_1025161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025182 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1025182 : Nat := 118140960795 + 1025182 * 2 ^ 59
def prefixEnd_1025182 : Nat := 4983230072969 + 3 ^ 40 * 1025182 * 2
def baseEnd_1025182 : Nat := 467920999411300626142471

theorem tailTrace_1025182 : CollatzResearch.WordTrace tailWord_1025182 prefixEnd_1025182 467920999411300626142471 := by
  unfold tailWord_1025182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4673932421493521998913725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24927639581298783994206533 4673932421493521998913725)
  ·
    refine ⟨1752724658060070749592647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4673932421493521998913725 1752724658060070749592647)
    ·
      refine ⟨2629086987090106124388971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1752724658060070749592647 2629086987090106124388971)
      ·
        refine ⟨3943630480635159186583457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2629086987090106124388971 3943630480635159186583457)
        ·
          refine ⟨2957722860476369389937593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3943630480635159186583457 2957722860476369389937593)
          ·
            refine ⟨2218292145357277042453195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2957722860476369389937593 2218292145357277042453195)
            ·
              refine ⟨3327438218035915563679793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2218292145357277042453195 3327438218035915563679793)
              ·
                refine ⟨2495578663526936672759845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3327438218035915563679793 2495578663526936672759845)
                ·
                  refine ⟨467920999411300626142471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2495578663526936672759845 467920999411300626142471)
                  ·
                    rfl

theorem cell20_1025182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1025182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025182 prefixEnd_1025182 := by exact prefixLift 1025182
  have htrace : WordTrace (prefixWord ++ tailWord_1025182) baseStart_1025182 baseEnd_1025182 := by
    simpa [prefixWord, tailWord_1025182, baseEnd_1025182] using wordTrace_append hprefix tailTrace_1025182
  have hstable : (prefixWord ++ tailWord_1025182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025182).length < 2 ^ (prefixWord ++ tailWord_1025182).sum := by decide
  have hdescent : baseEnd_1025182 < baseStart_1025182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025200 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 7]
def baseStart_1025200 : Nat := 118140960795 + 1025200 * 2 ^ 59
def prefixEnd_1025200 : Nat := 4983230072969 + 3 ^ 40 * 1025200 * 2
def baseEnd_1025200 : Nat := 467929215101772563542397

theorem tailTrace_1025200 : CollatzResearch.WordTrace tailWord_1025200 prefixEnd_1025200 467929215101772563542397 := by
  unfold tailWord_1025200
  simp only [CollatzResearch.WordTrace]
  refine ⟨18696057942941482532732527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24928077257255310043643369 18696057942941482532732527)
  ·
    refine ⟨28044086914412223799098791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18696057942941482532732527 28044086914412223799098791)
    ·
      refine ⟨42066130371618335698648187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28044086914412223799098791 42066130371618335698648187)
      ·
        refine ⟨63099195557427503547972281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42066130371618335698648187 63099195557427503547972281)
        ·
          refine ⟨47324396668070627660979211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63099195557427503547972281 47324396668070627660979211)
          ·
            refine ⟨70986595002105941491468817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47324396668070627660979211 70986595002105941491468817)
            ·
              refine ⟨53239946251579456118601613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70986595002105941491468817 53239946251579456118601613)
              ·
                refine ⟨19964979844342296044475605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53239946251579456118601613 19964979844342296044475605)
                ·
                  refine ⟨467929215101772563542397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19964979844342296044475605 467929215101772563542397)
                  ·
                    rfl

theorem cell20_1025200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_1025200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025200 prefixEnd_1025200 := by exact prefixLift 1025200
  have htrace : WordTrace (prefixWord ++ tailWord_1025200) baseStart_1025200 baseEnd_1025200 := by
    simpa [prefixWord, tailWord_1025200, baseEnd_1025200] using wordTrace_append hprefix tailTrace_1025200
  have hstable : (prefixWord ++ tailWord_1025200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025200).length < 2 ^ (prefixWord ++ tailWord_1025200).sum := by decide
  have hdescent : baseEnd_1025200 < baseStart_1025200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025203 : List Nat := [1, 1, 1, 2, 3, 2, 3, 5, 2]
def baseStart_1025203 : Nat := 118140960795 + 1025203 * 2 ^ 59
def prefixEnd_1025203 : Nat := 4983230072969 + 3 ^ 40 * 1025203 * 2
def baseEnd_1025203 : Nat := 467930584383517886442385

theorem tailTrace_1025203 : CollatzResearch.WordTrace tailWord_1025203 prefixEnd_1025203 467930584383517886442385 := by
  unfold tailWord_1025203
  simp only [CollatzResearch.WordTrace]
  refine ⟨37392225304872096577824263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24928150203248064385216175 37392225304872096577824263)
  ·
    refine ⟨56088337957308144866736395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37392225304872096577824263 56088337957308144866736395)
    ·
      refine ⟨84132506935962217300104593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56088337957308144866736395 84132506935962217300104593)
      ·
        refine ⟨63099380201971662975078445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84132506935962217300104593 63099380201971662975078445)
        ·
          refine ⟨23662267575739373615654417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63099380201971662975078445 23662267575739373615654417)
          ·
            refine ⟨17746700681804530211740813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23662267575739373615654417 17746700681804530211740813)
            ·
              refine ⟨6655012755676698829402805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17746700681804530211740813 6655012755676698829402805)
              ·
                refine ⟨623907445844690515256513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6655012755676698829402805 623907445844690515256513)
                ·
                  refine ⟨467930584383517886442385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623907445844690515256513 467930584383517886442385)
                  ·
                    rfl

theorem cell20_1025203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 2].length) (baseStart_1025203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025203 prefixEnd_1025203 := by exact prefixLift 1025203
  have htrace : WordTrace (prefixWord ++ tailWord_1025203) baseStart_1025203 baseEnd_1025203 := by
    simpa [prefixWord, tailWord_1025203, baseEnd_1025203] using wordTrace_append hprefix tailTrace_1025203
  have hstable : (prefixWord ++ tailWord_1025203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025203).length < 2 ^ (prefixWord ++ tailWord_1025203).sum := by decide
  have hdescent : baseEnd_1025203 < baseStart_1025203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025206 : List Nat := [5, 1, 3, 2, 1, 1, 7]
def baseStart_1025206 : Nat := 118140960795 + 1025206 * 2 ^ 59
def prefixEnd_1025206 : Nat := 4983230072969 + 3 ^ 40 * 1025206 * 2
def baseEnd_1025206 : Nat := 51992439296140356593597

theorem tailTrace_1025206 : CollatzResearch.WordTrace tailWord_1025206 prefixEnd_1025206 51992439296140356593597 := by
  unfold tailWord_1025206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2337020920241326755636467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24928223149240818726788981 2337020920241326755636467)
  ·
    refine ⟨3505531380361990133454701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2337020920241326755636467 3505531380361990133454701)
    ·
      refine ⟨1314574267635746300045513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3505531380361990133454701 1314574267635746300045513)
      ·
        refine ⟨985930700726809725034135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1314574267635746300045513 985930700726809725034135)
        ·
          refine ⟨1478896051090214587551203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985930700726809725034135 1478896051090214587551203)
          ·
            refine ⟨2218344076635321881326805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478896051090214587551203 2218344076635321881326805)
            ·
              refine ⟨51992439296140356593597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2218344076635321881326805 51992439296140356593597)
              ·
                rfl

theorem cell20_1025206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 7].length) (baseStart_1025206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025206 prefixEnd_1025206 := by exact prefixLift 1025206
  have htrace : WordTrace (prefixWord ++ tailWord_1025206) baseStart_1025206 baseEnd_1025206 := by
    simpa [prefixWord, tailWord_1025206, baseEnd_1025206] using wordTrace_append hprefix tailTrace_1025206
  have hstable : (prefixWord ++ tailWord_1025206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025206).length < 2 ^ (prefixWord ++ tailWord_1025206).sum := by decide
  have hdescent : baseEnd_1025206 < baseStart_1025206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025220 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 4]
def baseStart_1025220 : Nat := 118140960795 + 1025220 * 2 ^ 59
def prefixEnd_1025220 : Nat := 4983230072969 + 3 ^ 40 * 1025220 * 2
def baseEnd_1025220 : Nat := 467938343646741382875649

theorem tailTrace_1025220 : CollatzResearch.WordTrace tailWord_1025220 prefixEnd_1025220 467938343646741382875649 := by
  unfold tailWord_1025220
  simp only [CollatzResearch.WordTrace]
  refine ⟨18696422672905254240596557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24928563563873672320795409 18696422672905254240596557)
  ·
    refine ⟨7011158502339470340223709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18696422672905254240596557 7011158502339470340223709)
    ·
      refine ⟨2629184438377301377583891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7011158502339470340223709 2629184438377301377583891)
      ·
        refine ⟨3943776657565952066375837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2629184438377301377583891 3943776657565952066375837)
        ·
          refine ⟨1478916246587232024890939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3943776657565952066375837 1478916246587232024890939)
          ·
            refine ⟨2218374369880848037336409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478916246587232024890939 2218374369880848037336409)
            ·
              refine ⟨1663780777410636028002307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2218374369880848037336409 1663780777410636028002307)
              ·
                refine ⟨2495671166115954042003461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663780777410636028002307 2495671166115954042003461)
                ·
                  refine ⟨467938343646741382875649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2495671166115954042003461 467938343646741382875649)
                  ·
                    rfl

theorem cell20_1025220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_1025220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025220 prefixEnd_1025220 := by exact prefixLift 1025220
  have htrace : WordTrace (prefixWord ++ tailWord_1025220) baseStart_1025220 baseEnd_1025220 := by
    simpa [prefixWord, tailWord_1025220, baseEnd_1025220] using wordTrace_append hprefix tailTrace_1025220
  have hstable : (prefixWord ++ tailWord_1025220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025220).length < 2 ^ (prefixWord ++ tailWord_1025220).sum := by decide
  have hdescent : baseEnd_1025220 < baseStart_1025220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025224 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 4]
def baseStart_1025224 : Nat := 118140960795 + 1025224 * 2 ^ 59
def prefixEnd_1025224 : Nat := 4983230072969 + 3 ^ 40 * 1025224 * 2
def baseEnd_1025224 : Nat := 467940169355735146742299

theorem tailTrace_1025224 : CollatzResearch.WordTrace tailWord_1025224 prefixEnd_1025224 467940169355735146742299 := by
  unfold tailWord_1025224
  simp only [CollatzResearch.WordTrace]
  refine ⟨18696495618898008582169363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24928660825197344776225817 18696495618898008582169363)
  ·
    refine ⟨28044743428347012873254045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18696495618898008582169363 28044743428347012873254045)
    ·
      refine ⟨10516778785630129827470267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28044743428347012873254045 10516778785630129827470267)
      ·
        refine ⟨15775168178445194741205401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10516778785630129827470267 15775168178445194741205401)
        ·
          refine ⟨11831376133833896055904051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15775168178445194741205401 11831376133833896055904051)
          ·
            refine ⟨17747064200750844083856077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11831376133833896055904051 17747064200750844083856077)
            ·
              refine ⟨6655149075281566531446029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17747064200750844083856077 6655149075281566531446029)
              ·
                refine ⟨2495680903230587449292261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6655149075281566531446029 2495680903230587449292261)
                ·
                  refine ⟨467940169355735146742299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2495680903230587449292261 467940169355735146742299)
                  ·
                    rfl

theorem cell20_1025224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_1025224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025224 prefixEnd_1025224 := by exact prefixLift 1025224
  have htrace : WordTrace (prefixWord ++ tailWord_1025224) baseStart_1025224 baseEnd_1025224 := by
    simpa [prefixWord, tailWord_1025224, baseEnd_1025224] using wordTrace_append hprefix tailTrace_1025224
  have hstable : (prefixWord ++ tailWord_1025224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025224).length < 2 ^ (prefixWord ++ tailWord_1025224).sum := by decide
  have hdescent : baseEnd_1025224 < baseStart_1025224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025248 : List Nat := [2, 1, 1, 3, 1, 4, 4, 4]
def baseStart_1025248 : Nat := 118140960795 + 1025248 * 2 ^ 59
def prefixEnd_1025248 : Nat := 4983230072969 + 3 ^ 40 * 1025248 * 2
def baseEnd_1025248 : Nat := 155983707869899243314067

theorem tailTrace_1025248 : CollatzResearch.WordTrace tailWord_1025248 prefixEnd_1025248 155983707869899243314067 := by
  unfold tailWord_1025248
  simp only [CollatzResearch.WordTrace]
  refine ⟨18696933294854534631606199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24929244393139379508808265 18696933294854534631606199)
  ·
    refine ⟨28045399942281801947409299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18696933294854534631606199 28045399942281801947409299)
    ·
      refine ⟨42068099913422702921113949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28045399942281801947409299 42068099913422702921113949)
      ·
        refine ⟨15775537467533513595417731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42068099913422702921113949 15775537467533513595417731)
        ·
          refine ⟨23663306201300270393126597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15775537467533513595417731 23663306201300270393126597)
          ·
            refine ⟨4436869912743800698711237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23663306201300270393126597 4436869912743800698711237)
            ·
              refine ⟨831913108639462631008357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4436869912743800698711237 831913108639462631008357)
              ·
                refine ⟨155983707869899243314067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 831913108639462631008357 155983707869899243314067)
                ·
                  rfl

theorem cell20_1025248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_1025248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025248 prefixEnd_1025248 := by exact prefixLift 1025248
  have htrace : WordTrace (prefixWord ++ tailWord_1025248) baseStart_1025248 baseEnd_1025248 := by
    simpa [prefixWord, tailWord_1025248, baseEnd_1025248] using wordTrace_append hprefix tailTrace_1025248
  have hstable : (prefixWord ++ tailWord_1025248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025248).length < 2 ^ (prefixWord ++ tailWord_1025248).sum := by decide
  have hdescent : baseEnd_1025248 < baseStart_1025248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025258 : List Nat := [3, 1, 3, 1, 1, 3, 3, 3, 2]
def baseStart_1025258 : Nat := 118140960795 + 1025258 * 2 ^ 59
def prefixEnd_1025258 : Nat := 4983230072969 + 3 ^ 40 * 1025258 * 2
def baseEnd_1025258 : Nat := 467955687882182139608827

theorem tailTrace_1025258 : CollatzResearch.WordTrace tailWord_1025258 prefixEnd_1025258 467955687882182139608827 := by
  unfold tailWord_1025258
  simp only [CollatzResearch.WordTrace]
  refine ⟨9348557829918210242769107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24929487546448560647384285 9348557829918210242769107)
  ·
    refine ⟨14022836744877315364153661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9348557829918210242769107 14022836744877315364153661)
    ·
      refine ⟨5258563779328993261557623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14022836744877315364153661 5258563779328993261557623)
      ·
        refine ⟨7887845668993489892336435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5258563779328993261557623 7887845668993489892336435)
        ·
          refine ⟨11831768503490234838504653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7887845668993489892336435 11831768503490234838504653)
          ·
            refine ⟨4436913188808838064439245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11831768503490234838504653 4436913188808838064439245)
            ·
              refine ⟨1663842445803314274164717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4436913188808838064439245 1663842445803314274164717)
              ·
                refine ⟨623940917176242852811769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1663842445803314274164717 623940917176242852811769)
                ·
                  refine ⟨467955687882182139608827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623940917176242852811769 467955687882182139608827)
                  ·
                    rfl

theorem cell20_1025258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_1025258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025258 prefixEnd_1025258 := by exact prefixLift 1025258
  have htrace : WordTrace (prefixWord ++ tailWord_1025258) baseStart_1025258 baseEnd_1025258 := by
    simpa [prefixWord, tailWord_1025258, baseEnd_1025258] using wordTrace_append hprefix tailTrace_1025258
  have hstable : (prefixWord ++ tailWord_1025258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025258).length < 2 ^ (prefixWord ++ tailWord_1025258).sum := by decide
  have hdescent : baseEnd_1025258 < baseStart_1025258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025262 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_1025262 : Nat := 118140960795 + 1025262 * 2 ^ 59
def prefixEnd_1025262 : Nat := 4983230072969 + 3 ^ 40 * 1025262 * 2
def baseEnd_1025262 : Nat := 467957513591175903475477

theorem tailTrace_1025262 : CollatzResearch.WordTrace tailWord_1025262 prefixEnd_1025262 467957513591175903475477 := by
  unfold tailWord_1025262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4674297151457293706777755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24929584807772233102814693 4674297151457293706777755)
  ·
    refine ⟨7011445727185940560166633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4674297151457293706777755 7011445727185940560166633)
    ·
      refine ⟨5258584295389455420124975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7011445727185940560166633 5258584295389455420124975)
      ·
        refine ⟨7887876443084183130187463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5258584295389455420124975 7887876443084183130187463)
        ·
          refine ⟨11831814664626274695281195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7887876443084183130187463 11831814664626274695281195)
          ·
            refine ⟨17747721996939412042921793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11831814664626274695281195 17747721996939412042921793)
            ·
              refine ⟨13310791497704559032191345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17747721996939412042921793 13310791497704559032191345)
              ·
                refine ⟨9983093623278419274143509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13310791497704559032191345 9983093623278419274143509)
                ·
                  refine ⟨467957513591175903475477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9983093623278419274143509 467957513591175903475477)
                  ·
                    rfl

theorem cell20_1025262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_1025262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025262 prefixEnd_1025262 := by exact prefixLift 1025262
  have htrace : WordTrace (prefixWord ++ tailWord_1025262) baseStart_1025262 baseEnd_1025262 := by
    simpa [prefixWord, tailWord_1025262, baseEnd_1025262] using wordTrace_append hprefix tailTrace_1025262
  have hstable : (prefixWord ++ tailWord_1025262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025262).length < 2 ^ (prefixWord ++ tailWord_1025262).sum := by decide
  have hdescent : baseEnd_1025262 < baseStart_1025262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025279 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 4]
def baseStart_1025279 : Nat := 118140960795 + 1025279 * 2 ^ 59
def prefixEnd_1025279 : Nat := 4983230072969 + 3 ^ 40 * 1025279 * 2
def baseEnd_1025279 : Nat := 467965272854399399908741

theorem tailTrace_1025279 : CollatzResearch.WordTrace tailWord_1025279 prefixEnd_1025279 467965272854399399908741 := by
  unfold tailWord_1025279
  simp only [CollatzResearch.WordTrace]
  refine ⟨37394997252596761557590891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24929998168397841038393927 37394997252596761557590891)
  ·
    refine ⟨56092495878895142336386337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37394997252596761557590891 56092495878895142336386337)
    ·
      refine ⟨42069371909171356752289753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56092495878895142336386337 42069371909171356752289753)
      ·
        refine ⟨31552028931878517564217315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42069371909171356752289753 31552028931878517564217315)
        ·
          refine ⟨47328043397817776346325973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31552028931878517564217315 47328043397817776346325973)
          ·
            refine ⟨1109251017136354133117015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 47328043397817776346325973 1109251017136354133117015)
            ·
              refine ⟨1663876525704531199675523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109251017136354133117015 1663876525704531199675523)
              ·
                refine ⟨2495814788556796799513285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663876525704531199675523 2495814788556796799513285)
                ·
                  refine ⟨467965272854399399908741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2495814788556796799513285 467965272854399399908741)
                  ·
                    rfl

theorem cell20_1025279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 4].length) (baseStart_1025279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025279 prefixEnd_1025279 := by exact prefixLift 1025279
  have htrace : WordTrace (prefixWord ++ tailWord_1025279) baseStart_1025279 baseEnd_1025279 := by
    simpa [prefixWord, tailWord_1025279, baseEnd_1025279] using wordTrace_append hprefix tailTrace_1025279
  have hstable : (prefixWord ++ tailWord_1025279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025279).length < 2 ^ (prefixWord ++ tailWord_1025279).sum := by decide
  have hdescent : baseEnd_1025279 < baseStart_1025279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025331 : List Nat := [1, 1, 1, 2, 5, 2, 1, 4, 3]
def baseStart_1025331 : Nat := 118140960795 + 1025331 * 2 ^ 59
def prefixEnd_1025331 : Nat := 4983230072969 + 3 ^ 40 * 1025331 * 2
def baseEnd_1025331 : Nat := 467989007071318330175195

theorem tailTrace_1025331 : CollatzResearch.WordTrace tailWord_1025331 prefixEnd_1025331 467989007071318330175195 := by
  unfold tailWord_1025331
  simp only [CollatzResearch.WordTrace]
  refine ⟨37396893848408374438483847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24931262565605582958989231 37396893848408374438483847)
  ·
    refine ⟨56095340772612561657725771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37396893848408374438483847 56095340772612561657725771)
    ·
      refine ⟨84143011158918842486588657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56095340772612561657725771 84143011158918842486588657)
      ·
        refine ⟨63107258369189131864941493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84143011158918842486588657 63107258369189131864941493)
        ·
          refine ⟨5916305472111481112338265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63107258369189131864941493 5916305472111481112338265)
          ·
            refine ⟨4437229104083610834253699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5916305472111481112338265 4437229104083610834253699)
            ·
              refine ⟨6655843656125416251380549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437229104083610834253699 6655843656125416251380549)
              ·
                refine ⟨1247970685523515547133853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6655843656125416251380549 1247970685523515547133853)
                ·
                  refine ⟨467989007071318330175195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247970685523515547133853 467989007071318330175195)
                  ·
                    rfl

theorem cell20_1025331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 3].length) (baseStart_1025331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025331 prefixEnd_1025331 := by exact prefixLift 1025331
  have htrace : WordTrace (prefixWord ++ tailWord_1025331) baseStart_1025331 baseEnd_1025331 := by
    simpa [prefixWord, tailWord_1025331, baseEnd_1025331] using wordTrace_append hprefix tailTrace_1025331
  have hstable : (prefixWord ++ tailWord_1025331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025331).length < 2 ^ (prefixWord ++ tailWord_1025331).sum := by decide
  have hdescent : baseEnd_1025331 < baseStart_1025331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025338 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_1025338 : Nat := 118140960795 + 1025338 * 2 ^ 59
def prefixEnd_1025338 : Nat := 4983230072969 + 3 ^ 40 * 1025338 * 2
def baseEnd_1025338 : Nat := 467992202062057416941833

theorem tailTrace_1025338 : CollatzResearch.WordTrace tailWord_1025338 prefixEnd_1025338 467992202062057416941833 := by
  unfold tailWord_1025338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9349287289845753658497167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24931432772922009755992445 9349287289845753658497167)
  ·
    refine ⟨14023930934768630487745751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9349287289845753658497167 14023930934768630487745751)
    ·
      refine ⟨21035896402152945731618627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14023930934768630487745751 21035896402152945731618627)
      ·
        refine ⟨31553844603229418597427941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21035896402152945731618627 31553844603229418597427941)
        ·
          refine ⟨5916345863105515987017739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31553844603229418597427941 5916345863105515987017739)
          ·
            refine ⟨8874518794658273980526609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5916345863105515987017739 8874518794658273980526609)
            ·
              refine ⟨6655889095993705485394957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8874518794658273980526609 6655889095993705485394957)
              ·
                refine ⟨2495958410997639557023109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6655889095993705485394957 2495958410997639557023109)
                ·
                  refine ⟨467992202062057416941833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2495958410997639557023109 467992202062057416941833)
                  ·
                    rfl

theorem cell20_1025338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_1025338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025338 prefixEnd_1025338 := by exact prefixLift 1025338
  have htrace : WordTrace (prefixWord ++ tailWord_1025338) baseStart_1025338 baseEnd_1025338 := by
    simpa [prefixWord, tailWord_1025338, baseEnd_1025338] using wordTrace_append hprefix tailTrace_1025338
  have hstable : (prefixWord ++ tailWord_1025338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025338).length < 2 ^ (prefixWord ++ tailWord_1025338).sum := by decide
  have hdescent : baseEnd_1025338 < baseStart_1025338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025352 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 7]
def baseStart_1025352 : Nat := 118140960795 + 1025352 * 2 ^ 59
def prefixEnd_1025352 : Nat := 4983230072969 + 3 ^ 40 * 1025352 * 2
def baseEnd_1025352 : Nat := 467998592043535590475109

theorem tailTrace_1025352 : CollatzResearch.WordTrace tailWord_1025352 prefixEnd_1025352 467998592043535590475109 := by
  unfold tailWord_1025352
  simp only [CollatzResearch.WordTrace]
  refine ⟨18698829890666147512499155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24931773187554863349998873 18698829890666147512499155)
  ·
    refine ⟨28048244835999221268748733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18698829890666147512499155 28048244835999221268748733)
    ·
      refine ⟨10518091813499707975780775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28048244835999221268748733 10518091813499707975780775)
      ·
        refine ⟨15777137720249561963671163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10518091813499707975780775 15777137720249561963671163)
        ·
          refine ⟨23665706580374342945506745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15777137720249561963671163 23665706580374342945506745)
          ·
            refine ⟨17749279935280757209130059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23665706580374342945506745 17749279935280757209130059)
            ·
              refine ⟨26623919902921135813695089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17749279935280757209130059 26623919902921135813695089)
              ·
                refine ⟨19967939927190851860271317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26623919902921135813695089 19967939927190851860271317)
                ·
                  refine ⟨467998592043535590475109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19967939927190851860271317 467998592043535590475109)
                  ·
                    rfl

theorem cell20_1025352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_1025352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025352 prefixEnd_1025352 := by exact prefixLift 1025352
  have htrace : WordTrace (prefixWord ++ tailWord_1025352) baseStart_1025352 baseEnd_1025352 := by
    simpa [prefixWord, tailWord_1025352, baseEnd_1025352] using wordTrace_append hprefix tailTrace_1025352
  have hstable : (prefixWord ++ tailWord_1025352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025352).length < 2 ^ (prefixWord ++ tailWord_1025352).sum := by decide
  have hdescent : baseEnd_1025352 < baseStart_1025352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025386 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 5]
def baseStart_1025386 : Nat := 118140960795 + 1025386 * 2 ^ 59
def prefixEnd_1025386 : Nat := 4983230072969 + 3 ^ 40 * 1025386 * 2
def baseEnd_1025386 : Nat := 468014110569982583341637

theorem tailTrace_1025386 : CollatzResearch.WordTrace tailWord_1025386 prefixEnd_1025386 468014110569982583341637 := by
  unfold tailWord_1025386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9349724965802279707934003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24932599908806079221157341 9349724965802279707934003)
  ·
    refine ⟨14024587448703419561901005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9349724965802279707934003 14024587448703419561901005)
    ·
      refine ⟨5259220293263782335712877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14024587448703419561901005 5259220293263782335712877)
      ·
        refine ⟨1972207609973918375892329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5259220293263782335712877 1972207609973918375892329)
        ·
          refine ⟨1479155707480438781919247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1972207609973918375892329 1479155707480438781919247)
          ·
            refine ⟨2218733561220658172878871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479155707480438781919247 2218733561220658172878871)
            ·
              refine ⟨3328100341830987259318307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2218733561220658172878871 3328100341830987259318307)
              ·
                refine ⟨4992150512746480888977461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3328100341830987259318307 4992150512746480888977461)
                ·
                  refine ⟨468014110569982583341637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4992150512746480888977461 468014110569982583341637)
                  ·
                    rfl

theorem cell20_1025386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_1025386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025386 prefixEnd_1025386 := by exact prefixLift 1025386
  have htrace : WordTrace (prefixWord ++ tailWord_1025386) baseStart_1025386 baseEnd_1025386 := by
    simpa [prefixWord, tailWord_1025386, baseEnd_1025386] using wordTrace_append hprefix tailTrace_1025386
  have hstable : (prefixWord ++ tailWord_1025386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025386).length < 2 ^ (prefixWord ++ tailWord_1025386).sum := by decide
  have hdescent : baseEnd_1025386 < baseStart_1025386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025393 : List Nat := [1, 2, 2, 2, 1, 2, 4, 4, 2]
def baseStart_1025393 : Nat := 118140960795 + 1025393 * 2 ^ 59
def prefixEnd_1025393 : Nat := 4983230072969 + 3 ^ 40 * 1025393 * 2
def baseEnd_1025393 : Nat := 468017305560721670108275

theorem tailTrace_1025393 : CollatzResearch.WordTrace tailWord_1025393 prefixEnd_1025393 468017305560721670108275 := by
  unfold tailWord_1025393
  simp only [CollatzResearch.WordTrace]
  refine ⟨37399155174183759027240833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24932770116122506018160555 37399155174183759027240833)
  ·
    refine ⟨28049366380637819270430625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37399155174183759027240833 28049366380637819270430625)
    ·
      refine ⟨21037024785478364452822969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28049366380637819270430625 21037024785478364452822969)
      ·
        refine ⟨15777768589108773339617227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21037024785478364452822969 15777768589108773339617227)
        ·
          refine ⟨23666652883663160009425841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15777768589108773339617227 23666652883663160009425841)
          ·
            refine ⟨17749989662747370007069381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23666652883663160009425841 17749989662747370007069381)
            ·
              refine ⟨3328123061765131876325509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17749989662747370007069381 3328123061765131876325509)
              ·
                refine ⟨624023074080962226811033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3328123061765131876325509 624023074080962226811033)
                ·
                  refine ⟨468017305560721670108275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624023074080962226811033 468017305560721670108275)
                  ·
                    rfl

theorem cell20_1025393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 2].length) (baseStart_1025393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025393 prefixEnd_1025393 := by exact prefixLift 1025393
  have htrace : WordTrace (prefixWord ++ tailWord_1025393) baseStart_1025393 baseEnd_1025393 := by
    simpa [prefixWord, tailWord_1025393, baseEnd_1025393] using wordTrace_append hprefix tailTrace_1025393
  have hstable : (prefixWord ++ tailWord_1025393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025393).length < 2 ^ (prefixWord ++ tailWord_1025393).sum := by decide
  have hdescent : baseEnd_1025393 < baseStart_1025393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025410 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1025410 : Nat := 118140960795 + 1025410 * 2 ^ 59
def prefixEnd_1025410 : Nat := 4983230072969 + 3 ^ 40 * 1025410 * 2
def baseEnd_1025410 : Nat := 468025064823945166541539

theorem tailTrace_1025410 : CollatzResearch.WordTrace tailWord_1025410 prefixEnd_1025410 468025064823945166541539 := by
  unfold tailWord_1025410
  simp only [CollatzResearch.WordTrace]
  refine ⟨9349943803780542732652421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24933183476748113953739789 9349943803780542732652421)
  ·
    refine ⟨1753114463208851762372329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9349943803780542732652421 1753114463208851762372329)
    ·
      refine ⟨1314835847406638821779247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1753114463208851762372329 1314835847406638821779247)
      ·
        refine ⟨1972253771109958232668871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1314835847406638821779247 1972253771109958232668871)
        ·
          refine ⟨2958380656664937349003307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1972253771109958232668871 2958380656664937349003307)
          ·
            refine ⟨4437570984997406023504961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2958380656664937349003307 4437570984997406023504961)
            ·
              refine ⟨3328178238748054517628721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4437570984997406023504961 3328178238748054517628721)
              ·
                refine ⟨2496133679061040888221541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3328178238748054517628721 2496133679061040888221541)
                ·
                  refine ⟨468025064823945166541539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2496133679061040888221541 468025064823945166541539)
                  ·
                    rfl

theorem cell20_1025410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1025410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025410 prefixEnd_1025410 := by exact prefixLift 1025410
  have htrace : WordTrace (prefixWord ++ tailWord_1025410) baseStart_1025410 baseEnd_1025410 := by
    simpa [prefixWord, tailWord_1025410, baseEnd_1025410] using wordTrace_append hprefix tailTrace_1025410
  have hstable : (prefixWord ++ tailWord_1025410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025410).length < 2 ^ (prefixWord ++ tailWord_1025410).sum := by decide
  have hdescent : baseEnd_1025410 < baseStart_1025410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025417 : List Nat := [1, 2, 1, 1, 7, 2, 2, 4]
def baseStart_1025417 : Nat := 118140960795 + 1025417 * 2 ^ 59
def prefixEnd_1025417 : Nat := 4983230072969 + 3 ^ 40 * 1025417 * 2
def baseEnd_1025417 : Nat := 156009419938228084436059

theorem tailTrace_1025417 : CollatzResearch.WordTrace tailWord_1025417 prefixEnd_1025417 156009419938228084436059 := by
  unfold tailWord_1025417
  simp only [CollatzResearch.WordTrace]
  refine ⟨37400030526096811126114505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24933353684064540750743003 37400030526096811126114505)
  ·
    refine ⟨28050022894572608344585879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37400030526096811126114505 28050022894572608344585879)
    ·
      refine ⟨42075034341858912516878819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28050022894572608344585879 42075034341858912516878819)
      ·
        refine ⟨63112551512788368775318229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42075034341858912516878819 63112551512788368775318229)
        ·
          refine ⟨1479200426080977393171521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 63112551512788368775318229 1479200426080977393171521)
          ·
            refine ⟨1109400319560733044878641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1479200426080977393171521 1109400319560733044878641)
            ·
              refine ⟨832050239670549783658981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1109400319560733044878641 832050239670549783658981)
              ·
                refine ⟨156009419938228084436059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 832050239670549783658981 156009419938228084436059)
                ·
                  rfl

theorem cell20_1025417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 4].length) (baseStart_1025417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025417 prefixEnd_1025417 := by exact prefixLift 1025417
  have htrace : WordTrace (prefixWord ++ tailWord_1025417) baseStart_1025417 baseEnd_1025417 := by
    simpa [prefixWord, tailWord_1025417, baseEnd_1025417] using wordTrace_append hprefix tailTrace_1025417
  have hstable : (prefixWord ++ tailWord_1025417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025417).length < 2 ^ (prefixWord ++ tailWord_1025417).sum := by decide
  have hdescent : baseEnd_1025417 < baseStart_1025417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025452 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 4]
def baseStart_1025452 : Nat := 118140960795 + 1025452 * 2 ^ 59
def prefixEnd_1025452 : Nat := 4983230072969 + 3 ^ 40 * 1025452 * 2
def baseEnd_1025452 : Nat := 468044234768379687141367

theorem tailTrace_1025452 : CollatzResearch.WordTrace tailWord_1025452 prefixEnd_1025452 468044234768379687141367 := by
  unfold tailWord_1025452
  simp only [CollatzResearch.WordTrace]
  refine ⟨18700653540485006051819305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24934204720646674735759073 18700653540485006051819305)
  ·
    refine ⟨14025490155363754538864479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18700653540485006051819305 14025490155363754538864479)
    ·
      refine ⟨21038235233045631808296719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14025490155363754538864479 21038235233045631808296719)
      ·
        refine ⟨31557352849568447712445079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21038235233045631808296719 31557352849568447712445079)
        ·
          refine ⟨47336029274352671568667619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31557352849568447712445079 47336029274352671568667619)
          ·
            refine ⟨71004043911529007353001429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47336029274352671568667619 71004043911529007353001429)
            ·
              refine ⟨1664157279176461109835971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71004043911529007353001429 1664157279176461109835971)
              ·
                refine ⟨2496235918764691664753957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1664157279176461109835971 2496235918764691664753957)
                ·
                  refine ⟨468044234768379687141367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2496235918764691664753957 468044234768379687141367)
                  ·
                    rfl

theorem cell20_1025452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_1025452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025452 prefixEnd_1025452 := by exact prefixLift 1025452
  have htrace : WordTrace (prefixWord ++ tailWord_1025452) baseStart_1025452 baseEnd_1025452 := by
    simpa [prefixWord, tailWord_1025452, baseEnd_1025452] using wordTrace_append hprefix tailTrace_1025452
  have hstable : (prefixWord ++ tailWord_1025452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025452).length < 2 ^ (prefixWord ++ tailWord_1025452).sum := by decide
  have hdescent : baseEnd_1025452 < baseStart_1025452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025476 : List Nat := [2, 3, 3, 2, 1, 1, 2, 6]
def baseStart_1025476 : Nat := 118140960795 + 1025476 * 2 ^ 59
def prefixEnd_1025476 : Nat := 4983230072969 + 3 ^ 40 * 1025476 * 2
def baseEnd_1025476 : Nat := 156018396340780756780423

theorem tailTrace_1025476 : CollatzResearch.WordTrace tailWord_1025476 prefixEnd_1025476 156018396340780756780423 := by
  unfold tailWord_1025476
  simp only [CollatzResearch.WordTrace]
  refine ⟨18701091216441532101256141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24934788288588709468341521 18701091216441532101256141)
  ·
    refine ⟨7012909206165574537971053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18701091216441532101256141 7012909206165574537971053)
    ·
      refine ⟨2629840952312090451739145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7012909206165574537971053 2629840952312090451739145)
      ·
        refine ⟨1972380714234067838804359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2629840952312090451739145 1972380714234067838804359)
        ·
          refine ⟨2958571071351101758206539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1972380714234067838804359 2958571071351101758206539)
          ·
            refine ⟨4437856607026652637309809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2958571071351101758206539 4437856607026652637309809)
            ·
              refine ⟨3328392455269989477982357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4437856607026652637309809 3328392455269989477982357)
              ·
                refine ⟨156018396340780756780423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3328392455269989477982357 156018396340780756780423)
                ·
                  rfl

theorem cell20_1025476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_1025476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025476 prefixEnd_1025476 := by exact prefixLift 1025476
  have htrace : WordTrace (prefixWord ++ tailWord_1025476) baseStart_1025476 baseEnd_1025476 := by
    simpa [prefixWord, tailWord_1025476, baseEnd_1025476] using wordTrace_append hprefix tailTrace_1025476
  have hstable : (prefixWord ++ tailWord_1025476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025476).length < 2 ^ (prefixWord ++ tailWord_1025476).sum := by decide
  have hdescent : baseEnd_1025476 < baseStart_1025476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025521 : List Nat := [1, 2, 2, 2, 3, 2, 2, 3, 3]
def baseStart_1025521 : Nat := 118140960795 + 1025521 * 2 ^ 59
def prefixEnd_1025521 : Nat := 4983230072969 + 3 ^ 40 * 1025521 * 2
def baseEnd_1025521 : Nat := 468075728248522113841085

theorem tailTrace_1025521 : CollatzResearch.WordTrace tailWord_1025521 prefixEnd_1025521 468075728248522113841085 := by
  unfold tailWord_1025521
  simp only [CollatzResearch.WordTrace]
  refine ⟨37403823717720036887900417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24935882478480024591933611 37403823717720036887900417)
  ·
    refine ⟨28052867788290027665925313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37403823717720036887900417 28052867788290027665925313)
    ·
      refine ⟨21039650841217520749443985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28052867788290027665925313 21039650841217520749443985)
      ·
        refine ⟨15779738130913140562082989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21039650841217520749443985 15779738130913140562082989)
        ·
          refine ⟨5917401799092427710781121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15779738130913140562082989 5917401799092427710781121)
          ·
            refine ⟨4438051349319320783085841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5917401799092427710781121 4438051349319320783085841)
            ·
              refine ⟨3328538511989490587314381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4438051349319320783085841 3328538511989490587314381)
              ·
                refine ⟨1248201941996058970242893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3328538511989490587314381 1248201941996058970242893)
                ·
                  refine ⟨468075728248522113841085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1248201941996058970242893 468075728248522113841085)
                  ·
                    rfl

theorem cell20_1025521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_1025521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025521 prefixEnd_1025521 := by exact prefixLift 1025521
  have htrace : WordTrace (prefixWord ++ tailWord_1025521) baseStart_1025521 baseEnd_1025521 := by
    simpa [prefixWord, tailWord_1025521, baseEnd_1025521] using wordTrace_append hprefix tailTrace_1025521
  have hstable : (prefixWord ++ tailWord_1025521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025521).length < 2 ^ (prefixWord ++ tailWord_1025521).sum := by decide
  have hdescent : baseEnd_1025521 < baseStart_1025521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025528 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 4]
def baseStart_1025528 : Nat := 118140960795 + 1025528 * 2 ^ 59
def prefixEnd_1025528 : Nat := 4983230072969 + 3 ^ 40 * 1025528 * 2
def baseEnd_1025528 : Nat := 468078923239261200607723

theorem tailTrace_1025528 : CollatzResearch.WordTrace tailWord_1025528 prefixEnd_1025528 468078923239261200607723 := by
  unfold tailWord_1025528
  simp only [CollatzResearch.WordTrace]
  refine ⟨18702039514347338541702619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24936052685796451388936825 18702039514347338541702619)
  ·
    refine ⟨28053059271521007812553929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18702039514347338541702619 28053059271521007812553929)
    ·
      refine ⟨21039794453640755859415447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28053059271521007812553929 21039794453640755859415447)
      ·
        refine ⟨31559691680461133789123171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21039794453640755859415447 31559691680461133789123171)
        ·
          refine ⟨47339537520691700683684757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31559691680461133789123171 47339537520691700683684757)
          ·
            refine ⟨2219040821282423469547723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47339537520691700683684757 2219040821282423469547723)
            ·
              refine ⟨3328561231923635204321585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2219040821282423469547723 3328561231923635204321585)
              ·
                refine ⟨2496420923942726403241189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3328561231923635204321585 2496420923942726403241189)
                ·
                  refine ⟨468078923239261200607723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2496420923942726403241189 468078923239261200607723)
                  ·
                    rfl

theorem cell20_1025528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_1025528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025528 prefixEnd_1025528 := by exact prefixLift 1025528
  have htrace : WordTrace (prefixWord ++ tailWord_1025528) baseStart_1025528 baseEnd_1025528 := by
    simpa [prefixWord, tailWord_1025528, baseEnd_1025528] using wordTrace_append hprefix tailTrace_1025528
  have hstable : (prefixWord ++ tailWord_1025528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025528).length < 2 ^ (prefixWord ++ tailWord_1025528).sum := by decide
  have hdescent : baseEnd_1025528 < baseStart_1025528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025545 : List Nat := [1, 2, 1, 1, 3, 1, 6, 3, 2]
def baseStart_1025545 : Nat := 118140960795 + 1025545 * 2 ^ 59
def prefixEnd_1025545 : Nat := 4983230072969 + 3 ^ 40 * 1025545 * 2
def baseEnd_1025545 : Nat := 468086682502484697040987

theorem tailTrace_1025545 : CollatzResearch.WordTrace tailWord_1025545 prefixEnd_1025545 468086682502484697040987 := by
  unfold tailWord_1025545
  simp only [CollatzResearch.WordTrace]
  refine ⟨37404699069633088986774089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24936466046422059324516059 37404699069633088986774089)
  ·
    refine ⟨28053524302224816740080567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37404699069633088986774089 28053524302224816740080567)
    ·
      refine ⟨42080286453337225110120851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28053524302224816740080567 42080286453337225110120851)
      ·
        refine ⟨63120429680005837665181277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42080286453337225110120851 63120429680005837665181277)
        ·
          refine ⟨23670161130002189124442979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63120429680005837665181277 23670161130002189124442979)
          ·
            refine ⟨35505241695003283686664469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23670161130002189124442979 35505241695003283686664469)
            ·
              refine ⟨1664308204453278922812397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35505241695003283686664469 1664308204453278922812397)
              ·
                refine ⟨624115576669979596054649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1664308204453278922812397 624115576669979596054649)
                ·
                  refine ⟨468086682502484697040987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624115576669979596054649 468086682502484697040987)
                  ·
                    rfl

theorem cell20_1025545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 2].length) (baseStart_1025545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025545 prefixEnd_1025545 := by exact prefixLift 1025545
  have htrace : WordTrace (prefixWord ++ tailWord_1025545) baseStart_1025545 baseEnd_1025545 := by
    simpa [prefixWord, tailWord_1025545, baseEnd_1025545] using wordTrace_append hprefix tailTrace_1025545
  have hstable : (prefixWord ++ tailWord_1025545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025545).length < 2 ^ (prefixWord ++ tailWord_1025545).sum := by decide
  have hdescent : baseEnd_1025545 < baseStart_1025545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025628 : List Nat := [2, 2, 4, 1, 2, 2, 2, 5]
def baseStart_1025628 : Nat := 118140960795 + 1025628 * 2 ^ 59
def prefixEnd_1025628 : Nat := 4983230072969 + 3 ^ 40 * 1025628 * 2
def baseEnd_1025628 : Nat := 156041521988035099091327

theorem tailTrace_1025628 : CollatzResearch.WordTrace tailWord_1025628 prefixEnd_1025628 156041521988035099091327 := by
  unfold tailWord_1025628
  simp only [CollatzResearch.WordTrace]
  refine ⟨18703863164166197081022769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24938484218888262774697025 18703863164166197081022769)
  ·
    refine ⟨14027897373124647810767077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18703863164166197081022769 14027897373124647810767077)
    ·
      refine ⟨2630230757460871464518827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14027897373124647810767077 2630230757460871464518827)
      ·
        refine ⟨3945346136191307196778241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2630230757460871464518827 3945346136191307196778241)
        ·
          refine ⟨2959009602143480397583681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3945346136191307196778241 2959009602143480397583681)
          ·
            refine ⟨2219257201607610298187761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2959009602143480397583681 2219257201607610298187761)
            ·
              refine ⟨1664442901205707723640821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2219257201607610298187761 1664442901205707723640821)
              ·
                refine ⟨156041521988035099091327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1664442901205707723640821 156041521988035099091327)
                ·
                  rfl

theorem cell20_1025628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_1025628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025628 prefixEnd_1025628 := by exact prefixLift 1025628
  have htrace : WordTrace (prefixWord ++ tailWord_1025628) baseStart_1025628 baseEnd_1025628 := by
    simpa [prefixWord, tailWord_1025628, baseEnd_1025628] using wordTrace_append hprefix tailTrace_1025628
  have hstable : (prefixWord ++ tailWord_1025628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025628).length < 2 ^ (prefixWord ++ tailWord_1025628).sum := by decide
  have hdescent : baseEnd_1025628 < baseStart_1025628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025635 : List Nat := [1, 1, 1, 5, 1, 4, 1, 3, 3]
def baseStart_1025635 : Nat := 118140960795 + 1025635 * 2 ^ 59
def prefixEnd_1025635 : Nat := 4983230072969 + 3 ^ 40 * 1025635 * 2
def baseEnd_1025635 : Nat := 468127760954844384040619

theorem tailTrace_1025635 : CollatzResearch.WordTrace tailWord_1025635 prefixEnd_1025635 468127760954844384040619 := by
  unfold tailWord_1025635
  simp only [CollatzResearch.WordTrace]
  refine ⟨37407981639307034357550359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24938654426204689571700239 37407981639307034357550359)
  ·
    refine ⟨56111972458960551536325539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37407981639307034357550359 56111972458960551536325539)
    ·
      refine ⟨84167958688440827304488309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56111972458960551536325539 84167958688440827304488309)
      ·
        refine ⟨7890746127041327559795779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84167958688440827304488309 7890746127041327559795779)
        ·
          refine ⟨11836119190561991339693669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7890746127041327559795779 11836119190561991339693669)
          ·
            refine ⟨2219272348230373376192563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11836119190561991339693669 2219272348230373376192563)
            ·
              refine ⟨3328908522345560064288845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2219272348230373376192563 3328908522345560064288845)
              ·
                refine ⟨1248340695879585024108317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3328908522345560064288845 1248340695879585024108317)
                ·
                  refine ⟨468127760954844384040619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1248340695879585024108317 468127760954844384040619)
                  ·
                    rfl

theorem cell20_1025635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 3].length) (baseStart_1025635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025635 prefixEnd_1025635 := by exact prefixLift 1025635
  have htrace : WordTrace (prefixWord ++ tailWord_1025635) baseStart_1025635 baseEnd_1025635 := by
    simpa [prefixWord, tailWord_1025635, baseEnd_1025635] using wordTrace_append hprefix tailTrace_1025635
  have hstable : (prefixWord ++ tailWord_1025635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025635).length < 2 ^ (prefixWord ++ tailWord_1025635).sum := by decide
  have hdescent : baseEnd_1025635 < baseStart_1025635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025666 : List Nat := [3, 4, 3, 10]
def baseStart_1025666 : Nat := 118140960795 + 1025666 * 2 ^ 59
def prefixEnd_1025666 : Nat := 4983230072969 + 3 ^ 40 * 1025666 * 2
def baseEnd_1025666 : Nat := 1926509918516650428013

theorem tailTrace_1025666 : CollatzResearch.WordTrace tailWord_1025666 prefixEnd_1025666 1926509918516650428013 := by
  unfold tailWord_1025666
  simp only [CollatzResearch.WordTrace]
  refine ⟨9352278075548681662982213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24939408201463151101285901 9352278075548681662982213)
  ·
    refine ⟨1753552139165377811809165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9352278075548681662982213 1753552139165377811809165)
    ·
      refine ⟨657582052187016679428437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1753552139165377811809165 657582052187016679428437)
      ·
        refine ⟨1926509918516650428013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 657582052187016679428437 1926509918516650428013)
        ·
          rfl

theorem cell20_1025666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 10].length) (baseStart_1025666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025666 prefixEnd_1025666 := by exact prefixLift 1025666
  have htrace : WordTrace (prefixWord ++ tailWord_1025666) baseStart_1025666 baseEnd_1025666 := by
    simpa [prefixWord, tailWord_1025666, baseEnd_1025666] using wordTrace_append hprefix tailTrace_1025666
  have hstable : (prefixWord ++ tailWord_1025666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025666).length < 2 ^ (prefixWord ++ tailWord_1025666).sum := by decide
  have hdescent : baseEnd_1025666 < baseStart_1025666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025672 : List Nat := [2, 1, 3, 5, 1, 2, 2, 2, 2]
def baseStart_1025672 : Nat := 118140960795 + 1025672 * 2 ^ 59
def prefixEnd_1025672 : Nat := 4983230072969 + 3 ^ 40 * 1025672 * 2
def baseEnd_1025672 : Nat := 468144648763036699807135

theorem tailTrace_1025672 : CollatzResearch.WordTrace tailWord_1025672 prefixEnd_1025672 468144648763036699807135 := by
  unfold tailWord_1025672
  simp only [CollatzResearch.WordTrace]
  refine ⟨18704665570086494838323635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24939554093448659784431513 18704665570086494838323635)
  ·
    refine ⟨28056998355129742257485453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18704665570086494838323635 28056998355129742257485453)
    ·
      refine ⟨10521374383173653346557045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28056998355129742257485453 10521374383173653346557045)
      ·
        refine ⟨986378848422530001239723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10521374383173653346557045 986378848422530001239723)
        ·
          refine ⟨1479568272633795001859585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986378848422530001239723 1479568272633795001859585)
          ·
            refine ⟨1109676204475346251394689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1479568272633795001859585 1109676204475346251394689)
            ·
              refine ⟨832257153356509688546017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1109676204475346251394689 832257153356509688546017)
              ·
                refine ⟨624192865017382266409513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 832257153356509688546017 624192865017382266409513)
                ·
                  refine ⟨468144648763036699807135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624192865017382266409513 468144648763036699807135)
                  ·
                    rfl

theorem cell20_1025672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 2].length) (baseStart_1025672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025672 prefixEnd_1025672 := by exact prefixLift 1025672
  have htrace : WordTrace (prefixWord ++ tailWord_1025672) baseStart_1025672 baseEnd_1025672 := by
    simpa [prefixWord, tailWord_1025672, baseEnd_1025672] using wordTrace_append hprefix tailTrace_1025672
  have hstable : (prefixWord ++ tailWord_1025672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025672).length < 2 ^ (prefixWord ++ tailWord_1025672).sum := by decide
  have hdescent : baseEnd_1025672 < baseStart_1025672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025687 : List Nat := [1, 1, 3, 3, 2, 2, 3, 5]
def baseStart_1025687 : Nat := 118140960795 + 1025687 * 2 ^ 59
def prefixEnd_1025687 : Nat := 4983230072969 + 3 ^ 40 * 1025687 * 2
def baseEnd_1025687 : Nat := 156050498390587771435691

theorem tailTrace_1025687 : CollatzResearch.WordTrace tailWord_1025687 prefixEnd_1025687 156050498390587771435691 := by
  unfold tailWord_1025687
  simp only [CollatzResearch.WordTrace]
  refine ⟨37409878235118647238443315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24939918823412431492295543 37409878235118647238443315)
  ·
    refine ⟨56114817352677970857664973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37409878235118647238443315 56114817352677970857664973)
    ·
      refine ⟨21043056507254239071624365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56114817352677970857664973 21043056507254239071624365)
      ·
        refine ⟨7891146190220339651859137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21043056507254239071624365 7891146190220339651859137)
        ·
          refine ⟨5918359642665254738894353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7891146190220339651859137 5918359642665254738894353)
          ·
            refine ⟨4438769731998941054170765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5918359642665254738894353 4438769731998941054170765)
            ·
              refine ⟨1664538649499602895314037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4438769731998941054170765 1664538649499602895314037)
              ·
                refine ⟨156050498390587771435691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1664538649499602895314037 156050498390587771435691)
                ·
                  rfl

theorem cell20_1025687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 5].length) (baseStart_1025687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025687 prefixEnd_1025687 := by exact prefixLift 1025687
  have htrace : WordTrace (prefixWord ++ tailWord_1025687) baseStart_1025687 baseEnd_1025687 := by
    simpa [prefixWord, tailWord_1025687, baseEnd_1025687] using wordTrace_append hprefix tailTrace_1025687
  have hstable : (prefixWord ++ tailWord_1025687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025687).length < 2 ^ (prefixWord ++ tailWord_1025687).sum := by decide
  have hdescent : baseEnd_1025687 < baseStart_1025687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025701 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 6]
def baseStart_1025701 : Nat := 118140960795 + 1025701 * 2 ^ 59
def prefixEnd_1025701 : Nat := 4983230072969 + 3 ^ 40 * 1025701 * 2
def baseEnd_1025701 : Nat := 468157885153241487840349

theorem tailTrace_1025701 : CollatzResearch.WordTrace tailWord_1025701 prefixEnd_1025701 468157885153241487840349 := by
  unfold tailWord_1025701
  simp only [CollatzResearch.WordTrace]
  refine ⟨37410388857067927629452957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24940259238045285086301971 37410388857067927629452957)
  ·
    refine ⟨14028895821400472861044859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37410388857067927629452957 14028895821400472861044859)
    ·
      refine ⟨21043343732100709291567289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14028895821400472861044859 21043343732100709291567289)
      ·
        refine ⟨15782507799075531968675467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21043343732100709291567289 15782507799075531968675467)
        ·
          refine ⟨23673761698613297953013201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15782507799075531968675467 23673761698613297953013201)
          ·
            refine ⟨17755321273959973464759901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23673761698613297953013201 17755321273959973464759901)
            ·
              refine ⟨6658245477734990049284963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17755321273959973464759901 6658245477734990049284963)
              ·
                refine ⟨9987368216602485073927445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6658245477734990049284963 9987368216602485073927445)
                ·
                  refine ⟨468157885153241487840349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9987368216602485073927445 468157885153241487840349)
                  ·
                    rfl

theorem cell20_1025701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_1025701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025701 prefixEnd_1025701 := by exact prefixLift 1025701
  have htrace : WordTrace (prefixWord ++ tailWord_1025701) baseStart_1025701 baseEnd_1025701 := by
    simpa [prefixWord, tailWord_1025701, baseEnd_1025701] using wordTrace_append hprefix tailTrace_1025701
  have hstable : (prefixWord ++ tailWord_1025701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025701).length < 2 ^ (prefixWord ++ tailWord_1025701).sum := by decide
  have hdescent : baseEnd_1025701 < baseStart_1025701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025770 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_1025770 : Nat := 118140960795 + 1025770 * 2 ^ 59
def prefixEnd_1025770 : Nat := 4983230072969 + 3 ^ 40 * 1025770 * 2
def baseEnd_1025770 : Nat := 468189378633383914540067

theorem tailTrace_1025770 : CollatzResearch.WordTrace tailWord_1025770 prefixEnd_1025770 468189378633383914540067 := by
  unfold tailWord_1025770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9353226373454488103428691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24941936995878634942476509 9353226373454488103428691)
  ·
    refine ⟨14029839560181732155143037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9353226373454488103428691 14029839560181732155143037)
    ·
      refine ⟨5261189835068149558178639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14029839560181732155143037 5261189835068149558178639)
      ·
        refine ⟨7891784752602224337267959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5261189835068149558178639 7891784752602224337267959)
        ·
          refine ⟨11837677128903336505901939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7891784752602224337267959 11837677128903336505901939)
          ·
            refine ⟨17756515693355004758852909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11837677128903336505901939 17756515693355004758852909)
            ·
              refine ⟨6658693385008126784569841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17756515693355004758852909 6658693385008126784569841)
              ·
                refine ⟨4994020038756095088427381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6658693385008126784569841 4994020038756095088427381)
                ·
                  refine ⟨468189378633383914540067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4994020038756095088427381 468189378633383914540067)
                  ·
                    rfl

theorem cell20_1025770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_1025770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025770 prefixEnd_1025770 := by exact prefixLift 1025770
  have htrace : WordTrace (prefixWord ++ tailWord_1025770) baseStart_1025770 baseEnd_1025770 := by
    simpa [prefixWord, tailWord_1025770, baseEnd_1025770] using wordTrace_append hprefix tailTrace_1025770
  have hstable : (prefixWord ++ tailWord_1025770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025770).length < 2 ^ (prefixWord ++ tailWord_1025770).sum := by decide
  have hdescent : baseEnd_1025770 < baseStart_1025770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025790 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_1025790 : Nat := 118140960795 + 1025790 * 2 ^ 59
def prefixEnd_1025790 : Nat := 4983230072969 + 3 ^ 40 * 1025790 * 2
def baseEnd_1025790 : Nat := 468198507178352733873319

theorem tailTrace_1025790 : CollatzResearch.WordTrace tailWord_1025790 prefixEnd_1025790 468198507178352733873319 := by
  unfold tailWord_1025790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4676704369218186978680353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24942423302496997219628549 4676704369218186978680353)
  ·
    refine ⟨3507528276913640234010265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4676704369218186978680353 3507528276913640234010265)
    ·
      refine ⟨2630646207685230175507699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3507528276913640234010265 2630646207685230175507699)
      ·
        refine ⟨3945969311527845263261549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2630646207685230175507699 3945969311527845263261549)
        ·
          refine ⟨1479738491822941973723081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3945969311527845263261549 1479738491822941973723081)
          ·
            refine ⟨1109803868867206480292311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1479738491822941973723081 1109803868867206480292311)
            ·
              refine ⟨1664705803300809720438467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109803868867206480292311 1664705803300809720438467)
              ·
                refine ⟨2497058704951214580657701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1664705803300809720438467 2497058704951214580657701)
                ·
                  refine ⟨468198507178352733873319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2497058704951214580657701 468198507178352733873319)
                  ·
                    rfl

theorem cell20_1025790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_1025790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025790 prefixEnd_1025790 := by exact prefixLift 1025790
  have htrace : WordTrace (prefixWord ++ tailWord_1025790) baseStart_1025790 baseEnd_1025790 := by
    simpa [prefixWord, tailWord_1025790, baseEnd_1025790] using wordTrace_append hprefix tailTrace_1025790
  have hstable : (prefixWord ++ tailWord_1025790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025790).length < 2 ^ (prefixWord ++ tailWord_1025790).sum := by decide
  have hdescent : baseEnd_1025790 < baseStart_1025790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025845 : List Nat := [1, 3, 3, 1, 4, 2, 2, 2, 2]
def baseStart_1025845 : Nat := 118140960795 + 1025845 * 2 ^ 59
def prefixEnd_1025845 : Nat := 4983230072969 + 3 ^ 40 * 1025845 * 2
def baseEnd_1025845 : Nat := 468223610677016987039761

theorem tailTrace_1025845 : CollatzResearch.WordTrace tailWord_1025845 prefixEnd_1025845 468223610677016987039761 := by
  unfold tailWord_1025845
  simp only [CollatzResearch.WordTrace]
  refine ⟨37415640968546240222694989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24943760645697493481796659 37415640968546240222694989)
  ·
    refine ⟨14030865363204840083510621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37415640968546240222694989 14030865363204840083510621)
    ·
      refine ⟨5261574511201815031316483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14030865363204840083510621 5261574511201815031316483)
      ·
        refine ⟨7892361766802722546974725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5261574511201815031316483 7892361766802722546974725)
        ·
          refine ⟨1479817831275510477557761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7892361766802722546974725 1479817831275510477557761)
          ·
            refine ⟨1109863373456632858168321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1479817831275510477557761 1109863373456632858168321)
            ·
              refine ⟨832397530092474643626241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1109863373456632858168321 832397530092474643626241)
              ·
                refine ⟨624298147569355982719681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 832397530092474643626241 624298147569355982719681)
                ·
                  refine ⟨468223610677016987039761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624298147569355982719681 468223610677016987039761)
                  ·
                    rfl

theorem cell20_1025845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_1025845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025845 prefixEnd_1025845 := by exact prefixLift 1025845
  have htrace : WordTrace (prefixWord ++ tailWord_1025845) baseStart_1025845 baseEnd_1025845 := by
    simpa [prefixWord, tailWord_1025845, baseEnd_1025845] using wordTrace_append hprefix tailTrace_1025845
  have hstable : (prefixWord ++ tailWord_1025845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025845).length < 2 ^ (prefixWord ++ tailWord_1025845).sum := by decide
  have hdescent : baseEnd_1025845 < baseStart_1025845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025887 : List Nat := [1, 1, 2, 3, 1, 5, 2, 3, 2]
def baseStart_1025887 : Nat := 118140960795 + 1025887 * 2 ^ 59
def prefixEnd_1025887 : Nat := 4983230072969 + 3 ^ 40 * 1025887 * 2
def baseEnd_1025887 : Nat := 468242780621451507639589

theorem tailTrace_1025887 : CollatzResearch.WordTrace tailWord_1025887 prefixEnd_1025887 468242780621451507639589 := by
  unfold tailWord_1025887
  simp only [CollatzResearch.WordTrace]
  refine ⟨37417172834394081395723915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24944781889596054263815943 37417172834394081395723915)
  ·
    refine ⟨56125759251591122093585873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37417172834394081395723915 56125759251591122093585873)
    ·
      refine ⟨42094319438693341570189405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56125759251591122093585873 42094319438693341570189405)
      ·
        refine ⟨15785369789510003088821027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42094319438693341570189405 15785369789510003088821027)
        ·
          refine ⟨23678054684265004633231541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15785369789510003088821027 23678054684265004633231541)
          ·
            refine ⟨2219817626649844184365457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23678054684265004633231541 2219817626649844184365457)
            ·
              refine ⟨1664863219987383138274093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2219817626649844184365457 1664863219987383138274093)
              ·
                refine ⟨624323707495268676852785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1664863219987383138274093 624323707495268676852785)
                ·
                  refine ⟨468242780621451507639589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624323707495268676852785 468242780621451507639589)
                  ·
                    rfl

theorem cell20_1025887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 2].length) (baseStart_1025887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025887 prefixEnd_1025887 := by exact prefixLift 1025887
  have htrace : WordTrace (prefixWord ++ tailWord_1025887) baseStart_1025887 baseEnd_1025887 := by
    simpa [prefixWord, tailWord_1025887, baseEnd_1025887] using wordTrace_append hprefix tailTrace_1025887
  have hstable : (prefixWord ++ tailWord_1025887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025887).length < 2 ^ (prefixWord ++ tailWord_1025887).sum := by decide
  have hdescent : baseEnd_1025887 < baseStart_1025887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025901 : List Nat := [1, 5, 1, 1, 1, 1, 5, 2, 3]
def baseStart_1025901 : Nat := 118140960795 + 1025901 * 2 ^ 59
def prefixEnd_1025901 : Nat := 4983230072969 + 3 ^ 40 * 1025901 * 2
def baseEnd_1025901 : Nat := 468249170602929681172865

theorem tailTrace_1025901 : CollatzResearch.WordTrace tailWord_1025901 prefixEnd_1025901 468249170602929681172865 := by
  unfold tailWord_1025901
  simp only [CollatzResearch.WordTrace]
  refine ⟨37417683456343361786733557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24945122304228907857822371 37417683456343361786733557)
  ·
    refine ⟨3507907824032190167506271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37417683456343361786733557 3507907824032190167506271)
    ·
      refine ⟨5261861736048285251259407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3507907824032190167506271 5261861736048285251259407)
      ·
        refine ⟨7892792604072427876889111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5261861736048285251259407 7892792604072427876889111)
        ·
          refine ⟨11839188906108641815333667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7892792604072427876889111 11839188906108641815333667)
          ·
            refine ⟨17758783359162962723000501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11839188906108641815333667 17758783359162962723000501)
            ·
              refine ⟨1664885939921527755281297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17758783359162962723000501 1664885939921527755281297)
              ·
                refine ⟨1248664454941145816460973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1664885939921527755281297 1248664454941145816460973)
                ·
                  refine ⟨468249170602929681172865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1248664454941145816460973 468249170602929681172865)
                  ·
                    rfl

theorem cell20_1025901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_1025901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025901 prefixEnd_1025901 := by exact prefixLift 1025901
  have htrace : WordTrace (prefixWord ++ tailWord_1025901) baseStart_1025901 baseEnd_1025901 := by
    simpa [prefixWord, tailWord_1025901, baseEnd_1025901] using wordTrace_append hprefix tailTrace_1025901
  have hstable : (prefixWord ++ tailWord_1025901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025901).length < 2 ^ (prefixWord ++ tailWord_1025901).sum := by decide
  have hdescent : baseEnd_1025901 < baseStart_1025901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025929 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 4]
def baseStart_1025929 : Nat := 118140960795 + 1025929 * 2 ^ 59
def prefixEnd_1025929 : Nat := 4983230072969 + 3 ^ 40 * 1025929 * 2
def baseEnd_1025929 : Nat := 468261950565886028239417

theorem tailTrace_1025929 : CollatzResearch.WordTrace tailWord_1025929 prefixEnd_1025929 468261950565886028239417 := by
  unfold tailWord_1025929
  simp only [CollatzResearch.WordTrace]
  refine ⟨37418704700241922568752841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24945803133494615045835227 37418704700241922568752841)
  ·
    refine ⟨28064028525181441926564631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37418704700241922568752841 28064028525181441926564631)
    ·
      refine ⟨42096042787772162889846947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28064028525181441926564631 42096042787772162889846947)
      ·
        refine ⟨63144064181658244334770421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42096042787772162889846947 63144064181658244334770421)
        ·
          refine ⟨5919756017030460406384727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63144064181658244334770421 5919756017030460406384727)
          ·
            refine ⟨8879634025545690609577091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5919756017030460406384727 8879634025545690609577091)
            ·
              refine ⟨13319451038318535914365637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8879634025545690609577091 13319451038318535914365637)
              ·
                refine ⟨2497397069684725483943557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13319451038318535914365637 2497397069684725483943557)
                ·
                  refine ⟨468261950565886028239417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2497397069684725483943557 468261950565886028239417)
                  ·
                    rfl

theorem cell20_1025929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_1025929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025929 prefixEnd_1025929 := by exact prefixLift 1025929
  have htrace : WordTrace (prefixWord ++ tailWord_1025929) baseStart_1025929 baseEnd_1025929 := by
    simpa [prefixWord, tailWord_1025929, baseEnd_1025929] using wordTrace_append hprefix tailTrace_1025929
  have hstable : (prefixWord ++ tailWord_1025929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025929).length < 2 ^ (prefixWord ++ tailWord_1025929).sum := by decide
  have hdescent : baseEnd_1025929 < baseStart_1025929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1025966 : List Nat := [4, 1, 5, 1, 1, 1, 2, 5]
def baseStart_1025966 : Nat := 118140960795 + 1025966 * 2 ^ 59
def prefixEnd_1025966 : Nat := 4983230072969 + 3 ^ 40 * 1025966 * 2
def baseEnd_1025966 : Nat := 156092946124692781335311

theorem tailTrace_1025966 : CollatzResearch.WordTrace tailWord_1025966 prefixEnd_1025966 156092946124692781335311 := by
  unfold tailWord_1025966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4677506775138484735981219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24946702800738585258566501 4677506775138484735981219)
  ·
    refine ⟨7016260162707727103971829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4677506775138484735981219 7016260162707727103971829)
    ·
      refine ⟨657774390253849415997359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7016260162707727103971829 657774390253849415997359)
      ·
        refine ⟨986661585380774123996039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657774390253849415997359 986661585380774123996039)
        ·
          refine ⟨1479992378071161185994059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986661585380774123996039 1479992378071161185994059)
          ·
            refine ⟨2219988567106741778991089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479992378071161185994059 2219988567106741778991089)
            ·
              refine ⟨1664991425330056334243317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2219988567106741778991089 1664991425330056334243317)
              ·
                refine ⟨156092946124692781335311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1664991425330056334243317 156092946124692781335311)
                ·
                  rfl

theorem cell20_1025966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_1025966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1025966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1025966 prefixEnd_1025966 := by exact prefixLift 1025966
  have htrace : WordTrace (prefixWord ++ tailWord_1025966) baseStart_1025966 baseEnd_1025966 := by
    simpa [prefixWord, tailWord_1025966, baseEnd_1025966] using wordTrace_append hprefix tailTrace_1025966
  have hstable : (prefixWord ++ tailWord_1025966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1025966).length < 2 ^ (prefixWord ++ tailWord_1025966).sum := by decide
  have hdescent : baseEnd_1025966 < baseStart_1025966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1025966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026015 : List Nat := [1, 1, 2, 3, 4, 2, 2, 2, 3]
def baseStart_1026015 : Nat := 118140960795 + 1026015 * 2 ^ 59
def prefixEnd_1026015 : Nat := 4983230072969 + 3 ^ 40 * 1026015 * 2
def baseEnd_1026015 : Nat := 468301203309251951372399

theorem tailTrace_1026015 : CollatzResearch.WordTrace tailWord_1026015 prefixEnd_1026015 468301203309251951372399 := by
  unfold tailWord_1026015
  simp only [CollatzResearch.WordTrace]
  refine ⟨37421841377930359256383499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24947894251953572837588999 37421841377930359256383499)
  ·
    refine ⟨56132762066895538884575249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37421841377930359256383499 56132762066895538884575249)
    ·
      refine ⟨42099571550171654163431437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56132762066895538884575249 42099571550171654163431437)
      ·
        refine ⟨15787339331314370311286789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42099571550171654163431437 15787339331314370311286789)
        ·
          refine ⟨2960126124621444433366273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15787339331314370311286789 2960126124621444433366273)
          ·
            refine ⟨2220094593466083325024705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2960126124621444433366273 2220094593466083325024705)
            ·
              refine ⟨1665070945099562493768529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2220094593466083325024705 1665070945099562493768529)
              ·
                refine ⟨1248803208824671870326397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665070945099562493768529 1248803208824671870326397)
                ·
                  refine ⟨468301203309251951372399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1248803208824671870326397 468301203309251951372399)
                  ·
                    rfl

theorem cell20_1026015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 3].length) (baseStart_1026015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026015 prefixEnd_1026015 := by exact prefixLift 1026015
  have htrace : WordTrace (prefixWord ++ tailWord_1026015) baseStart_1026015 baseEnd_1026015 := by
    simpa [prefixWord, tailWord_1026015, baseEnd_1026015] using wordTrace_append hprefix tailTrace_1026015
  have hstable : (prefixWord ++ tailWord_1026015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026015).length < 2 ^ (prefixWord ++ tailWord_1026015).sum := by decide
  have hdescent : baseEnd_1026015 < baseStart_1026015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026074 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_1026074 : Nat := 118140960795 + 1026074 * 2 ^ 59
def prefixEnd_1026074 : Nat := 4983230072969 + 3 ^ 40 * 1026074 * 2
def baseEnd_1026074 : Nat := 468328132516909968405491

theorem tailTrace_1026074 : CollatzResearch.WordTrace tailWord_1026074 prefixEnd_1026074 468328132516909968405491 := by
  unfold tailWord_1026074
  simp only [CollatzResearch.WordTrace]
  refine ⟨9355998321179153083195319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24949328856477741555187517 9355998321179153083195319)
  ·
    refine ⟨14033997481768729624792979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9355998321179153083195319 14033997481768729624792979)
    ·
      refine ⟨21050996222653094437189469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14033997481768729624792979 21050996222653094437189469)
      ·
        refine ⟨7894123583494910413946051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21050996222653094437189469 7894123583494910413946051)
        ·
          refine ⟨11841185375242365620919077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7894123583494910413946051 11841185375242365620919077)
          ·
            refine ⟨2220222257857943553922327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11841185375242365620919077 2220222257857943553922327)
            ·
              refine ⟨3330333386786915330883491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220222257857943553922327 3330333386786915330883491)
              ·
                refine ⟨4995500080180372996325237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3330333386786915330883491 4995500080180372996325237)
                ·
                  refine ⟨468328132516909968405491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4995500080180372996325237 468328132516909968405491)
                  ·
                    rfl

theorem cell20_1026074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_1026074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026074 prefixEnd_1026074 := by exact prefixLift 1026074
  have htrace : WordTrace (prefixWord ++ tailWord_1026074) baseStart_1026074 baseEnd_1026074 := by
    simpa [prefixWord, tailWord_1026074, baseEnd_1026074] using wordTrace_append hprefix tailTrace_1026074
  have hstable : (prefixWord ++ tailWord_1026074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026074).length < 2 ^ (prefixWord ++ tailWord_1026074).sum := by decide
  have hdescent : baseEnd_1026074 < baseStart_1026074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026077 : List Nat := [1, 4, 2, 2, 2, 1, 2, 4, 2]
def baseStart_1026077 : Nat := 118140960795 + 1026077 * 2 ^ 59
def prefixEnd_1026077 : Nat := 4983230072969 + 3 ^ 40 * 1026077 * 2
def baseEnd_1026077 : Nat := 468329501798655291305479

theorem tailTrace_1026077 : CollatzResearch.WordTrace tailWord_1026077 prefixEnd_1026077 468329501798655291305479 := by
  unfold tailWord_1026077
  simp only [CollatzResearch.WordTrace]
  refine ⟨37424102703705743845140485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24949401802470495896760323 37424102703705743845140485)
  ·
    refine ⟨7017019256944826970963841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37424102703705743845140485 7017019256944826970963841)
    ·
      refine ⟨5262764442708620228222881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7017019256944826970963841 5262764442708620228222881)
      ·
        refine ⟨3947073332031465171167161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5262764442708620228222881 3947073332031465171167161)
        ·
          refine ⟨2960304999023598878375371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3947073332031465171167161 2960304999023598878375371)
          ·
            refine ⟨4440457498535398317563057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2960304999023598878375371 4440457498535398317563057)
            ·
              refine ⟨3330343123901548738172293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4440457498535398317563057 3330343123901548738172293)
              ·
                refine ⟨624439335731540388407305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3330343123901548738172293 624439335731540388407305)
                ·
                  refine ⟨468329501798655291305479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624439335731540388407305 468329501798655291305479)
                  ·
                    rfl

theorem cell20_1026077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_1026077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026077 prefixEnd_1026077 := by exact prefixLift 1026077
  have htrace : WordTrace (prefixWord ++ tailWord_1026077) baseStart_1026077 baseEnd_1026077 := by
    simpa [prefixWord, tailWord_1026077, baseEnd_1026077] using wordTrace_append hprefix tailTrace_1026077
  have hstable : (prefixWord ++ tailWord_1026077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026077).length < 2 ^ (prefixWord ++ tailWord_1026077).sum := by decide
  have hdescent : baseEnd_1026077 < baseStart_1026077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026087 : List Nat := [1, 1, 7, 1, 2, 1, 3, 1, 3]
def baseStart_1026087 : Nat := 118140960795 + 1026087 * 2 ^ 59
def prefixEnd_1026087 : Nat := 4983230072969 + 3 ^ 40 * 1026087 * 2
def baseEnd_1026087 : Nat := 468334066071139700972105

theorem tailTrace_1026087 : CollatzResearch.WordTrace tailWord_1026087 prefixEnd_1026087 468334066071139700972105 := by
  unfold tailWord_1026087
  simp only [CollatzResearch.WordTrace]
  refine ⟨37424467433669515553004515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24949644955779677035336343 37424467433669515553004515)
  ·
    refine ⟨56136701150504273329506773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37424467433669515553004515 56136701150504273329506773)
    ·
      refine ⟨1315703933214943906160315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 56136701150504273329506773 1315703933214943906160315)
      ·
        refine ⟨1973555899822415859240473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1315703933214943906160315 1973555899822415859240473)
        ·
          refine ⟨1480166924866811894430355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1973555899822415859240473 1480166924866811894430355)
          ·
            refine ⟨2220250387300217841645533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480166924866811894430355 2220250387300217841645533)
            ·
              refine ⟨832593895237581690617075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2220250387300217841645533 832593895237581690617075)
              ·
                refine ⟨1248890842856372535925613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832593895237581690617075 1248890842856372535925613)
                ·
                  refine ⟨468334066071139700972105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1248890842856372535925613 468334066071139700972105)
                  ·
                    rfl

theorem cell20_1026087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 3].length) (baseStart_1026087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026087 prefixEnd_1026087 := by exact prefixLift 1026087
  have htrace : WordTrace (prefixWord ++ tailWord_1026087) baseStart_1026087 baseEnd_1026087 := by
    simpa [prefixWord, tailWord_1026087, baseEnd_1026087] using wordTrace_append hprefix tailTrace_1026087
  have hstable : (prefixWord ++ tailWord_1026087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026087).length < 2 ^ (prefixWord ++ tailWord_1026087).sum := by decide
  have hdescent : baseEnd_1026087 < baseStart_1026087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026105 : List Nat := [1, 2, 1, 5, 3, 1, 1, 6]
def baseStart_1026105 : Nat := 118140960795 + 1026105 * 2 ^ 59
def prefixEnd_1026105 : Nat := 4983230072969 + 3 ^ 40 * 1026105 * 2
def baseEnd_1026105 : Nat := 156114093920537212790677

theorem tailTrace_1026105 : CollatzResearch.WordTrace tailWord_1026105 prefixEnd_1026105 156114093920537212790677 := by
  unfold tailWord_1026105
  simp only [CollatzResearch.WordTrace]
  refine ⟨37425123947604304627159769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24950082631736203084773179 37425123947604304627159769)
  ·
    refine ⟨28068842960703228470369827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37425123947604304627159769 28068842960703228470369827)
    ·
      refine ⟨42103264441054842705554741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28068842960703228470369827 42103264441054842705554741)
      ·
        refine ⟨3947181041348891503645757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42103264441054842705554741 3947181041348891503645757)
        ·
          refine ⟨1480192890505834313867159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3947181041348891503645757 1480192890505834313867159)
          ·
            refine ⟨2220289335758751470800739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480192890505834313867159 2220289335758751470800739)
            ·
              refine ⟨3330434003638127206201109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220289335758751470800739 3330434003638127206201109)
              ·
                refine ⟨156114093920537212790677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3330434003638127206201109 156114093920537212790677)
                ·
                  rfl

theorem cell20_1026105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 6].length) (baseStart_1026105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026105 prefixEnd_1026105 := by exact prefixLift 1026105
  have htrace : WordTrace (prefixWord ++ tailWord_1026105) baseStart_1026105 baseEnd_1026105 := by
    simpa [prefixWord, tailWord_1026105, baseEnd_1026105] using wordTrace_append hprefix tailTrace_1026105
  have hstable : (prefixWord ++ tailWord_1026105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026105).length < 2 ^ (prefixWord ++ tailWord_1026105).sum := by decide
  have hdescent : baseEnd_1026105 < baseStart_1026105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026126 : List Nat := [4, 1, 1, 1, 1, 4, 8]
def baseStart_1026126 : Nat := 118140960795 + 1026126 * 2 ^ 59
def prefixEnd_1026126 : Nat := 4983230072969 + 3 ^ 40 * 1026126 * 2
def baseEnd_1026126 : Nat := 52039096303758766519105

theorem tailTrace_1026126 : CollatzResearch.WordTrace tailWord_1026126 prefixEnd_1026126 52039096303758766519105 := by
  unfold tailWord_1026126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4678236235066028151709279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24950593253685483475782821 4678236235066028151709279)
  ·
    refine ⟨7017354352599042227563919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4678236235066028151709279 7017354352599042227563919)
    ·
      refine ⟨10526031528898563341345879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7017354352599042227563919 10526031528898563341345879)
      ·
        refine ⟨15789047293347845012018819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10526031528898563341345879 15789047293347845012018819)
        ·
          refine ⟨23683570940021767518028229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15789047293347845012018819 23683570940021767518028229)
          ·
            refine ⟨4440669551254081409630293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23683570940021767518028229 4440669551254081409630293)
            ·
              refine ⟨52039096303758766519105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4440669551254081409630293 52039096303758766519105)
              ·
                rfl

theorem cell20_1026126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 8].length) (baseStart_1026126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026126 prefixEnd_1026126 := by exact prefixLift 1026126
  have htrace : WordTrace (prefixWord ++ tailWord_1026126) baseStart_1026126 baseEnd_1026126 := by
    simpa [prefixWord, tailWord_1026126, baseEnd_1026126] using wordTrace_append hprefix tailTrace_1026126
  have hstable : (prefixWord ++ tailWord_1026126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026126).length < 2 ^ (prefixWord ++ tailWord_1026126).sum := by decide
  have hdescent : baseEnd_1026126 < baseStart_1026126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026136 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 4]
def baseStart_1026136 : Nat := 118140960795 + 1026136 * 2 ^ 59
def prefixEnd_1026136 : Nat := 4983230072969 + 3 ^ 40 * 1026136 * 2
def baseEnd_1026136 : Nat := 468356431006313308338571

theorem tailTrace_1026136 : CollatzResearch.WordTrace tailWord_1026136 prefixEnd_1026136 468356431006313308338571 := by
  unfold tailWord_1026136
  simp only [CollatzResearch.WordTrace]
  refine ⟨18713127305245998460769131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24950836406994664614358841 18713127305245998460769131)
  ·
    refine ⟨28069690957868997691153697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18713127305245998460769131 28069690957868997691153697)
    ·
      refine ⟨21052268218401748268365273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28069690957868997691153697 21052268218401748268365273)
      ·
        refine ⟨15789201163801311201273955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21052268218401748268365273 15789201163801311201273955)
        ·
          refine ⟨23683801745701966801910933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15789201163801311201273955 23683801745701966801910933)
          ·
            refine ⟨1110178206829779693839575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23683801745701966801910933 1110178206829779693839575)
            ·
              refine ⟨1665267310244669540759363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110178206829779693839575 1665267310244669540759363)
              ·
                refine ⟨2497900965367004311139045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1665267310244669540759363 2497900965367004311139045)
                ·
                  refine ⟨468356431006313308338571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2497900965367004311139045 468356431006313308338571)
                  ·
                    rfl

theorem cell20_1026136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_1026136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026136 prefixEnd_1026136 := by exact prefixLift 1026136
  have htrace : WordTrace (prefixWord ++ tailWord_1026136) baseStart_1026136 baseEnd_1026136 := by
    simpa [prefixWord, tailWord_1026136, baseEnd_1026136] using wordTrace_append hprefix tailTrace_1026136
  have hstable : (prefixWord ++ tailWord_1026136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026136).length < 2 ^ (prefixWord ++ tailWord_1026136).sum := by decide
  have hdescent : baseEnd_1026136 < baseStart_1026136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026146 : List Nat := [3, 3, 2, 2, 2, 1, 1, 3, 3]
def baseStart_1026146 : Nat := 118140960795 + 1026146 * 2 ^ 59
def prefixEnd_1026146 : Nat := 4983230072969 + 3 ^ 40 * 1026146 * 2
def baseEnd_1026146 : Nat := 468360995278797718005197

theorem tailTrace_1026146 : CollatzResearch.WordTrace tailWord_1026146 prefixEnd_1026146 468360995278797718005197 := by
  unfold tailWord_1026146
  simp only [CollatzResearch.WordTrace]
  refine ⟨9356654835113942157350573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24951079560303845752934861 9356654835113942157350573)
  ·
    refine ⟨3508745563167728309006465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9356654835113942157350573 3508745563167728309006465)
    ·
      refine ⟨2631559172375796231754849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3508745563167728309006465 2631559172375796231754849)
      ·
        refine ⟨1973669379281847173816137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2631559172375796231754849 1973669379281847173816137)
        ·
          refine ⟨1480252034461385380362103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1973669379281847173816137 1480252034461385380362103)
          ·
            refine ⟨2220378051692078070543155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480252034461385380362103 2220378051692078070543155)
            ·
              refine ⟨3330567077538117105814733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220378051692078070543155 3330567077538117105814733)
              ·
                refine ⟨1248962654076793914680525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3330567077538117105814733 1248962654076793914680525)
                ·
                  refine ⟨468360995278797718005197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1248962654076793914680525 468360995278797718005197)
                  ·
                    rfl

theorem cell20_1026146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_1026146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026146 prefixEnd_1026146 := by exact prefixLift 1026146
  have htrace : WordTrace (prefixWord ++ tailWord_1026146) baseStart_1026146 baseEnd_1026146 := by
    simpa [prefixWord, tailWord_1026146, baseEnd_1026146] using wordTrace_append hprefix tailTrace_1026146
  have hstable : (prefixWord ++ tailWord_1026146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026146).length < 2 ^ (prefixWord ++ tailWord_1026146).sum := by decide
  have hdescent : baseEnd_1026146 < baseStart_1026146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026157 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1026157 : Nat := 118140960795 + 1026157 * 2 ^ 59
def prefixEnd_1026157 : Nat := 4983230072969 + 3 ^ 40 * 1026157 * 2
def baseEnd_1026157 : Nat := 468366015978530568638485

theorem tailTrace_1026157 : CollatzResearch.WordTrace tailWord_1026157 prefixEnd_1026157 468366015978530568638485 := by
  unfold tailWord_1026157
  simp only [CollatzResearch.WordTrace]
  refine ⟨37427020543415917508052725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24951347028943945005368483 37427020543415917508052725)
  ·
    refine ⟨3508783175945242266379943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37427020543415917508052725 3508783175945242266379943)
    ·
      refine ⟨5263174763917863399569915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3508783175945242266379943 5263174763917863399569915)
      ·
        refine ⟨7894762145876795099354873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5263174763917863399569915 7894762145876795099354873)
        ·
          refine ⟨5921071609407596324516155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7894762145876795099354873 5921071609407596324516155)
          ·
            refine ⟨8881607414111394486774233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5921071609407596324516155 8881607414111394486774233)
            ·
              refine ⟨6661205560583545865080675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8881607414111394486774233 6661205560583545865080675)
              ·
                refine ⟨9991808340875318797621013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6661205560583545865080675 9991808340875318797621013)
                ·
                  refine ⟨468366015978530568638485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9991808340875318797621013 468366015978530568638485)
                  ·
                    rfl

theorem cell20_1026157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1026157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026157 prefixEnd_1026157 := by exact prefixLift 1026157
  have htrace : WordTrace (prefixWord ++ tailWord_1026157) baseStart_1026157 baseEnd_1026157 := by
    simpa [prefixWord, tailWord_1026157, baseEnd_1026157] using wordTrace_append hprefix tailTrace_1026157
  have hstable : (prefixWord ++ tailWord_1026157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026157).length < 2 ^ (prefixWord ++ tailWord_1026157).sum := by decide
  have hdescent : baseEnd_1026157 < baseStart_1026157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026212 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 4]
def baseStart_1026212 : Nat := 118140960795 + 1026212 * 2 ^ 59
def prefixEnd_1026212 : Nat := 4983230072969 + 3 ^ 40 * 1026212 * 2
def baseEnd_1026212 : Nat := 468391119477194821804927

theorem tailTrace_1026212 : CollatzResearch.WordTrace tailWord_1026212 prefixEnd_1026212 468391119477194821804927 := by
  unfold tailWord_1026212
  simp only [CollatzResearch.WordTrace]
  refine ⟨18714513279108330950652445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24952684372144441267536593 18714513279108330950652445)
  ·
    refine ⟨7017942479665624106494667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18714513279108330950652445 7017942479665624106494667)
    ·
      refine ⟨10526913719498436159742001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7017942479665624106494667 10526913719498436159742001)
      ·
        refine ⟨7895185289623827119806501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10526913719498436159742001 7895185289623827119806501)
        ·
          refine ⟨1480347241804467584963719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7895185289623827119806501 1480347241804467584963719)
          ·
            refine ⟨2220520862706701377445579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480347241804467584963719 2220520862706701377445579)
            ·
              refine ⟨3330781294060052066168369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220520862706701377445579 3330781294060052066168369)
              ·
                refine ⟨2498085970545039049626277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3330781294060052066168369 2498085970545039049626277)
                ·
                  refine ⟨468391119477194821804927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2498085970545039049626277 468391119477194821804927)
                  ·
                    rfl

theorem cell20_1026212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_1026212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026212 prefixEnd_1026212 := by exact prefixLift 1026212
  have htrace : WordTrace (prefixWord ++ tailWord_1026212) baseStart_1026212 baseEnd_1026212 := by
    simpa [prefixWord, tailWord_1026212, baseEnd_1026212] using wordTrace_append hprefix tailTrace_1026212
  have hstable : (prefixWord ++ tailWord_1026212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026212).length < 2 ^ (prefixWord ++ tailWord_1026212).sum := by decide
  have hdescent : baseEnd_1026212 < baseStart_1026212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026240 : List Nat := [2, 1, 1, 2, 5, 2, 7]
def baseStart_1026240 : Nat := 118140960795 + 1026240 * 2 ^ 59
def prefixEnd_1026240 : Nat := 4983230072969 + 3 ^ 40 * 1026240 * 2
def baseEnd_1026240 : Nat := 52044877715572352096831

theorem tailTrace_1026240 : CollatzResearch.WordTrace tailWord_1026240 prefixEnd_1026240 52044877715572352096831 := by
  unfold tailWord_1026240
  simp only [CollatzResearch.WordTrace]
  refine ⟨18715023901057611341662087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24953365201410148455549449 18715023901057611341662087)
  ·
    refine ⟨28072535851586417012493131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18715023901057611341662087 28072535851586417012493131)
    ·
      refine ⟨42108803777379625518739697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28072535851586417012493131 42108803777379625518739697)
      ·
        refine ⟨31581602833034719139054773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42108803777379625518739697 31581602833034719139054773)
        ·
          refine ⟨2960775265597004919286385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31581602833034719139054773 2960775265597004919286385)
          ·
            refine ⟨2220581449197753689464789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2960775265597004919286385 2220581449197753689464789)
            ·
              refine ⟨52044877715572352096831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2220581449197753689464789 52044877715572352096831)
              ·
                rfl

theorem cell20_1026240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 7].length) (baseStart_1026240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026240 prefixEnd_1026240 := by exact prefixLift 1026240
  have htrace : WordTrace (prefixWord ++ tailWord_1026240) baseStart_1026240 baseEnd_1026240 := by
    simpa [prefixWord, tailWord_1026240, baseEnd_1026240] using wordTrace_append hprefix tailTrace_1026240
  have hstable : (prefixWord ++ tailWord_1026240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026240).length < 2 ^ (prefixWord ++ tailWord_1026240).sum := by decide
  have hdescent : baseEnd_1026240 < baseStart_1026240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026250 : List Nat := [3, 1, 2, 1, 3, 1, 1, 6, 2]
def baseStart_1026250 : Nat := 118140960795 + 1026250 * 2 ^ 59
def prefixEnd_1026250 : Nat := 4983230072969 + 3 ^ 40 * 1026250 * 2
def baseEnd_1026250 : Nat := 468408463712635578538105

theorem tailTrace_1026250 : CollatzResearch.WordTrace tailWord_1026250 prefixEnd_1026250 468408463712635578538105 := by
  unfold tailWord_1026250
  simp only [CollatzResearch.WordTrace]
  refine ⟨9357603133019748597797051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24953608354719329594125469 9357603133019748597797051)
  ·
    refine ⟨14036404699529622896695577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9357603133019748597797051 14036404699529622896695577)
    ·
      refine ⟨10527303524647217172521683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14036404699529622896695577 10527303524647217172521683)
      ·
        refine ⟨15790955286970825758782525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10527303524647217172521683 15790955286970825758782525)
        ·
          refine ⟨5921608232614059659543447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15790955286970825758782525 5921608232614059659543447)
          ·
            refine ⟨8882412348921089489315171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5921608232614059659543447 8882412348921089489315171)
            ·
              refine ⟨13323618523381634233972757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8882412348921089489315171 13323618523381634233972757)
              ·
                refine ⟨624544618283514104717473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13323618523381634233972757 624544618283514104717473)
                ·
                  refine ⟨468408463712635578538105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624544618283514104717473 468408463712635578538105)
                  ·
                    rfl

theorem cell20_1026250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_1026250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026250 prefixEnd_1026250 := by exact prefixLift 1026250
  have htrace : WordTrace (prefixWord ++ tailWord_1026250) baseStart_1026250 baseEnd_1026250 := by
    simpa [prefixWord, tailWord_1026250, baseEnd_1026250] using wordTrace_append hprefix tailTrace_1026250
  have hstable : (prefixWord ++ tailWord_1026250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026250).length < 2 ^ (prefixWord ++ tailWord_1026250).sum := by decide
  have hdescent : baseEnd_1026250 < baseStart_1026250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026302 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1026302 : Nat := 118140960795 + 1026302 * 2 ^ 59
def prefixEnd_1026302 : Nat := 4983230072969 + 3 ^ 40 * 1026302 * 2
def baseEnd_1026302 : Nat := 468432197929554508804559

theorem tailTrace_1026302 : CollatzResearch.WordTrace tailWord_1026302 prefixEnd_1026302 468432197929554508804559 := by
  unfold tailWord_1026302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4679038640986325909010145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24954872751927071514720773 4679038640986325909010145)
  ·
    refine ⟨3509278980739744431757609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4679038640986325909010145 3509278980739744431757609)
    ·
      refine ⟨2631959235554808323818207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3509278980739744431757609 2631959235554808323818207)
      ·
        refine ⟨3947938853332212485727311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2631959235554808323818207 3947938853332212485727311)
        ·
          refine ⟨5921908279998318728590967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3947938853332212485727311 5921908279998318728590967)
          ·
            refine ⟨8882862419997478092886451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5921908279998318728590967 8882862419997478092886451)
            ·
              refine ⟨13324293629996217139329677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8882862419997478092886451 13324293629996217139329677)
              ·
                refine ⟨4996610111248581427248629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13324293629996217139329677 4996610111248581427248629)
                ·
                  refine ⟨468432197929554508804559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4996610111248581427248629 468432197929554508804559)
                  ·
                    rfl

theorem cell20_1026302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1026302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026302 prefixEnd_1026302 := by exact prefixLift 1026302
  have htrace : WordTrace (prefixWord ++ tailWord_1026302) baseStart_1026302 baseEnd_1026302 := by
    simpa [prefixWord, tailWord_1026302, baseEnd_1026302] using wordTrace_append hprefix tailTrace_1026302
  have hstable : (prefixWord ++ tailWord_1026302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026302).length < 2 ^ (prefixWord ++ tailWord_1026302).sum := by decide
  have hdescent : baseEnd_1026302 < baseStart_1026302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026305 : List Nat := [1, 2, 4, 1, 1, 2, 5, 2, 2]
def baseStart_1026305 : Nat := 118140960795 + 1026305 * 2 ^ 59
def prefixEnd_1026305 : Nat := 4983230072969 + 3 ^ 40 * 1026305 * 2
def baseEnd_1026305 : Nat := 468433567211299831704547

theorem tailTrace_1026305 : CollatzResearch.WordTrace tailWord_1026305 prefixEnd_1026305 468433567211299831704547 := by
  unfold tailWord_1026305
  simp only [CollatzResearch.WordTrace]
  refine ⟨37432418546879738784440369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24954945697919825856293579 37432418546879738784440369)
  ·
    refine ⟨28074313910159804088330277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37432418546879738784440369 28074313910159804088330277)
    ·
      refine ⟨5263933858154963266561927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28074313910159804088330277 5263933858154963266561927)
      ·
        refine ⟨7895900787232444899842891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5263933858154963266561927 7895900787232444899842891)
        ·
          refine ⟨11843851180848667349764337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7895900787232444899842891 11843851180848667349764337)
          ·
            refine ⟨8882888385636500512323253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11843851180848667349764337 8882888385636500512323253)
            ·
              refine ⟨832770786153421923030305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8882888385636500512323253 832770786153421923030305)
              ·
                refine ⟨624578089615066442272729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 832770786153421923030305 624578089615066442272729)
                ·
                  refine ⟨468433567211299831704547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624578089615066442272729 468433567211299831704547)
                  ·
                    rfl

theorem cell20_1026305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 2].length) (baseStart_1026305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026305 prefixEnd_1026305 := by exact prefixLift 1026305
  have htrace : WordTrace (prefixWord ++ tailWord_1026305) baseStart_1026305 baseEnd_1026305 := by
    simpa [prefixWord, tailWord_1026305, baseEnd_1026305] using wordTrace_append hprefix tailTrace_1026305
  have hstable : (prefixWord ++ tailWord_1026305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026305).length < 2 ^ (prefixWord ++ tailWord_1026305).sum := by decide
  have hdescent : baseEnd_1026305 < baseStart_1026305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026316 : List Nat := [2, 2, 1, 2, 2, 2, 4, 5]
def baseStart_1026316 : Nat := 118140960795 + 1026316 * 2 ^ 59
def prefixEnd_1026316 : Nat := 4983230072969 + 3 ^ 40 * 1026316 * 2
def baseEnd_1026316 : Nat := 156146195970344227445945

theorem tailTrace_1026316 : CollatzResearch.WordTrace tailWord_1026316 prefixEnd_1026316 156146195970344227445945 := by
  unfold tailWord_1026316
  simp only [CollatzResearch.WordTrace]
  refine ⟨18716409874919943831545401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24955213166559925108727201 18716409874919943831545401)
  ·
    refine ⟨14037307406189957873659051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18716409874919943831545401 14037307406189957873659051)
    ·
      refine ⟨21055961109284936810488577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14037307406189957873659051 21055961109284936810488577)
      ·
        refine ⟨15791970831963702607866433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21055961109284936810488577 15791970831963702607866433)
        ·
          refine ⟨11843978123972776955899825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15791970831963702607866433 11843978123972776955899825)
          ·
            refine ⟨8882983592979582716924869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11843978123972776955899825 8882983592979582716924869)
            ·
              refine ⟨1665559423683671759423413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8882983592979582716924869 1665559423683671759423413)
              ·
                refine ⟨156146195970344227445945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1665559423683671759423413 156146195970344227445945)
                ·
                  rfl

theorem cell20_1026316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_1026316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026316 prefixEnd_1026316 := by exact prefixLift 1026316
  have htrace : WordTrace (prefixWord ++ tailWord_1026316) baseStart_1026316 baseEnd_1026316 := by
    simpa [prefixWord, tailWord_1026316, baseEnd_1026316] using wordTrace_append hprefix tailTrace_1026316
  have hstable : (prefixWord ++ tailWord_1026316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026316).length < 2 ^ (prefixWord ++ tailWord_1026316).sum := by decide
  have hdescent : baseEnd_1026316 < baseStart_1026316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026350 : List Nat := [4, 1, 3, 3, 2, 7]
def baseStart_1026350 : Nat := 118140960795 + 1026350 * 2 ^ 59
def prefixEnd_1026350 : Nat := 4983230072969 + 3 ^ 40 * 1026350 * 2
def baseEnd_1026350 : Nat := 17350152090277025007569

theorem tailTrace_1026350 : CollatzResearch.WordTrace tailWord_1026350 prefixEnd_1026350 17350152090277025007569 := by
  unfold tailWord_1026350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4679257478964588933728563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24956039887811140979885669 4679257478964588933728563)
  ·
    refine ⟨7018886218446883400592845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4679257478964588933728563 7018886218446883400592845)
    ·
      refine ⟨2632082331917581275222317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7018886218446883400592845 2632082331917581275222317)
      ·
        refine ⟨987030874469092978208369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2632082331917581275222317 987030874469092978208369)
        ·
          refine ⟨740273155851819733656277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987030874469092978208369 740273155851819733656277)
          ·
            refine ⟨17350152090277025007569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 740273155851819733656277 17350152090277025007569)
            ·
              rfl

theorem cell20_1026350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 7].length) (baseStart_1026350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026350 prefixEnd_1026350 := by exact prefixLift 1026350
  have htrace : WordTrace (prefixWord ++ tailWord_1026350) baseStart_1026350 baseEnd_1026350 := by
    simpa [prefixWord, tailWord_1026350, baseEnd_1026350] using wordTrace_append hprefix tailTrace_1026350
  have hstable : (prefixWord ++ tailWord_1026350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026350).length < 2 ^ (prefixWord ++ tailWord_1026350).sum := by decide
  have hdescent : baseEnd_1026350 < baseStart_1026350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026354 : List Nat := [3, 2, 1, 1, 5, 8]
def baseStart_1026354 : Nat := 118140960795 + 1026354 * 2 ^ 59
def prefixEnd_1026354 : Nat := 4983230072969 + 3 ^ 40 * 1026354 * 2
def baseEnd_1026354 : Nat := 17350219709128645891519

theorem tailTrace_1026354 : CollatzResearch.WordTrace tailWord_1026354 prefixEnd_1026354 17350219709128645891519 := by
  unfold tailWord_1026354
  simp only [CollatzResearch.WordTrace]
  refine ⟨9358551430925555038243529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24956137149134813435316077 9358551430925555038243529)
  ·
    refine ⟨7018913573194166278682647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9358551430925555038243529 7018913573194166278682647)
    ·
      refine ⟨10528370359791249418023971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7018913573194166278682647 10528370359791249418023971)
      ·
        refine ⟨15792555539686874127035957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10528370359791249418023971 15792555539686874127035957)
        ·
          refine ⟨1480552081845644449409621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15792555539686874127035957 1480552081845644449409621)
          ·
            refine ⟨17350219709128645891519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1480552081845644449409621 17350219709128645891519)
            ·
              rfl

theorem cell20_1026354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 8].length) (baseStart_1026354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026354 prefixEnd_1026354 := by exact prefixLift 1026354
  have htrace : WordTrace (prefixWord ++ tailWord_1026354) baseStart_1026354 baseEnd_1026354 := by
    simpa [prefixWord, tailWord_1026354, baseEnd_1026354] using wordTrace_append hprefix tailTrace_1026354
  have hstable : (prefixWord ++ tailWord_1026354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026354).length < 2 ^ (prefixWord ++ tailWord_1026354).sum := by decide
  have hdescent : baseEnd_1026354 < baseStart_1026354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026364 : List Nat := [2, 2, 2, 2, 1, 2, 3, 4, 2]
def baseStart_1026364 : Nat := 118140960795 + 1026364 * 2 ^ 59
def prefixEnd_1026364 : Nat := 4983230072969 + 3 ^ 40 * 1026364 * 2
def baseEnd_1026364 : Nat := 468460496418957848737639

theorem tailTrace_1026364 : CollatzResearch.WordTrace tailWord_1026364 prefixEnd_1026364 468460496418957848737639 := by
  unfold tailWord_1026364
  simp only [CollatzResearch.WordTrace]
  refine ⟨18717285226832995930419073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24956380302443994573892097 18717285226832995930419073)
  ·
    refine ⟨14037963920124746947814305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18717285226832995930419073 14037963920124746947814305)
    ·
      refine ⟨10528472940093560210860729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14037963920124746947814305 10528472940093560210860729)
      ·
        refine ⟨7896354705070170158145547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10528472940093560210860729 7896354705070170158145547)
        ·
          refine ⟨11844532057605255237218321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7896354705070170158145547 11844532057605255237218321)
          ·
            refine ⟨8883399043203941427913741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11844532057605255237218321 8883399043203941427913741)
            ·
              refine ⟨3331274641201478035467653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8883399043203941427913741 3331274641201478035467653)
              ·
                refine ⟨624613995225277131650185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3331274641201478035467653 624613995225277131650185)
                ·
                  refine ⟨468460496418957848737639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624613995225277131650185 468460496418957848737639)
                  ·
                    rfl

theorem cell20_1026364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_1026364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026364 prefixEnd_1026364 := by exact prefixLift 1026364
  have htrace : WordTrace (prefixWord ++ tailWord_1026364) baseStart_1026364 baseEnd_1026364 := by
    simpa [prefixWord, tailWord_1026364, baseEnd_1026364] using wordTrace_append hprefix tailTrace_1026364
  have hstable : (prefixWord ++ tailWord_1026364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026364).length < 2 ^ (prefixWord ++ tailWord_1026364).sum := by decide
  have hdescent : baseEnd_1026364 < baseStart_1026364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026385 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 4]
def baseStart_1026385 : Nat := 118140960795 + 1026385 * 2 ^ 59
def prefixEnd_1026385 : Nat := 4983230072969 + 3 ^ 40 * 1026385 * 2
def baseEnd_1026385 : Nat := 468470081391175109037553

theorem tailTrace_1026385 : CollatzResearch.WordTrace tailWord_1026385 prefixEnd_1026385 468470081391175109037553 := by
  unfold tailWord_1026385
  simp only [CollatzResearch.WordTrace]
  refine ⟨37435336386589912447352609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24956890924393274964901739 37435336386589912447352609)
  ·
    refine ⟨28076502289942434335514457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37435336386589912447352609 28076502289942434335514457)
    ·
      refine ⟨21057376717456825751635843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28076502289942434335514457 21057376717456825751635843)
      ·
        refine ⟨31586065076185238627453765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21057376717456825751635843 31586065076185238627453765)
        ·
          refine ⟨5922387201784732242647581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31586065076185238627453765 5922387201784732242647581)
          ·
            refine ⟨2220895200669274590992843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5922387201784732242647581 2220895200669274590992843)
            ·
              refine ⟨3331342801003911886489265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220895200669274590992843 3331342801003911886489265)
              ·
                refine ⟨2498507100752933914866949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3331342801003911886489265 2498507100752933914866949)
                ·
                  refine ⟨468470081391175109037553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2498507100752933914866949 468470081391175109037553)
                  ·
                    rfl

theorem cell20_1026385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_1026385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026385 prefixEnd_1026385 := by exact prefixLift 1026385
  have htrace : WordTrace (prefixWord ++ tailWord_1026385) baseStart_1026385 baseEnd_1026385 := by
    simpa [prefixWord, tailWord_1026385, baseEnd_1026385] using wordTrace_append hprefix tailTrace_1026385
  have hstable : (prefixWord ++ tailWord_1026385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026385).length < 2 ^ (prefixWord ++ tailWord_1026385).sum := by decide
  have hdescent : baseEnd_1026385 < baseStart_1026385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026412 : List Nat := [2, 2, 1, 1, 7, 1, 1, 2, 3]
def baseStart_1026412 : Nat := 118140960795 + 1026412 * 2 ^ 59
def prefixEnd_1026412 : Nat := 4983230072969 + 3 ^ 40 * 1026412 * 2
def baseEnd_1026412 : Nat := 468482404926883015137443

theorem tailTrace_1026412 : CollatzResearch.WordTrace tailWord_1026412 prefixEnd_1026412 468482404926883015137443 := by
  unfold tailWord_1026412
  simp only [CollatzResearch.WordTrace]
  refine ⟨18718160578746048029292745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24957547438328064039056993 18718160578746048029292745)
  ·
    refine ⟨14038620434059536021969559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18718160578746048029292745 14038620434059536021969559)
    ·
      refine ⟨21057930651089304032954339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14038620434059536021969559 21057930651089304032954339)
      ·
        refine ⟨31586895976633956049431509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21057930651089304032954339 31586895976633956049431509)
        ·
          refine ⟨740317874452358344908551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 31586895976633956049431509 740317874452358344908551)
          ·
            refine ⟨1110476811678537517362827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740317874452358344908551 1110476811678537517362827)
            ·
              refine ⟨1665715217517806276044241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110476811678537517362827 1665715217517806276044241)
              ·
                refine ⟨1249286413138354707033181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665715217517806276044241 1249286413138354707033181)
                ·
                  refine ⟨468482404926883015137443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1249286413138354707033181 468482404926883015137443)
                  ·
                    rfl

theorem cell20_1026412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_1026412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026412 prefixEnd_1026412 := by exact prefixLift 1026412
  have htrace : WordTrace (prefixWord ++ tailWord_1026412) baseStart_1026412 baseEnd_1026412 := by
    simpa [prefixWord, tailWord_1026412, baseEnd_1026412] using wordTrace_append hprefix tailTrace_1026412
  have hstable : (prefixWord ++ tailWord_1026412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026412).length < 2 ^ (prefixWord ++ tailWord_1026412).sum := by decide
  have hdescent : baseEnd_1026412 < baseStart_1026412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026416 : List Nat := [2, 1, 1, 1, 4, 3, 3, 2, 3]
def baseStart_1026416 : Nat := 118140960795 + 1026416 * 2 ^ 59
def prefixEnd_1026416 : Nat := 4983230072969 + 3 ^ 40 * 1026416 * 2
def baseEnd_1026416 : Nat := 468484230635876779004093

theorem tailTrace_1026416 : CollatzResearch.WordTrace tailWord_1026416 prefixEnd_1026416 468484230635876779004093 := by
  unfold tailWord_1026416
  simp only [CollatzResearch.WordTrace]
  refine ⟨18718233524738802370865551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24957644699651736494487401 18718233524738802370865551)
  ·
    refine ⟨28077350287108203556298327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18718233524738802370865551 28077350287108203556298327)
    ·
      refine ⟨42116025430662305334447491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28077350287108203556298327 42116025430662305334447491)
      ·
        refine ⟨63174038145993458001671237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42116025430662305334447491 63174038145993458001671237)
        ·
          refine ⟨11845132152373773375313357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63174038145993458001671237 11845132152373773375313357)
          ·
            refine ⟨4441924557140165015742509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11845132152373773375313357 4441924557140165015742509)
            ·
              refine ⟨1665721708927561880903441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4441924557140165015742509 1665721708927561880903441)
              ·
                refine ⟨1249291281695671410677581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665721708927561880903441 1249291281695671410677581)
                ·
                  refine ⟨468484230635876779004093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1249291281695671410677581 468484230635876779004093)
                  ·
                    rfl

theorem cell20_1026416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_1026416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026416 prefixEnd_1026416 := by exact prefixLift 1026416
  have htrace : WordTrace (prefixWord ++ tailWord_1026416) baseStart_1026416 baseEnd_1026416 := by
    simpa [prefixWord, tailWord_1026416, baseEnd_1026416] using wordTrace_append hprefix tailTrace_1026416
  have hstable : (prefixWord ++ tailWord_1026416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026416).length < 2 ^ (prefixWord ++ tailWord_1026416).sum := by decide
  have hdescent : baseEnd_1026416 < baseStart_1026416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026484 : List Nat := [2, 5, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1026484 : Nat := 118140960795 + 1026484 * 2 ^ 59
def prefixEnd_1026484 : Nat := 4983230072969 + 3 ^ 40 * 1026484 * 2
def baseEnd_1026484 : Nat := 468515267688770764737149

theorem tailTrace_1026484 : CollatzResearch.WordTrace tailWord_1026484 prefixEnd_1026484 468515267688770764737149 := by
  unfold tailWord_1026484
  simp only [CollatzResearch.WordTrace]
  refine ⟨18719473606615626177603253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24959298142154168236804337 18719473606615626177603253)
  ·
    refine ⟨1754950650620214954150305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18719473606615626177603253 1754950650620214954150305)
    ·
      refine ⟨1316212987965161215612729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1754950650620214954150305 1316212987965161215612729)
      ·
        refine ⟨987159740973870911709547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1316212987965161215612729 987159740973870911709547)
        ·
          refine ⟨1480739611460806367564321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987159740973870911709547 1480739611460806367564321)
          ·
            refine ⟨1110554708595604775673241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1480739611460806367564321 1110554708595604775673241)
            ·
              refine ⟨832916031446703581754931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1110554708595604775673241 832916031446703581754931)
              ·
                refine ⟨1249374047170055372632397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832916031446703581754931 1249374047170055372632397)
                ·
                  refine ⟨468515267688770764737149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1249374047170055372632397 468515267688770764737149)
                  ·
                    rfl

theorem cell20_1026484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1026484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026484 prefixEnd_1026484 := by exact prefixLift 1026484
  have htrace : WordTrace (prefixWord ++ tailWord_1026484) baseStart_1026484 baseEnd_1026484 := by
    simpa [prefixWord, tailWord_1026484, baseEnd_1026484] using wordTrace_append hprefix tailTrace_1026484
  have hstable : (prefixWord ++ tailWord_1026484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026484).length < 2 ^ (prefixWord ++ tailWord_1026484).sum := by decide
  have hdescent : baseEnd_1026484 < baseStart_1026484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026485 : List Nat := [1, 3, 3, 2, 3, 1, 2, 5]
def baseStart_1026485 : Nat := 118140960795 + 1026485 * 2 ^ 59
def prefixEnd_1026485 : Nat := 4983230072969 + 3 ^ 40 * 1026485 * 2
def baseEnd_1026485 : Nat := 156171908038673068567937

theorem tailTrace_1026485 : CollatzResearch.WordTrace tailWord_1026485 prefixEnd_1026485 156171908038673068567937 := by
  unfold tailWord_1026485
  simp only [CollatzResearch.WordTrace]
  refine ⟨37438983686227629525992909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24959322457485086350661939 37438983686227629525992909)
  ·
    refine ⟨14039618882335361072247341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37438983686227629525992909 14039618882335361072247341)
    ·
      refine ⟨5264857080875760402092753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14039618882335361072247341 5264857080875760402092753)
      ·
        refine ⟨3948642810656820301569565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5264857080875760402092753 3948642810656820301569565)
        ·
          refine ⟨1480741053996307613088587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3948642810656820301569565 1480741053996307613088587)
          ·
            refine ⟨2221111580994461419632881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480741053996307613088587 2221111580994461419632881)
            ·
              refine ⟨1665833685745846064724661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2221111580994461419632881 1665833685745846064724661)
              ·
                refine ⟨156171908038673068567937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1665833685745846064724661 156171908038673068567937)
                ·
                  rfl

theorem cell20_1026485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 5].length) (baseStart_1026485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026485 prefixEnd_1026485 := by exact prefixLift 1026485
  have htrace : WordTrace (prefixWord ++ tailWord_1026485) baseStart_1026485 baseEnd_1026485 := by
    simpa [prefixWord, tailWord_1026485, baseEnd_1026485] using wordTrace_append hprefix tailTrace_1026485
  have hstable : (prefixWord ++ tailWord_1026485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026485).length < 2 ^ (prefixWord ++ tailWord_1026485).sum := by decide
  have hdescent : baseEnd_1026485 < baseStart_1026485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026527 : List Nat := [1, 1, 2, 3, 3, 10]
def baseStart_1026527 : Nat := 118140960795 + 1026527 * 2 ^ 59
def prefixEnd_1026527 : Nat := 4983230072969 + 3 ^ 40 * 1026527 * 2
def baseEnd_1026527 : Nat := 17353144224461249122357

theorem tailTrace_1026527 : CollatzResearch.WordTrace tailWord_1026527 prefixEnd_1026527 17353144224461249122357 := by
  unfold tailWord_1026527
  simp only [CollatzResearch.WordTrace]
  refine ⟨37440515552075470699021835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24960343701383647132681223 37440515552075470699021835)
  ·
    refine ⟨56160773328113206048532753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37440515552075470699021835 56160773328113206048532753)
    ·
      refine ⟨42120579996084904536399565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56160773328113206048532753 42120579996084904536399565)
      ·
        refine ⟨15795217498531839201149837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42120579996084904536399565 15795217498531839201149837)
        ·
          refine ⟨5923206561949439700431189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15795217498531839201149837 5923206561949439700431189)
          ·
            refine ⟨17353144224461249122357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5923206561949439700431189 17353144224461249122357)
            ·
              rfl

theorem cell20_1026527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 10].length) (baseStart_1026527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026527 prefixEnd_1026527 := by exact prefixLift 1026527
  have htrace : WordTrace (prefixWord ++ tailWord_1026527) baseStart_1026527 baseEnd_1026527 := by
    simpa [prefixWord, tailWord_1026527, baseEnd_1026527] using wordTrace_append hprefix tailTrace_1026527
  have hstable : (prefixWord ++ tailWord_1026527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026527).length < 2 ^ (prefixWord ++ tailWord_1026527).sum := by decide
  have hdescent : baseEnd_1026527 < baseStart_1026527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026533 : List Nat := [1, 3, 1, 5, 2, 1, 1, 4, 2]
def baseStart_1026533 : Nat := 118140960795 + 1026533 * 2 ^ 59
def prefixEnd_1026533 : Nat := 4983230072969 + 3 ^ 40 * 1026533 * 2
def baseEnd_1026533 : Nat := 468537632623944372103615

theorem tailTrace_1026533 : CollatzResearch.WordTrace tailWord_1026533 prefixEnd_1026533 468537632623944372103615 := by
  unfold tailWord_1026533
  simp only [CollatzResearch.WordTrace]
  refine ⟨37440734390053733723740253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24960489593369155815826835 37440734390053733723740253)
  ·
    refine ⟨14040275396270150146402595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37440734390053733723740253 14040275396270150146402595)
    ·
      refine ⟨21060413094405225219603893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14040275396270150146402595 21060413094405225219603893)
      ·
        refine ⟨1974413727600489864337865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21060413094405225219603893 1974413727600489864337865)
        ·
          refine ⟨1480810295700367398253399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1974413727600489864337865 1480810295700367398253399)
          ·
            refine ⟨2221215443550551097380099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480810295700367398253399 2221215443550551097380099)
            ·
              refine ⟨3331823165325826646070149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2221215443550551097380099 3331823165325826646070149)
              ·
                refine ⟨624716843498592496138153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3331823165325826646070149 624716843498592496138153)
                ·
                  refine ⟨468537632623944372103615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624716843498592496138153 468537632623944372103615)
                  ·
                    rfl

theorem cell20_1026533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_1026533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026533 prefixEnd_1026533 := by exact prefixLift 1026533
  have htrace : WordTrace (prefixWord ++ tailWord_1026533) baseStart_1026533 baseEnd_1026533 := by
    simpa [prefixWord, tailWord_1026533, baseEnd_1026533] using wordTrace_append hprefix tailTrace_1026533
  have hstable : (prefixWord ++ tailWord_1026533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026533).length < 2 ^ (prefixWord ++ tailWord_1026533).sum := by decide
  have hdescent : baseEnd_1026533 < baseStart_1026533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026561 : List Nat := [1, 2, 4, 1, 3, 2, 3, 4]
def baseStart_1026561 : Nat := 118140960795 + 1026561 * 2 ^ 59
def prefixEnd_1026561 : Nat := 4983230072969 + 3 ^ 40 * 1026561 * 2
def baseEnd_1026561 : Nat := 156183470862300239723389

theorem tailTrace_1026561 : CollatzResearch.WordTrace tailWord_1026561 prefixEnd_1026561 156183470862300239723389 := by
  unfold tailWord_1026561
  simp only [CollatzResearch.WordTrace]
  refine ⟨37441755633952294505759537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24961170422634863003839691 37441755633952294505759537)
  ·
    refine ⟨28081316725464220879319653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37441755633952294505759537 28081316725464220879319653)
    ·
      refine ⟨5265246886024541414872435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28081316725464220879319653 5265246886024541414872435)
      ·
        refine ⟨7897870329036812122308653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5265246886024541414872435 7897870329036812122308653)
        ·
          refine ⟨2961701373388804545865745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7897870329036812122308653 2961701373388804545865745)
          ·
            refine ⟨2221276030041603409399309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2961701373388804545865745 2221276030041603409399309)
            ·
              refine ⟨832978511265601278524741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2221276030041603409399309 832978511265601278524741)
              ·
                refine ⟨156183470862300239723389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 832978511265601278524741 156183470862300239723389)
                ·
                  rfl

theorem cell20_1026561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 4].length) (baseStart_1026561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026561 prefixEnd_1026561 := by exact prefixLift 1026561
  have htrace : WordTrace (prefixWord ++ tailWord_1026561) baseStart_1026561 baseEnd_1026561 := by
    simpa [prefixWord, tailWord_1026561, baseEnd_1026561] using wordTrace_append hprefix tailTrace_1026561
  have hstable : (prefixWord ++ tailWord_1026561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026561).length < 2 ^ (prefixWord ++ tailWord_1026561).sum := by decide
  have hdescent : baseEnd_1026561 < baseStart_1026561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026565 : List Nat := [1, 3, 1, 1, 2, 2, 2, 8]
def baseStart_1026565 : Nat := 118140960795 + 1026565 * 2 ^ 59
def prefixEnd_1026565 : Nat := 4983230072969 + 3 ^ 40 * 1026565 * 2
def baseEnd_1026565 : Nat := 156184079431964827678939

theorem tailTrace_1026565 : CollatzResearch.WordTrace tailWord_1026565 prefixEnd_1026565 156184079431964827678939 := by
  unfold tailWord_1026565
  simp only [CollatzResearch.WordTrace]
  refine ⟨37441901525937803188905149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24961267683958535459270099 37441901525937803188905149)
  ·
    refine ⟨14040713072226676195839431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37441901525937803188905149 14040713072226676195839431)
    ·
      refine ⟨21061069608340014293759147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14040713072226676195839431 21061069608340014293759147)
      ·
        refine ⟨31591604412510021440638721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21061069608340014293759147 31591604412510021440638721)
        ·
          refine ⟨23693703309382516080479041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31591604412510021440638721 23693703309382516080479041)
          ·
            refine ⟨17770277482036887060359281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23693703309382516080479041 17770277482036887060359281)
            ·
              refine ⟨13327708111527665295269461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17770277482036887060359281 13327708111527665295269461)
              ·
                refine ⟨156184079431964827678939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13327708111527665295269461 156184079431964827678939)
                ·
                  rfl

theorem cell20_1026565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 8].length) (baseStart_1026565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026565 prefixEnd_1026565 := by exact prefixLift 1026565
  have htrace : WordTrace (prefixWord ++ tailWord_1026565) baseStart_1026565 baseEnd_1026565 := by
    simpa [prefixWord, tailWord_1026565, baseEnd_1026565] using wordTrace_append hprefix tailTrace_1026565
  have hstable : (prefixWord ++ tailWord_1026565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026565).length < 2 ^ (prefixWord ++ tailWord_1026565).sum := by decide
  have hdescent : baseEnd_1026565 < baseStart_1026565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026575 : List Nat := [1, 1, 2, 1, 1, 1, 2, 9, 2]
def baseStart_1026575 : Nat := 118140960795 + 1026575 * 2 ^ 59
def prefixEnd_1026575 : Nat := 4983230072969 + 3 ^ 40 * 1026575 * 2
def baseEnd_1026575 : Nat := 468556802568378892703443

theorem tailTrace_1026575 : CollatzResearch.WordTrace tailWord_1026575 prefixEnd_1026575 468556802568378892703443 := by
  unfold tailWord_1026575
  simp only [CollatzResearch.WordTrace]
  refine ⟨37442266255901574896769179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24961510837267716597846119 37442266255901574896769179)
  ·
    refine ⟨56163399383852362345153769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37442266255901574896769179 56163399383852362345153769)
    ·
      refine ⟨42122549537889271758865327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56163399383852362345153769 42122549537889271758865327)
      ·
        refine ⟨63183824306833907638297991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42122549537889271758865327 63183824306833907638297991)
        ·
          refine ⟨94775736460250861457446987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63183824306833907638297991 94775736460250861457446987)
          ·
            refine ⟨142163604690376292186170481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94775736460250861457446987 142163604690376292186170481)
            ·
              refine ⟨106622703517782219139627861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142163604690376292186170481 106622703517782219139627861)
              ·
                refine ⟨624742403424505190271257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 106622703517782219139627861 624742403424505190271257)
                ·
                  refine ⟨468556802568378892703443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624742403424505190271257 468556802568378892703443)
                  ·
                    rfl

theorem cell20_1026575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 2].length) (baseStart_1026575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026575 prefixEnd_1026575 := by exact prefixLift 1026575
  have htrace : WordTrace (prefixWord ++ tailWord_1026575) baseStart_1026575 baseEnd_1026575 := by
    simpa [prefixWord, tailWord_1026575, baseEnd_1026575] using wordTrace_append hprefix tailTrace_1026575
  have hstable : (prefixWord ++ tailWord_1026575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026575).length < 2 ^ (prefixWord ++ tailWord_1026575).sum := by decide
  have hdescent : baseEnd_1026575 < baseStart_1026575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026592 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 4]
def baseStart_1026592 : Nat := 118140960795 + 1026592 * 2 ^ 59
def prefixEnd_1026592 : Nat := 4983230072969 + 3 ^ 40 * 1026592 * 2
def baseEnd_1026592 : Nat := 468564561831602389136707

theorem tailTrace_1026592 : CollatzResearch.WordTrace tailWord_1026592 prefixEnd_1026592 468564561831602389136707 := by
  unfold tailWord_1026592
  simp only [CollatzResearch.WordTrace]
  refine ⟨18721443148419993400069015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24961924197893324533425353 18721443148419993400069015)
  ·
    refine ⟨28082164722629990100103523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18721443148419993400069015 28082164722629990100103523)
    ·
      refine ⟨42123247083944985150155285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28082164722629990100103523 42123247083944985150155285)
      ·
        refine ⟨1974527207059921178913529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42123247083944985150155285 1974527207059921178913529)
        ·
          refine ⟨1480895405294940884185147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1974527207059921178913529 1480895405294940884185147)
          ·
            refine ⟨2221343107942411326277721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480895405294940884185147 2221343107942411326277721)
            ·
              refine ⟨1666007330956808494708291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2221343107942411326277721 1666007330956808494708291)
              ·
                refine ⟨2499010996435212742062437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666007330956808494708291 2499010996435212742062437)
                ·
                  refine ⟨468564561831602389136707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2499010996435212742062437 468564561831602389136707)
                  ·
                    rfl

theorem cell20_1026592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_1026592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026592 prefixEnd_1026592 := by exact prefixLift 1026592
  have htrace : WordTrace (prefixWord ++ tailWord_1026592) baseStart_1026592 baseEnd_1026592 := by
    simpa [prefixWord, tailWord_1026592, baseEnd_1026592] using wordTrace_append hprefix tailTrace_1026592
  have hstable : (prefixWord ++ tailWord_1026592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026592).length < 2 ^ (prefixWord ++ tailWord_1026592).sum := by decide
  have hdescent : baseEnd_1026592 < baseStart_1026592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026612 : List Nat := [2, 5, 1, 3, 2, 1, 2, 4]
def baseStart_1026612 : Nat := 118140960795 + 1026612 * 2 ^ 59
def prefixEnd_1026612 : Nat := 4983230072969 + 3 ^ 40 * 1026612 * 2
def baseEnd_1026612 : Nat := 156191230125523736156653

theorem tailTrace_1026612 : CollatzResearch.WordTrace tailWord_1026612 prefixEnd_1026612 156191230125523736156653 := by
  unfold tailWord_1026612
  simp only [CollatzResearch.WordTrace]
  refine ⟨18721807878383765107933045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24962410504511686810577393 18721807878383765107933045)
  ·
    refine ⟨1755169488598477978868723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18721807878383765107933045 1755169488598477978868723)
    ·
      refine ⟨2632754232897716968303085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1755169488598477978868723 2632754232897716968303085)
      ·
        refine ⟨987282837336643863113657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2632754232897716968303085 987282837336643863113657)
        ·
          refine ⟨740462128002482897335243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987282837336643863113657 740462128002482897335243)
          ·
            refine ⟨1110693192003724346002865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740462128002482897335243 1110693192003724346002865)
            ·
              refine ⟨833019894002793259502149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1110693192003724346002865 833019894002793259502149)
              ·
                refine ⟨156191230125523736156653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 833019894002793259502149 156191230125523736156653)
                ·
                  rfl

theorem cell20_1026612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_1026612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026612 prefixEnd_1026612 := by exact prefixLift 1026612
  have htrace : WordTrace (prefixWord ++ tailWord_1026612) baseStart_1026612 baseEnd_1026612 := by
    simpa [prefixWord, tailWord_1026612, baseEnd_1026612] using wordTrace_append hprefix tailTrace_1026612
  have hstable : (prefixWord ++ tailWord_1026612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026612).length < 2 ^ (prefixWord ++ tailWord_1026612).sum := by decide
  have hdescent : baseEnd_1026612 < baseStart_1026612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026620 : List Nat := [2, 2, 2, 2, 3, 2, 1, 6]
def baseStart_1026620 : Nat := 118140960795 + 1026620 * 2 ^ 59
def prefixEnd_1026620 : Nat := 4983230072969 + 3 ^ 40 * 1026620 * 2
def baseEnd_1026620 : Nat := 156192447264852912067753

theorem tailTrace_1026620 : CollatzResearch.WordTrace tailWord_1026620 prefixEnd_1026620 156192447264852912067753 := by
  unfold tailWord_1026620
  simp only [CollatzResearch.WordTrace]
  refine ⟨18721953770369273791078657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24962605027159031721438209 18721953770369273791078657)
  ·
    refine ⟨14041465327776955343308993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18721953770369273791078657 14041465327776955343308993)
    ·
      refine ⟨10531098995832716507481745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14041465327776955343308993 10531098995832716507481745)
      ·
        refine ⟨7898324246874537380611309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10531098995832716507481745 7898324246874537380611309)
        ·
          refine ⟨2961871592577951517729241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7898324246874537380611309 2961871592577951517729241)
          ·
            refine ⟨2221403694433463638296931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2961871592577951517729241 2221403694433463638296931)
            ·
              refine ⟨3332105541650195457445397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2221403694433463638296931 3332105541650195457445397)
              ·
                refine ⟨156192447264852912067753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3332105541650195457445397 156192447264852912067753)
                ·
                  rfl

theorem cell20_1026620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_1026620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026620 prefixEnd_1026620 := by exact prefixLift 1026620
  have htrace : WordTrace (prefixWord ++ tailWord_1026620) baseStart_1026620 baseEnd_1026620 := by
    simpa [prefixWord, tailWord_1026620, baseEnd_1026620] using wordTrace_append hprefix tailTrace_1026620
  have hstable : (prefixWord ++ tailWord_1026620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026620).length < 2 ^ (prefixWord ++ tailWord_1026620).sum := by decide
  have hdescent : baseEnd_1026620 < baseStart_1026620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026637 : List Nat := [1, 6, 1, 1, 2, 3, 6]
def baseStart_1026637 : Nat := 118140960795 + 1026637 * 2 ^ 59
def prefixEnd_1026637 : Nat := 4983230072969 + 3 ^ 40 * 1026637 * 2
def baseEnd_1026637 : Nat := 52065011228642470292947

theorem tailTrace_1026637 : CollatzResearch.WordTrace tailWord_1026637 prefixEnd_1026637 52065011228642470292947 := by
  unfold tailWord_1026637
  simp only [CollatzResearch.WordTrace]
  refine ⟨37444527581676959485526165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24963018387784639657017443 37444527581676959485526165)
  ·
    refine ⟨1755212230391107475884039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37444527581676959485526165 1755212230391107475884039)
    ·
      refine ⟨2632818345586661213826059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1755212230391107475884039 2632818345586661213826059)
      ·
        refine ⟨3949227518379991820739089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2632818345586661213826059 3949227518379991820739089)
        ·
          refine ⟨2961920638784993865554317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3949227518379991820739089 2961920638784993865554317)
          ·
            refine ⟨1110720239544372699582869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2961920638784993865554317 1110720239544372699582869)
            ·
              refine ⟨52065011228642470292947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1110720239544372699582869 52065011228642470292947)
              ·
                rfl

theorem cell20_1026637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 6].length) (baseStart_1026637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026637 prefixEnd_1026637 := by exact prefixLift 1026637
  have htrace : WordTrace (prefixWord ++ tailWord_1026637) baseStart_1026637 baseEnd_1026637 := by
    simpa [prefixWord, tailWord_1026637, baseEnd_1026637] using wordTrace_append hprefix tailTrace_1026637
  have hstable : (prefixWord ++ tailWord_1026637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026637).length < 2 ^ (prefixWord ++ tailWord_1026637).sum := by decide
  have hdescent : baseEnd_1026637 < baseStart_1026637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026641 : List Nat := [1, 2, 2, 1, 3, 3, 8]
def baseStart_1026641 : Nat := 118140960795 + 1026641 * 2 ^ 59
def prefixEnd_1026641 : Nat := 4983230072969 + 3 ^ 40 * 1026641 * 2
def baseEnd_1026641 : Nat := 52065214085197332944797

theorem tailTrace_1026641 : CollatzResearch.WordTrace tailWord_1026641 prefixEnd_1026641 52065214085197332944797 := by
  unfold tailWord_1026641
  simp only [CollatzResearch.WordTrace]
  refine ⟨37444673473662468168671777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24963115649108312112447851 37444673473662468168671777)
  ·
    refine ⟨28083505105246851126503833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37444673473662468168671777 28083505105246851126503833)
    ·
      refine ⟨21062628828935138344877875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28083505105246851126503833 21062628828935138344877875)
      ·
        refine ⟨31593943243402707517316813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21062628828935138344877875 31593943243402707517316813)
        ·
          refine ⟨11847728716276015318993805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31593943243402707517316813 11847728716276015318993805)
          ·
            refine ⟨4442898268603505744622677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11847728716276015318993805 4442898268603505744622677)
            ·
              refine ⟨52065214085197332944797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4442898268603505744622677 52065214085197332944797)
              ·
                rfl

theorem cell20_1026641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 8].length) (baseStart_1026641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026641 prefixEnd_1026641 := by exact prefixLift 1026641
  have htrace : WordTrace (prefixWord ++ tailWord_1026641) baseStart_1026641 baseEnd_1026641 := by
    simpa [prefixWord, tailWord_1026641, baseEnd_1026641] using wordTrace_append hprefix tailTrace_1026641
  have hstable : (prefixWord ++ tailWord_1026641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026641).length < 2 ^ (prefixWord ++ tailWord_1026641).sum := by decide
  have hdescent : baseEnd_1026641 < baseStart_1026641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026679 : List Nat := [1, 1, 3, 1, 1, 3, 4, 6]
def baseStart_1026679 : Nat := 118140960795 + 1026679 * 2 ^ 59
def prefixEnd_1026679 : Nat := 4983230072969 + 3 ^ 40 * 1026679 * 2
def baseEnd_1026679 : Nat := 156201423667405584412117

theorem tailTrace_1026679 : CollatzResearch.WordTrace tailWord_1026679 prefixEnd_1026679 156201423667405584412117 := by
  unfold tailWord_1026679
  simp only [CollatzResearch.WordTrace]
  refine ⟨37446059447524800658555091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24964039631683200439036727 37446059447524800658555091)
  ·
    refine ⟨56169089171287200987832637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37446059447524800658555091 56169089171287200987832637)
    ·
      refine ⟨21063408439232700370437239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56169089171287200987832637 21063408439232700370437239)
      ·
        refine ⟨31595112658849050555655859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21063408439232700370437239 31595112658849050555655859)
        ·
          refine ⟨47392668988273575833483789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31595112658849050555655859 47392668988273575833483789)
          ·
            refine ⟨17772250870602590937556421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47392668988273575833483789 17772250870602590937556421)
            ·
              refine ⟨3332297038237985800791829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17772250870602590937556421 3332297038237985800791829)
              ·
                refine ⟨156201423667405584412117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3332297038237985800791829 156201423667405584412117)
                ·
                  rfl

theorem cell20_1026679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 6].length) (baseStart_1026679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026679 prefixEnd_1026679 := by exact prefixLift 1026679
  have htrace : WordTrace (prefixWord ++ tailWord_1026679) baseStart_1026679 baseEnd_1026679 := by
    simpa [prefixWord, tailWord_1026679, baseEnd_1026679] using wordTrace_append hprefix tailTrace_1026679
  have hstable : (prefixWord ++ tailWord_1026679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026679).length < 2 ^ (prefixWord ++ tailWord_1026679).sum := by decide
  have hdescent : baseEnd_1026679 < baseStart_1026679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026748 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 6]
def baseStart_1026748 : Nat := 118140960795 + 1026748 * 2 ^ 59
def prefixEnd_1026748 : Nat := 4983230072969 + 3 ^ 40 * 1026748 * 2
def baseEnd_1026748 : Nat := 468635764482359179936069

theorem tailTrace_1026748 : CollatzResearch.WordTrace tailWord_1026748 prefixEnd_1026748 468635764482359179936069 := by
  unfold tailWord_1026748
  simp only [CollatzResearch.WordTrace]
  refine ⟨18724288042137412721408449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24965717389516550295211265 18724288042137412721408449)
  ·
    refine ⟨14043216031603059541056337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18724288042137412721408449 14043216031603059541056337)
    ·
      refine ⟨10532412023702294655792253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14043216031603059541056337 10532412023702294655792253)
      ·
        refine ⟨3949654508888360495922095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10532412023702294655792253 3949654508888360495922095)
        ·
          refine ⟨5924481763332540743883143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3949654508888360495922095 5924481763332540743883143)
          ·
            refine ⟨8886722644998811115824715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5924481763332540743883143 8886722644998811115824715)
            ·
              refine ⟨13330083967498216673737073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8886722644998811115824715 13330083967498216673737073)
              ·
                refine ⟨9997562975623662505302805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13330083967498216673737073 9997562975623662505302805)
                ·
                  refine ⟨468635764482359179936069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9997562975623662505302805 468635764482359179936069)
                  ·
                    rfl

theorem cell20_1026748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_1026748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026748 prefixEnd_1026748 := by exact prefixLift 1026748
  have htrace : WordTrace (prefixWord ++ tailWord_1026748) baseStart_1026748 baseEnd_1026748 := by
    simpa [prefixWord, tailWord_1026748, baseEnd_1026748] using wordTrace_append hprefix tailTrace_1026748
  have hstable : (prefixWord ++ tailWord_1026748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026748).length < 2 ^ (prefixWord ++ tailWord_1026748).sum := by decide
  have hdescent : baseEnd_1026748 < baseStart_1026748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026789 : List Nat := [1, 3, 1, 4, 1, 4, 2, 4]
def baseStart_1026789 : Nat := 118140960795 + 1026789 * 2 ^ 59
def prefixEnd_1026789 : Nat := 4983230072969 + 3 ^ 40 * 1026789 * 2
def baseEnd_1026789 : Nat := 156218159333181753189745

theorem tailTrace_1026789 : CollatzResearch.WordTrace tailWord_1026789 prefixEnd_1026789 156218159333181753189745 := by
  unfold tailWord_1026789
  simp only [CollatzResearch.WordTrace]
  refine ⟨37450071477126289445059421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24966714318084192963372947 37450071477126289445059421)
  ·
    refine ⟨14043776803922358541897283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37450071477126289445059421 14043776803922358541897283)
    ·
      refine ⟨21065665205883537812845925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14043776803922358541897283 21065665205883537812845925)
      ·
        refine ⟨3949812226103163339908611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21065665205883537812845925 3949812226103163339908611)
        ·
          refine ⟨5924718339154745009862917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3949812226103163339908611 5924718339154745009862917)
          ·
            refine ⟨1110884688591514689349297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5924718339154745009862917 1110884688591514689349297)
            ·
              refine ⟨833163516443636017011973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1110884688591514689349297 833163516443636017011973)
              ·
                refine ⟨156218159333181753189745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 833163516443636017011973 156218159333181753189745)
                ·
                  rfl

theorem cell20_1026789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 4].length) (baseStart_1026789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026789 prefixEnd_1026789 := by exact prefixLift 1026789
  have htrace : WordTrace (prefixWord ++ tailWord_1026789) baseStart_1026789 baseEnd_1026789 := by
    simpa [prefixWord, tailWord_1026789, baseEnd_1026789] using wordTrace_append hprefix tailTrace_1026789
  have hstable : (prefixWord ++ tailWord_1026789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026789).length < 2 ^ (prefixWord ++ tailWord_1026789).sum := by decide
  have hdescent : baseEnd_1026789 < baseStart_1026789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026800 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 7]
def baseStart_1026800 : Nat := 118140960795 + 1026800 * 2 ^ 59
def prefixEnd_1026800 : Nat := 4983230072969 + 3 ^ 40 * 1026800 * 2
def baseEnd_1026800 : Nat := 468659498699278110202523

theorem tailTrace_1026800 : CollatzResearch.WordTrace tailWord_1026800 prefixEnd_1026800 468659498699278110202523 := by
  unfold tailWord_1026800
  simp only [CollatzResearch.WordTrace]
  refine ⟨18725236340043219161854927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24966981786724292215806569 18725236340043219161854927)
  ·
    refine ⟨28087854510064828742782391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18725236340043219161854927 28087854510064828742782391)
    ·
      refine ⟨42131781765097243114173587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28087854510064828742782391 42131781765097243114173587)
      ·
        refine ⟨63197672647645864671260381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42131781765097243114173587 63197672647645864671260381)
        ·
          refine ⟨23699127242867199251722643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63197672647645864671260381 23699127242867199251722643)
          ·
            refine ⟨35548690864300798877583965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23699127242867199251722643 35548690864300798877583965)
            ·
              refine ⟨13330759074112799579093987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35548690864300798877583965 13330759074112799579093987)
              ·
                refine ⟨19996138611169199368640981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13330759074112799579093987 19996138611169199368640981)
                ·
                  refine ⟨468659498699278110202523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19996138611169199368640981 468659498699278110202523)
                  ·
                    rfl

theorem cell20_1026800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_1026800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026800 prefixEnd_1026800 := by exact prefixLift 1026800
  have htrace : WordTrace (prefixWord ++ tailWord_1026800) baseStart_1026800 baseEnd_1026800 := by
    simpa [prefixWord, tailWord_1026800, baseEnd_1026800] using wordTrace_append hprefix tailTrace_1026800
  have hstable : (prefixWord ++ tailWord_1026800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026800).length < 2 ^ (prefixWord ++ tailWord_1026800).sum := by decide
  have hdescent : baseEnd_1026800 < baseStart_1026800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026817 : List Nat := [1, 2, 4, 1, 1, 1, 1, 6, 3]
def baseStart_1026817 : Nat := 118140960795 + 1026817 * 2 ^ 59
def prefixEnd_1026817 : Nat := 4983230072969 + 3 ^ 40 * 1026817 * 2
def baseEnd_1026817 : Nat := 468667257962501606635787

theorem tailTrace_1026817 : CollatzResearch.WordTrace tailWord_1026817 prefixEnd_1026817 468667257962501606635787 := by
  unfold tailWord_1026817
  simp only [CollatzResearch.WordTrace]
  refine ⟨37451092721024850227078705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24967395147349900151385803 37451092721024850227078705)
  ·
    refine ⟨28088319540768637670309029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37451092721024850227078705 28088319540768637670309029)
    ·
      refine ⟨5266559913894119563182943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28088319540768637670309029 5266559913894119563182943)
      ·
        refine ⟨7899839870841179344774415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5266559913894119563182943 7899839870841179344774415)
        ·
          refine ⟨11849759806261769017161623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7899839870841179344774415 11849759806261769017161623)
          ·
            refine ⟨17774639709392653525742435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11849759806261769017161623 17774639709392653525742435)
            ·
              refine ⟨26661959564088980288613653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17774639709392653525742435 26661959564088980288613653)
              ·
                refine ⟨1249779354566670951028765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26661959564088980288613653 1249779354566670951028765)
                ·
                  refine ⟨468667257962501606635787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1249779354566670951028765 468667257962501606635787)
                  ·
                    rfl

theorem cell20_1026817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_1026817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026817 prefixEnd_1026817 := by exact prefixLift 1026817
  have htrace : WordTrace (prefixWord ++ tailWord_1026817) baseStart_1026817 baseEnd_1026817 := by
    simpa [prefixWord, tailWord_1026817, baseEnd_1026817] using wordTrace_append hprefix tailTrace_1026817
  have hstable : (prefixWord ++ tailWord_1026817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026817).length < 2 ^ (prefixWord ++ tailWord_1026817).sum := by decide
  have hdescent : baseEnd_1026817 < baseStart_1026817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026831 : List Nat := [1, 1, 2, 1, 1, 1, 8, 5]
def baseStart_1026831 : Nat := 118140960795 + 1026831 * 2 ^ 59
def prefixEnd_1026831 : Nat := 4983230072969 + 3 ^ 40 * 1026831 * 2
def baseEnd_1026831 : Nat := 156224549314659926723021

theorem tailTrace_1026831 : CollatzResearch.WordTrace tailWord_1026831 prefixEnd_1026831 156224549314659926723021 := by
  unfold tailWord_1026831
  simp only [CollatzResearch.WordTrace]
  refine ⟨37451603342974130618088347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24967735561982753745392231 37451603342974130618088347)
  ·
    refine ⟨56177405014461195927132521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37451603342974130618088347 56177405014461195927132521)
    ·
      refine ⟨42133053760845896945349391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56177405014461195927132521 42133053760845896945349391)
      ·
        refine ⟨63199580641268845418024087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42133053760845896945349391 63199580641268845418024087)
        ·
          refine ⟨94799370961903268127036131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63199580641268845418024087 94799370961903268127036131)
          ·
            refine ⟨142199056442854902190554197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94799370961903268127036131 142199056442854902190554197)
            ·
              refine ⟨1666395192689705885045557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 142199056442854902190554197 1666395192689705885045557)
              ·
                refine ⟨156224549314659926723021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1666395192689705885045557 156224549314659926723021)
                ·
                  rfl

theorem cell20_1026831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 5].length) (baseStart_1026831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026831 prefixEnd_1026831 := by exact prefixLift 1026831
  have htrace : WordTrace (prefixWord ++ tailWord_1026831) baseStart_1026831 baseEnd_1026831 := by
    simpa [prefixWord, tailWord_1026831, baseEnd_1026831] using wordTrace_append hprefix tailTrace_1026831
  have hstable : (prefixWord ++ tailWord_1026831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026831).length < 2 ^ (prefixWord ++ tailWord_1026831).sum := by decide
  have hdescent : baseEnd_1026831 < baseStart_1026831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026869 : List Nat := [1, 3, 3, 1, 3, 9]
def baseStart_1026869 : Nat := 118140960795 + 1026869 * 2 ^ 59
def prefixEnd_1026869 : Nat := 4983230072969 + 3 ^ 40 * 1026869 * 2
def baseEnd_1026869 : Nat := 17358925636274834700083

theorem tailTrace_1026869 : CollatzResearch.WordTrace tailWord_1026869 prefixEnd_1026869 17358925636274834700083 := by
  unfold tailWord_1026869
  simp only [CollatzResearch.WordTrace]
  refine ⟨37452989316836463107971661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24968659544557642071981107 37452989316836463107971661)
  ·
    refine ⟨14044870993813673665489373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37452989316836463107971661 14044870993813673665489373)
    ·
      refine ⟨5266826622680127624558515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14044870993813673665489373 5266826622680127624558515)
      ·
        refine ⟨7900239934020191436837773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5266826622680127624558515 7900239934020191436837773)
        ·
          refine ⟨2962589975257571788814165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7900239934020191436837773 2962589975257571788814165)
          ·
            refine ⟨17358925636274834700083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2962589975257571788814165 17358925636274834700083)
            ·
              rfl

theorem cell20_1026869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 9].length) (baseStart_1026869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026869 prefixEnd_1026869 := by exact prefixLift 1026869
  have htrace : WordTrace (prefixWord ++ tailWord_1026869) baseStart_1026869 baseEnd_1026869 := by
    simpa [prefixWord, tailWord_1026869, baseEnd_1026869] using wordTrace_append hprefix tailTrace_1026869
  have hstable : (prefixWord ++ tailWord_1026869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026869).length < 2 ^ (prefixWord ++ tailWord_1026869).sum := by decide
  have hdescent : baseEnd_1026869 < baseStart_1026869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026917 : List Nat := [1, 3, 1, 3, 1, 1, 3, 5, 2]
def baseStart_1026917 : Nat := 118140960795 + 1026917 * 2 ^ 59
def prefixEnd_1026917 : Nat := 4983230072969 + 3 ^ 40 * 1026917 * 2
def baseEnd_1026917 : Nat := 468712900687345703302045

theorem tailTrace_1026917 : CollatzResearch.WordTrace tailWord_1026917 prefixEnd_1026917 468712900687345703302045 := by
  unfold tailWord_1026917
  simp only [CollatzResearch.WordTrace]
  refine ⟨37454740020662567305719005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24969826680441711537146003 37454740020662567305719005)
  ·
    refine ⟨14045527507748462739644627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37454740020662567305719005 14045527507748462739644627)
    ·
      refine ⟨21068291261622694109466941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14045527507748462739644627 21068291261622694109466941)
      ·
        refine ⟨7900609223108510291050103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21068291261622694109466941 7900609223108510291050103)
        ·
          refine ⟨11850913834662765436575155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7900609223108510291050103 11850913834662765436575155)
          ·
            refine ⟨17776370751994148154862733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11850913834662765436575155 17776370751994148154862733)
            ·
              refine ⟨6666139031997805558073525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17776370751994148154862733 6666139031997805558073525)
              ·
                refine ⟨624950534249794271069393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6666139031997805558073525 624950534249794271069393)
                ·
                  refine ⟨468712900687345703302045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624950534249794271069393 468712900687345703302045)
                  ·
                    rfl

theorem cell20_1026917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_1026917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026917 prefixEnd_1026917 := by exact prefixLift 1026917
  have htrace : WordTrace (prefixWord ++ tailWord_1026917) baseStart_1026917 baseEnd_1026917 := by
    simpa [prefixWord, tailWord_1026917, baseEnd_1026917] using wordTrace_append hprefix tailTrace_1026917
  have hstable : (prefixWord ++ tailWord_1026917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026917).length < 2 ^ (prefixWord ++ tailWord_1026917).sum := by decide
  have hdescent : baseEnd_1026917 < baseStart_1026917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026931 : List Nat := [1, 1, 1, 2, 2, 1, 7, 2, 3]
def baseStart_1026931 : Nat := 118140960795 + 1026931 * 2 ^ 59
def prefixEnd_1026931 : Nat := 4983230072969 + 3 ^ 40 * 1026931 * 2
def baseEnd_1026931 : Nat := 468719290668823876835321

theorem tailTrace_1026931 : CollatzResearch.WordTrace tailWord_1026931 prefixEnd_1026931 468719290668823876835321 := by
  unfold tailWord_1026931
  simp only [CollatzResearch.WordTrace]
  refine ⟨37455250642611847696728647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24970167095074565131152431 37455250642611847696728647)
  ·
    refine ⟨56182875963917771545092971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37455250642611847696728647 56182875963917771545092971)
    ·
      refine ⟨84274313945876657317639457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56182875963917771545092971 84274313945876657317639457)
      ·
        refine ⟨63205735459407492988229593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84274313945876657317639457 63205735459407492988229593)
        ·
          refine ⟨47404301594555619741172195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63205735459407492988229593 47404301594555619741172195)
          ·
            refine ⟨71106452391833429611758293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47404301594555619741172195 71106452391833429611758293)
            ·
              refine ⟨1666557477933596006525585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71106452391833429611758293 1666557477933596006525585)
              ·
                refine ⟨1249918108450197004894189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1666557477933596006525585 1249918108450197004894189)
                ·
                  refine ⟨468719290668823876835321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1249918108450197004894189 468719290668823876835321)
                  ·
                    rfl

theorem cell20_1026931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 3].length) (baseStart_1026931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026931 prefixEnd_1026931 := by exact prefixLift 1026931
  have htrace : WordTrace (prefixWord ++ tailWord_1026931) baseStart_1026931 baseEnd_1026931 := by
    simpa [prefixWord, tailWord_1026931, baseEnd_1026931] using wordTrace_append hprefix tailTrace_1026931
  have hstable : (prefixWord ++ tailWord_1026931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026931).length < 2 ^ (prefixWord ++ tailWord_1026931).sum := by decide
  have hdescent : baseEnd_1026931 < baseStart_1026931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026934 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1026934 : Nat := 118140960795 + 1026934 * 2 ^ 59
def prefixEnd_1026934 : Nat := 4983230072969 + 3 ^ 40 * 1026934 * 2
def baseEnd_1026934 : Nat := 468720659950569199735309

theorem tailTrace_1026934 : CollatzResearch.WordTrace tailWord_1026934 prefixEnd_1026934 468720659950569199735309 := by
  unfold tailWord_1026934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2340960003850061200567991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24970240041067319472725237 2340960003850061200567991)
  ·
    refine ⟨3511440005775091800851987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2340960003850061200567991 3511440005775091800851987)
    ·
      refine ⟨5267160008662637701277981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3511440005775091800851987 5267160008662637701277981)
      ·
        refine ⟨1975185003248489137979243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5267160008662637701277981 1975185003248489137979243)
        ·
          refine ⟨2962777504872733706968865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1975185003248489137979243 2962777504872733706968865)
          ·
            refine ⟨2222083128654550280226649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2962777504872733706968865 2222083128654550280226649)
            ·
              refine ⟨1666562346490912710169987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2222083128654550280226649 1666562346490912710169987)
              ·
                refine ⟨2499843519736369065254981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666562346490912710169987 2499843519736369065254981)
                ·
                  refine ⟨468720659950569199735309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2499843519736369065254981 468720659950569199735309)
                  ·
                    rfl

theorem cell20_1026934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1026934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026934 prefixEnd_1026934 := by exact prefixLift 1026934
  have htrace : WordTrace (prefixWord ++ tailWord_1026934) baseStart_1026934 baseEnd_1026934 := by
    simpa [prefixWord, tailWord_1026934, baseEnd_1026934] using wordTrace_append hprefix tailTrace_1026934
  have hstable : (prefixWord ++ tailWord_1026934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026934).length < 2 ^ (prefixWord ++ tailWord_1026934).sum := by decide
  have hdescent : baseEnd_1026934 < baseStart_1026934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1026989 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 4]
def baseStart_1026989 : Nat := 118140960795 + 1026989 * 2 ^ 59
def prefixEnd_1026989 : Nat := 4983230072969 + 3 ^ 40 * 1026989 * 2
def baseEnd_1026989 : Nat := 468745763449233452901751

theorem tailTrace_1026989 : CollatzResearch.WordTrace tailWord_1026989 prefixEnd_1026989 468745763449233452901751 := by
  unfold tailWord_1026989
  simp only [CollatzResearch.WordTrace]
  refine ⟨37457366076401723602340021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24971577384267815734893347 37457366076401723602340021)
  ·
    refine ⟨3511628069662661587719377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37457366076401723602340021 3511628069662661587719377)
    ·
      refine ⟨2633721052246996190789533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3511628069662661587719377 2633721052246996190789533)
      ·
        refine ⟨987645394592623571546075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2633721052246996190789533 987645394592623571546075)
        ·
          refine ⟨1481468091888935357319113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987645394592623571546075 1481468091888935357319113)
          ·
            refine ⟨1111101068916701517989335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1481468091888935357319113 1111101068916701517989335)
            ·
              refine ⟨1666651603375052276984003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111101068916701517989335 1666651603375052276984003)
              ·
                refine ⟨2499977405062578415476005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666651603375052276984003 2499977405062578415476005)
                ·
                  refine ⟨468745763449233452901751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2499977405062578415476005 468745763449233452901751)
                  ·
                    rfl

theorem cell20_1026989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_1026989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1026989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1026989 prefixEnd_1026989 := by exact prefixLift 1026989
  have htrace : WordTrace (prefixWord ++ tailWord_1026989) baseStart_1026989 baseEnd_1026989 := by
    simpa [prefixWord, tailWord_1026989, baseEnd_1026989] using wordTrace_append hprefix tailTrace_1026989
  have hstable : (prefixWord ++ tailWord_1026989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1026989).length < 2 ^ (prefixWord ++ tailWord_1026989).sum := by decide
  have hdescent : baseEnd_1026989 < baseStart_1026989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1026989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027048 : List Nat := [2, 1, 4, 1, 1, 1, 6, 2, 2]
def baseStart_1027048 : Nat := 118140960795 + 1027048 * 2 ^ 59
def prefixEnd_1027048 : Nat := 4983230072969 + 3 ^ 40 * 1027048 * 2
def baseEnd_1027048 : Nat := 468772692656891469934843

theorem tailTrace_1027048 : CollatzResearch.WordTrace tailWord_1027048 prefixEnd_1027048 468772692656891469934843 := by
  unfold tailWord_1027048
  simp only [CollatzResearch.WordTrace]
  refine ⟨18729758991593988339368899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24973011988791984452491865 18729758991593988339368899)
  ·
    refine ⟨28094638487390982509053349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18729758991593988339368899 28094638487390982509053349)
    ·
      refine ⟨5267744716385809220447503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28094638487390982509053349 5267744716385809220447503)
      ·
        refine ⟨7901617074578713830671255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5267744716385809220447503 7901617074578713830671255)
        ·
          refine ⟨11852425611868070746006883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7901617074578713830671255 11852425611868070746006883)
          ·
            refine ⟨17778638417802106119010325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11852425611868070746006883 17778638417802106119010325)
            ·
              refine ⟨833373675834473724328609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17778638417802106119010325 833373675834473724328609)
              ·
                refine ⟨625030256875855293246457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833373675834473724328609 625030256875855293246457)
                ·
                  refine ⟨468772692656891469934843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625030256875855293246457 468772692656891469934843)
                  ·
                    rfl

theorem cell20_1027048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 2].length) (baseStart_1027048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027048 prefixEnd_1027048 := by exact prefixLift 1027048
  have htrace : WordTrace (prefixWord ++ tailWord_1027048) baseStart_1027048 baseEnd_1027048 := by
    simpa [prefixWord, tailWord_1027048, baseEnd_1027048] using wordTrace_append hprefix tailTrace_1027048
  have hstable : (prefixWord ++ tailWord_1027048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027048).length < 2 ^ (prefixWord ++ tailWord_1027048).sum := by decide
  have hdescent : baseEnd_1027048 < baseStart_1027048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027062 : List Nat := [5, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1027062 : Nat := 118140960795 + 1027062 * 2 ^ 59
def prefixEnd_1027062 : Nat := 4983230072969 + 3 ^ 40 * 1027062 * 2
def baseEnd_1027062 : Nat := 468779082638369643468119

theorem tailTrace_1027062 : CollatzResearch.WordTrace tailWord_1027062 prefixEnd_1027062 468779082638369643468119 := by
  unfold tailWord_1027062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2341251787821078566859215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24973352403424838046498293 2341251787821078566859215)
  ·
    refine ⟨3511877681731617850288823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2341251787821078566859215 3511877681731617850288823)
    ·
      refine ⟨5267816522597426775433235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3511877681731617850288823 5267816522597426775433235)
      ·
        refine ⟨7901724783896140163149853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5267816522597426775433235 7901724783896140163149853)
        ·
          refine ⟨2963146793961052561181195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7901724783896140163149853 2963146793961052561181195)
          ·
            refine ⟨4444720190941578841771793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2963146793961052561181195 4444720190941578841771793)
            ·
              refine ⟨3333540143206184131328845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4444720190941578841771793 3333540143206184131328845)
              ·
                refine ⟨1250077553702319049248317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3333540143206184131328845 1250077553702319049248317)
                ·
                  refine ⟨468779082638369643468119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1250077553702319049248317 468779082638369643468119)
                  ·
                    rfl

theorem cell20_1027062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1027062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027062 prefixEnd_1027062 := by exact prefixLift 1027062
  have htrace : WordTrace (prefixWord ++ tailWord_1027062) baseStart_1027062 baseEnd_1027062 := by
    simpa [prefixWord, tailWord_1027062, baseEnd_1027062] using wordTrace_append hprefix tailTrace_1027062
  have hstable : (prefixWord ++ tailWord_1027062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027062).length < 2 ^ (prefixWord ++ tailWord_1027062).sum := by decide
  have hdescent : baseEnd_1027062 < baseStart_1027062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027086 : List Nat := [4, 1, 1, 2, 2, 3, 2, 3, 2]
def baseStart_1027086 : Nat := 118140960795 + 1027086 * 2 ^ 59
def prefixEnd_1027086 : Nat := 4983230072969 + 3 ^ 40 * 1027086 * 2
def baseEnd_1027086 : Nat := 468790036892332226668021

theorem tailTrace_1027086 : CollatzResearch.WordTrace tailWord_1027086 prefixEnd_1027086 468790036892332226668021 := by
  unfold tailWord_1027086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4682612994631288646077639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24973935971366872779080741 4682612994631288646077639)
  ·
    refine ⟨7023919491946932969116459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4682612994631288646077639 7023919491946932969116459)
    ·
      refine ⟨10535879237920399453674689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7023919491946932969116459 10535879237920399453674689)
      ·
        refine ⟨7901909428440299590256017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10535879237920399453674689 7901909428440299590256017)
        ·
          refine ⟨5926432071330224692692013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7901909428440299590256017 5926432071330224692692013)
          ·
            refine ⟨2222412026748834259759505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5926432071330224692692013 2222412026748834259759505)
            ·
              refine ⟨1666809020061625694819629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2222412026748834259759505 1666809020061625694819629)
              ·
                refine ⟨625053382523109635557361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1666809020061625694819629 625053382523109635557361)
                ·
                  refine ⟨468790036892332226668021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625053382523109635557361 468790036892332226668021)
                  ·
                    rfl

theorem cell20_1027086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_1027086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027086 prefixEnd_1027086 := by exact prefixLift 1027086
  have htrace : WordTrace (prefixWord ++ tailWord_1027086) baseStart_1027086 baseEnd_1027086 := by
    simpa [prefixWord, tailWord_1027086, baseEnd_1027086] using wordTrace_append hprefix tailTrace_1027086
  have hstable : (prefixWord ++ tailWord_1027086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027086).length < 2 ^ (prefixWord ++ tailWord_1027086).sum := by decide
  have hdescent : baseEnd_1027086 < baseStart_1027086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027107 : List Nat := [1, 1, 1, 4, 3, 2, 2, 4, 2]
def baseStart_1027107 : Nat := 118140960795 + 1027107 * 2 ^ 59
def prefixEnd_1027107 : Nat := 4983230072969 + 3 ^ 40 * 1027107 * 2
def baseEnd_1027107 : Nat := 468799621864549486967935

theorem tailTrace_1027107 : CollatzResearch.WordTrace tailWord_1027107 prefixEnd_1027107 468799621864549486967935 := by
  unfold tailWord_1027107
  simp only [CollatzResearch.WordTrace]
  refine ⟨37461669889974229755135575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24974446593316153170090383 37461669889974229755135575)
  ·
    refine ⟨56192504834961344632703363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37461669889974229755135575 56192504834961344632703363)
    ·
      refine ⟨84288757252442016949055045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56192504834961344632703363 84288757252442016949055045)
      ·
        refine ⟨15804141984832878177947821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84288757252442016949055045 15804141984832878177947821)
        ·
          refine ⟨5926553244312329316730433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15804141984832878177947821 5926553244312329316730433)
          ·
            refine ⟨4444914933234246987547825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5926553244312329316730433 4444914933234246987547825)
            ·
              refine ⟨3333686199925685240660869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4444914933234246987547825 3333686199925685240660869)
              ·
                refine ⟨625066162486065982623913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3333686199925685240660869 625066162486065982623913)
                ·
                  refine ⟨468799621864549486967935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625066162486065982623913 468799621864549486967935)
                  ·
                    rfl

theorem cell20_1027107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 2].length) (baseStart_1027107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027107 prefixEnd_1027107 := by exact prefixLift 1027107
  have htrace : WordTrace (prefixWord ++ tailWord_1027107) baseStart_1027107 baseEnd_1027107 := by
    simpa [prefixWord, tailWord_1027107, baseEnd_1027107] using wordTrace_append hprefix tailTrace_1027107
  have hstable : (prefixWord ++ tailWord_1027107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027107).length < 2 ^ (prefixWord ++ tailWord_1027107).sum := by decide
  have hdescent : baseEnd_1027107 < baseStart_1027107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027128 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 4]
def baseStart_1027128 : Nat := 118140960795 + 1027128 * 2 ^ 59
def prefixEnd_1027128 : Nat := 4983230072969 + 3 ^ 40 * 1027128 * 2
def baseEnd_1027128 : Nat := 468809206836766747267849

theorem tailTrace_1027128 : CollatzResearch.WordTrace tailWord_1027128 prefixEnd_1027128 468809206836766747267849 := by
  unfold tailWord_1027128
  simp only [CollatzResearch.WordTrace]
  refine ⟨18731217911449075170825019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24974957215265433561100025 18731217911449075170825019)
  ·
    refine ⟨28096826867173612756237529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18731217911449075170825019 28096826867173612756237529)
    ·
      refine ⟨21072620150380209567178147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28096826867173612756237529 21072620150380209567178147)
      ·
        refine ⟨31608930225570314350767221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21072620150380209567178147 31608930225570314350767221)
        ·
          refine ⟨2963337208647216970384427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31608930225570314350767221 2963337208647216970384427)
          ·
            refine ⟨4445005812970825455576641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2963337208647216970384427 4445005812970825455576641)
            ·
              refine ⟨3333754359728119091682481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4445005812970825455576641 3333754359728119091682481)
              ·
                refine ⟨2500315769796089318761861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3333754359728119091682481 2500315769796089318761861)
                ·
                  refine ⟨468809206836766747267849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2500315769796089318761861 468809206836766747267849)
                  ·
                    rfl

theorem cell20_1027128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_1027128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027128 prefixEnd_1027128 := by exact prefixLift 1027128
  have htrace : WordTrace (prefixWord ++ tailWord_1027128) baseStart_1027128 baseEnd_1027128 := by
    simpa [prefixWord, tailWord_1027128, baseEnd_1027128] using wordTrace_append hprefix tailTrace_1027128
  have hstable : (prefixWord ++ tailWord_1027128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027128).length < 2 ^ (prefixWord ++ tailWord_1027128).sum := by decide
  have hdescent : baseEnd_1027128 < baseStart_1027128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027158 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_1027158 : Nat := 118140960795 + 1027158 * 2 ^ 59
def prefixEnd_1027158 : Nat := 4983230072969 + 3 ^ 40 * 1027158 * 2
def baseEnd_1027158 : Nat := 468822899654219976267727

theorem tailTrace_1027158 : CollatzResearch.WordTrace tailWord_1027158 prefixEnd_1027158 468822899654219976267727 := by
  unfold tailWord_1027158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2341470625799341591577633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24975686675192976976828085 2341470625799341591577633)
  ·
    refine ⟨1756102969349506193683225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2341470625799341591577633 1756102969349506193683225)
    ·
      refine ⟨1317077227012129645262419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1756102969349506193683225 1317077227012129645262419)
      ·
        refine ⟨1975615840518194467893629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317077227012129645262419 1975615840518194467893629)
        ·
          refine ⟨740855940194322925460111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1975615840518194467893629 740855940194322925460111)
          ·
            refine ⟨1111283910291484388190167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740855940194322925460111 1111283910291484388190167)
            ·
              refine ⟨1666925865437226582285251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111283910291484388190167 1666925865437226582285251)
              ·
                refine ⟨2500388798155839873427877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666925865437226582285251 2500388798155839873427877)
                ·
                  refine ⟨468822899654219976267727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2500388798155839873427877 468822899654219976267727)
                  ·
                    rfl

theorem cell20_1027158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_1027158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027158 prefixEnd_1027158 := by exact prefixLift 1027158
  have htrace : WordTrace (prefixWord ++ tailWord_1027158) baseStart_1027158 baseEnd_1027158 := by
    simpa [prefixWord, tailWord_1027158, baseEnd_1027158] using wordTrace_append hprefix tailTrace_1027158
  have hstable : (prefixWord ++ tailWord_1027158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027158).length < 2 ^ (prefixWord ++ tailWord_1027158).sum := by decide
  have hdescent : baseEnd_1027158 < baseStart_1027158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027173 : List Nat := [1, 3, 1, 3, 2, 1, 4, 5]
def baseStart_1027173 : Nat := 118140960795 + 1027173 * 2 ^ 59
def prefixEnd_1027173 : Nat := 4983230072969 + 3 ^ 40 * 1027173 * 2
def baseEnd_1027173 : Nat := 156276582020982196922555

theorem tailTrace_1027173 : CollatzResearch.WordTrace tailWord_1027173 prefixEnd_1027173 156276582020982196922555 := by
  unfold tailWord_1027173
  simp only [CollatzResearch.WordTrace]
  refine ⟨37464077107735123027038173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24976051405156748684692115 37464077107735123027038173)
  ·
    refine ⟨14049028915400671135139315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37464077107735123027038173 14049028915400671135139315)
    ·
      refine ⟨21073543373101006702708973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14049028915400671135139315 21073543373101006702708973)
      ·
        refine ⟨7902578764912877513515865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21073543373101006702708973 7902578764912877513515865)
        ·
          refine ⟨5926934073684658135136899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7902578764912877513515865 5926934073684658135136899)
          ·
            refine ⟨8890401110526987202705349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5926934073684658135136899 8890401110526987202705349)
            ·
              refine ⟨1666950208223810100507253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8890401110526987202705349 1666950208223810100507253)
              ·
                refine ⟨156276582020982196922555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1666950208223810100507253 156276582020982196922555)
                ·
                  rfl

theorem cell20_1027173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 5].length) (baseStart_1027173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027173 prefixEnd_1027173 := by exact prefixLift 1027173
  have htrace : WordTrace (prefixWord ++ tailWord_1027173) baseStart_1027173 baseEnd_1027173 := by
    simpa [prefixWord, tailWord_1027173, baseEnd_1027173] using wordTrace_append hprefix tailTrace_1027173
  have hstable : (prefixWord ++ tailWord_1027173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027173).length < 2 ^ (prefixWord ++ tailWord_1027173).sum := by decide
  have hdescent : baseEnd_1027173 < baseStart_1027173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027214 : List Nat := [4, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_1027214 : Nat := 118140960795 + 1027214 * 2 ^ 59
def prefixEnd_1027214 : Nat := 4983230072969 + 3 ^ 40 * 1027214 * 2
def baseEnd_1027214 : Nat := 468848459580132670400831

theorem tailTrace_1027214 : CollatzResearch.WordTrace tailWord_1027214 prefixEnd_1027214 468848459580132670400831 := by
  unfold tailWord_1027214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4683196562573323378660087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24977048333724391352853797 4683196562573323378660087)
  ·
    refine ⟨7024794843859985067990131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4683196562573323378660087 7024794843859985067990131)
    ·
      refine ⟨10537192265789977601985197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7024794843859985067990131 10537192265789977601985197)
      ·
        refine ⟨3951447099671241600744449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10537192265789977601985197 3951447099671241600744449)
        ·
          refine ⟨2963585324753431200558337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3951447099671241600744449 2963585324753431200558337)
          ·
            refine ⟨2222688993565073400418753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2963585324753431200558337 2222688993565073400418753)
            ·
              refine ⟨1667016745173805050314065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2222688993565073400418753 1667016745173805050314065)
              ·
                refine ⟨1250262558880353787735549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667016745173805050314065 1250262558880353787735549)
                ·
                  refine ⟨468848459580132670400831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1250262558880353787735549 468848459580132670400831)
                  ·
                    rfl

theorem cell20_1027214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_1027214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027214 prefixEnd_1027214 := by exact prefixLift 1027214
  have htrace : WordTrace (prefixWord ++ tailWord_1027214) baseStart_1027214 baseEnd_1027214 := by
    simpa [prefixWord, tailWord_1027214, baseEnd_1027214] using wordTrace_append hprefix tailTrace_1027214
  have hstable : (prefixWord ++ tailWord_1027214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027214).length < 2 ^ (prefixWord ++ tailWord_1027214).sum := by decide
  have hdescent : baseEnd_1027214 < baseStart_1027214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027228 : List Nat := [2, 2, 3, 2, 1, 4, 1, 5]
def baseStart_1027228 : Nat := 118140960795 + 1027228 * 2 ^ 59
def prefixEnd_1027228 : Nat := 4983230072969 + 3 ^ 40 * 1027228 * 2
def baseEnd_1027228 : Nat := 156284949853870281311369

theorem tailTrace_1027228 : CollatzResearch.WordTrace tailWord_1027228 prefixEnd_1027228 156284949853870281311369 := by
  unfold tailWord_1027228
  simp only [CollatzResearch.WordTrace]
  refine ⟨18733041561267933710145169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24977388748357244946860225 18733041561267933710145169)
  ·
    refine ⟨14049781170950950282608877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18733041561267933710145169 14049781170950950282608877)
    ·
      refine ⟨5268667939106606355978329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14049781170950950282608877 5268667939106606355978329)
      ·
        refine ⟨3951500954329954766983747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5268667939106606355978329 3951500954329954766983747)
        ·
          refine ⟨5927251431494932150475621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3951500954329954766983747 5927251431494932150475621)
          ·
            refine ⟨1111359643405299778214179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5927251431494932150475621 1111359643405299778214179)
            ·
              refine ⟨1667039465107949667321269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111359643405299778214179 1667039465107949667321269)
              ·
                refine ⟨156284949853870281311369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1667039465107949667321269 156284949853870281311369)
                ·
                  rfl

theorem cell20_1027228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_1027228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027228 prefixEnd_1027228 := by exact prefixLift 1027228
  have htrace : WordTrace (prefixWord ++ tailWord_1027228) baseStart_1027228 baseEnd_1027228 := by
    simpa [prefixWord, tailWord_1027228, baseEnd_1027228] using wordTrace_append hprefix tailTrace_1027228
  have hstable : (prefixWord ++ tailWord_1027228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027228).length < 2 ^ (prefixWord ++ tailWord_1027228).sum := by decide
  have hdescent : baseEnd_1027228 < baseStart_1027228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027245 : List Nat := [1, 5, 2, 1, 3, 1, 3, 4]
def baseStart_1027245 : Nat := 118140960795 + 1027245 * 2 ^ 59
def prefixEnd_1027245 : Nat := 4983230072969 + 3 ^ 40 * 1027245 * 2
def baseEnd_1027245 : Nat := 156287536274944780122457

theorem tailTrace_1027245 : CollatzResearch.WordTrace tailWord_1027245 prefixEnd_1027245 156287536274944780122457 := by
  unfold tailWord_1027245
  simp only [CollatzResearch.WordTrace]
  refine ⟨37466703163474279323659189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24977802108982852882439459 37466703163474279323659189)
  ·
    refine ⟨3512503421575713686593049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37466703163474279323659189 3512503421575713686593049)
    ·
      refine ⟨2634377566181785264944787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3512503421575713686593049 2634377566181785264944787)
      ·
        refine ⟨3951566349272677897417181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2634377566181785264944787 3951566349272677897417181)
        ·
          refine ⟨1481837380977254211531443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3951566349272677897417181 1481837380977254211531443)
          ·
            refine ⟨2222756071465881317297165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481837380977254211531443 2222756071465881317297165)
            ·
              refine ⟨833533526799705493986437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2222756071465881317297165 833533526799705493986437)
              ·
                refine ⟨156287536274944780122457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 833533526799705493986437 156287536274944780122457)
                ·
                  rfl

theorem cell20_1027245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 4].length) (baseStart_1027245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027245 prefixEnd_1027245 := by exact prefixLift 1027245
  have htrace : WordTrace (prefixWord ++ tailWord_1027245) baseStart_1027245 baseEnd_1027245 := by
    simpa [prefixWord, tailWord_1027245, baseEnd_1027245] using wordTrace_append hprefix tailTrace_1027245
  have hstable : (prefixWord ++ tailWord_1027245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027245).length < 2 ^ (prefixWord ++ tailWord_1027245).sum := by decide
  have hdescent : baseEnd_1027245 < baseStart_1027245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027286 : List Nat := [5, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1027286 : Nat := 118140960795 + 1027286 * 2 ^ 59
def prefixEnd_1027286 : Nat := 4983230072969 + 3 ^ 40 * 1027286 * 2
def baseEnd_1027286 : Nat := 468881322342020420000537

theorem tailTrace_1027286 : CollatzResearch.WordTrace tailWord_1027286 prefixEnd_1027286 468881322342020420000537 := by
  unfold tailWord_1027286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2341762409770358957868857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24978799037550495550601141 2341762409770358957868857)
  ·
    refine ⟨1756321807327769218401643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2341762409770358957868857 1756321807327769218401643)
    ·
      refine ⟨2634482710991653827602465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1756321807327769218401643 2634482710991653827602465)
      ·
        refine ⟨1975862033243740370701849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2634482710991653827602465 1975862033243740370701849)
        ·
          refine ⟨1481896524932805278026387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1975862033243740370701849 1481896524932805278026387)
          ·
            refine ⟨2222844787399207917039581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481896524932805278026387 2222844787399207917039581)
            ·
              refine ⟨833566795274702968889843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2222844787399207917039581 833566795274702968889843)
              ·
                refine ⟨1250350192912054453334765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833566795274702968889843 1250350192912054453334765)
                ·
                  refine ⟨468881322342020420000537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1250350192912054453334765 468881322342020420000537)
                  ·
                    rfl

theorem cell20_1027286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1027286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027286 prefixEnd_1027286 := by exact prefixLift 1027286
  have htrace : WordTrace (prefixWord ++ tailWord_1027286) baseStart_1027286 baseEnd_1027286 := by
    simpa [prefixWord, tailWord_1027286, baseEnd_1027286] using wordTrace_append hprefix tailTrace_1027286
  have hstable : (prefixWord ++ tailWord_1027286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027286).length < 2 ^ (prefixWord ++ tailWord_1027286).sum := by decide
  have hdescent : baseEnd_1027286 < baseStart_1027286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027408 : List Nat := [2, 1, 1, 1, 1, 5, 1, 5, 3]
def baseStart_1027408 : Nat := 118140960795 + 1027408 * 2 ^ 59
def prefixEnd_1027408 : Nat := 4983230072969 + 3 ^ 40 * 1027408 * 2
def baseEnd_1027408 : Nat := 468937006466330217933371

theorem tailTrace_1027408 : CollatzResearch.WordTrace tailWord_1027408 prefixEnd_1027408 468937006466330217933371 := by
  unfold tailWord_1027408
  simp only [CollatzResearch.WordTrace]
  refine ⟨18736324130941879080921439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24981765507922505441228585 18736324130941879080921439)
  ·
    refine ⟨28104486196412818621382159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18736324130941879080921439 28104486196412818621382159)
    ·
      refine ⟨42156729294619227932073239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28104486196412818621382159 42156729294619227932073239)
      ·
        refine ⟨63235093941928841898109859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42156729294619227932073239 63235093941928841898109859)
        ·
          refine ⟨94852640912893262847164789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63235093941928841898109859 94852640912893262847164789)
          ·
            refine ⟨8892435085583743391921699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94852640912893262847164789 8892435085583743391921699)
            ·
              refine ⟨13338652628375615087882549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8892435085583743391921699 13338652628375615087882549)
              ·
                refine ⟨1250498683910213914488989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13338652628375615087882549 1250498683910213914488989)
                ·
                  refine ⟨468937006466330217933371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1250498683910213914488989 468937006466330217933371)
                  ·
                    rfl

theorem cell20_1027408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_1027408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027408 prefixEnd_1027408 := by exact prefixLift 1027408
  have htrace : WordTrace (prefixWord ++ tailWord_1027408) baseStart_1027408 baseEnd_1027408 := by
    simpa [prefixWord, tailWord_1027408, baseEnd_1027408] using wordTrace_append hprefix tailTrace_1027408
  have hstable : (prefixWord ++ tailWord_1027408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027408).length < 2 ^ (prefixWord ++ tailWord_1027408).sum := by decide
  have hdescent : baseEnd_1027408 < baseStart_1027408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027415 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 6]
def baseStart_1027415 : Nat := 118140960795 + 1027415 * 2 ^ 59
def prefixEnd_1027415 : Nat := 4983230072969 + 3 ^ 40 * 1027415 * 2
def baseEnd_1027415 : Nat := 468940201457069304700009

theorem tailTrace_1027415 : CollatzResearch.WordTrace tailWord_1027415 prefixEnd_1027415 468940201457069304700009 := by
  unfold tailWord_1027415
  simp only [CollatzResearch.WordTrace]
  refine ⟨37472903572858398357347699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24981935715238932238231799 37472903572858398357347699)
  ·
    refine ⟨56209355359287597536021549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37472903572858398357347699 56209355359287597536021549)
    ·
      refine ⟨21078508259732849076008081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56209355359287597536021549 21078508259732849076008081)
      ·
        refine ⟨15808881194799636807006061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21078508259732849076008081 15808881194799636807006061)
        ·
          refine ⟨5928330448049863802627273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15808881194799636807006061 5928330448049863802627273)
          ·
            refine ⟨4446247836037397851970455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5928330448049863802627273 4446247836037397851970455)
            ·
              refine ⟨6669371754056096777955683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4446247836037397851970455 6669371754056096777955683)
              ·
                refine ⟨10004057631084145166933525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6669371754056096777955683 10004057631084145166933525)
                ·
                  refine ⟨468940201457069304700009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10004057631084145166933525 468940201457069304700009)
                  ·
                    rfl

theorem cell20_1027415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_1027415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027415 prefixEnd_1027415 := by exact prefixLift 1027415
  have htrace : WordTrace (prefixWord ++ tailWord_1027415) baseStart_1027415 baseEnd_1027415 := by
    simpa [prefixWord, tailWord_1027415, baseEnd_1027415] using wordTrace_append hprefix tailTrace_1027415
  have hstable : (prefixWord ++ tailWord_1027415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027415).length < 2 ^ (prefixWord ++ tailWord_1027415).sum := by decide
  have hdescent : baseEnd_1027415 < baseStart_1027415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027438 : List Nat := [4, 1, 2, 4, 2, 1, 1, 2, 3]
def baseStart_1027438 : Nat := 118140960795 + 1027438 * 2 ^ 59
def prefixEnd_1027438 : Nat := 4983230072969 + 3 ^ 40 * 1027438 * 2
def baseEnd_1027438 : Nat := 468950699283783446933249

theorem tailTrace_1027438 : CollatzResearch.WordTrace tailWord_1027438 prefixEnd_1027438 468950699283783446933249 := by
  unfold tailWord_1027438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4684217806471884160679371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24982494967850048856956645 4684217806471884160679371)
  ·
    refine ⟨7026326709707826241019057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4684217806471884160679371 7026326709707826241019057)
    ·
      refine ⟨5269745032280869680764293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7026326709707826241019057 5269745032280869680764293)
      ·
        refine ⟨988077193552663065143305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5269745032280869680764293 988077193552663065143305)
        ·
          refine ⟨741057895164497298857479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 988077193552663065143305 741057895164497298857479)
          ·
            refine ⟨1111586842746745948286219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741057895164497298857479 1111586842746745948286219)
            ·
              refine ⟨1667380264120118922429329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111586842746745948286219 1667380264120118922429329)
              ·
                refine ⟨1250535198090089191821997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667380264120118922429329 1250535198090089191821997)
                ·
                  refine ⟨468950699283783446933249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1250535198090089191821997 468950699283783446933249)
                  ·
                    rfl

theorem cell20_1027438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_1027438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027438 prefixEnd_1027438 := by exact prefixLift 1027438
  have htrace : WordTrace (prefixWord ++ tailWord_1027438) baseStart_1027438 baseEnd_1027438 := by
    simpa [prefixWord, tailWord_1027438, baseEnd_1027438] using wordTrace_append hprefix tailTrace_1027438
  have hstable : (prefixWord ++ tailWord_1027438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027438).length < 2 ^ (prefixWord ++ tailWord_1027438).sum := by decide
  have hdescent : baseEnd_1027438 < baseStart_1027438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027477 : List Nat := [1, 3, 2, 1, 1, 2, 6, 4]
def baseStart_1027477 : Nat := 118140960795 + 1027477 * 2 ^ 59
def prefixEnd_1027477 : Nat := 4983230072969 + 3 ^ 40 * 1027477 * 2
def baseEnd_1027477 : Nat := 156322833315490881544363

theorem tailTrace_1027477 : CollatzResearch.WordTrace tailWord_1027477 prefixEnd_1027477 156322833315490881544363 := by
  unfold tailWord_1027477
  simp only [CollatzResearch.WordTrace]
  refine ⟨37475164898633782946104685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24983443265755855297403123 37475164898633782946104685)
  ·
    refine ⟨14053186836987668604789257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37475164898633782946104685 14053186836987668604789257)
    ·
      refine ⟨10539890127740751453591943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14053186836987668604789257 10539890127740751453591943)
      ·
        refine ⟨15809835191611127180387915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10539890127740751453591943 15809835191611127180387915)
        ·
          refine ⟨23714752787416690770581873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15809835191611127180387915 23714752787416690770581873)
          ·
            refine ⟨17786064590562518077936405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23714752787416690770581873 17786064590562518077936405)
            ·
              refine ⟨833721777682618034903269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17786064590562518077936405 833721777682618034903269)
              ·
                refine ⟨156322833315490881544363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 833721777682618034903269 156322833315490881544363)
                ·
                  rfl

theorem cell20_1027477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 4].length) (baseStart_1027477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027477 prefixEnd_1027477 := by exact prefixLift 1027477
  have htrace : WordTrace (prefixWord ++ tailWord_1027477) baseStart_1027477 baseEnd_1027477 := by
    simpa [prefixWord, tailWord_1027477, baseEnd_1027477] using wordTrace_append hprefix tailTrace_1027477
  have hstable : (prefixWord ++ tailWord_1027477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027477).length < 2 ^ (prefixWord ++ tailWord_1027477).sum := by decide
  have hdescent : baseEnd_1027477 < baseStart_1027477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027487 : List Nat := [1, 1, 2, 5, 1, 2, 3, 3, 2]
def baseStart_1027487 : Nat := 118140960795 + 1027487 * 2 ^ 59
def prefixEnd_1027487 : Nat := 4983230072969 + 3 ^ 40 * 1027487 * 2
def baseEnd_1027487 : Nat := 468973064218957054299715

theorem tailTrace_1027487 : CollatzResearch.WordTrace tailWord_1027487 prefixEnd_1027487 468973064218957054299715 := by
  unfold tailWord_1027487
  simp only [CollatzResearch.WordTrace]
  refine ⟨37475529628597554653968715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24983686419065036435979143 37475529628597554653968715)
  ·
    refine ⟨56213294442896331980953073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37475529628597554653968715 56213294442896331980953073)
    ·
      refine ⟨42159970832172248985714805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56213294442896331980953073 42159970832172248985714805)
      ·
        refine ⟨3952497265516148342410763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42159970832172248985714805 3952497265516148342410763)
        ·
          refine ⟨5928745898274222513616145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3952497265516148342410763 5928745898274222513616145)
          ·
            refine ⟨4446559423705666885212109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5928745898274222513616145 4446559423705666885212109)
            ·
              refine ⟨1667459783889625081954541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4446559423705666885212109 1667459783889625081954541)
              ·
                refine ⟨625297418958609405732953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1667459783889625081954541 625297418958609405732953)
                ·
                  refine ⟨468973064218957054299715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625297418958609405732953 468973064218957054299715)
                  ·
                    rfl

theorem cell20_1027487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 2].length) (baseStart_1027487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027487 prefixEnd_1027487 := by exact prefixLift 1027487
  have htrace : WordTrace (prefixWord ++ tailWord_1027487) baseStart_1027487 baseEnd_1027487 := by
    simpa [prefixWord, tailWord_1027487, baseEnd_1027487] using wordTrace_append hprefix tailTrace_1027487
  have hstable : (prefixWord ++ tailWord_1027487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027487).length < 2 ^ (prefixWord ++ tailWord_1027487).sum := by decide
  have hdescent : baseEnd_1027487 < baseStart_1027487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027501 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 5]
def baseStart_1027501 : Nat := 118140960795 + 1027501 * 2 ^ 59
def prefixEnd_1027501 : Nat := 4983230072969 + 3 ^ 40 * 1027501 * 2
def baseEnd_1027501 : Nat := 468979454200435227832991

theorem tailTrace_1027501 : CollatzResearch.WordTrace tailWord_1027501 prefixEnd_1027501 468979454200435227832991 := by
  unfold tailWord_1027501
  simp only [CollatzResearch.WordTrace]
  refine ⟨37476040250546835044978357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24984026833697890029985571 37476040250546835044978357)
  ·
    refine ⟨3513378773488765785466721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37476040250546835044978357 3513378773488765785466721)
    ·
      refine ⟨2635034080116574339100041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3513378773488765785466721 2635034080116574339100041)
      ·
        refine ⟨1976275560087430754325031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2635034080116574339100041 1976275560087430754325031)
        ·
          refine ⟨2964413340131146131487547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1976275560087430754325031 2964413340131146131487547)
          ·
            refine ⟨4446620010196719197231321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2964413340131146131487547 4446620010196719197231321)
            ·
              refine ⟨3334965007647539397923491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4446620010196719197231321 3334965007647539397923491)
              ·
                refine ⟨5002447511471309096885237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3334965007647539397923491 5002447511471309096885237)
                ·
                  refine ⟨468979454200435227832991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5002447511471309096885237 468979454200435227832991)
                  ·
                    rfl

theorem cell20_1027501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_1027501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027501 prefixEnd_1027501 := by exact prefixLift 1027501
  have htrace : WordTrace (prefixWord ++ tailWord_1027501) baseStart_1027501 baseEnd_1027501 := by
    simpa [prefixWord, tailWord_1027501, baseEnd_1027501] using wordTrace_append hprefix tailTrace_1027501
  have hstable : (prefixWord ++ tailWord_1027501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027501).length < 2 ^ (prefixWord ++ tailWord_1027501).sum := by decide
  have hdescent : baseEnd_1027501 < baseStart_1027501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027543 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 7]
def baseStart_1027543 : Nat := 118140960795 + 1027543 * 2 ^ 59
def prefixEnd_1027543 : Nat := 4983230072969 + 3 ^ 40 * 1027543 * 2
def baseEnd_1027543 : Nat := 468998624144869748432819

theorem tailTrace_1027543 : CollatzResearch.WordTrace tailWord_1027543 prefixEnd_1027543 468998624144869748432819 := by
  unfold tailWord_1027543
  simp only [CollatzResearch.WordTrace]
  refine ⟨37477572116394676218007283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24985048077596450812004855 37477572116394676218007283)
  ·
    refine ⟨56216358174592014327010925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37477572116394676218007283 56216358174592014327010925)
    ·
      refine ⟨21081134315472005372629097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56216358174592014327010925 21081134315472005372629097)
      ·
        refine ⟨15810850736604004029471823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21081134315472005372629097 15810850736604004029471823)
        ·
          refine ⟨23716276104906006044207735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15810850736604004029471823 23716276104906006044207735)
          ·
            refine ⟨35574414157359009066311603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23716276104906006044207735 35574414157359009066311603)
            ·
              refine ⟨53361621236038513599467405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35574414157359009066311603 53361621236038513599467405)
              ·
                refine ⟨20010607963514442599800277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53361621236038513599467405 20010607963514442599800277)
                ·
                  refine ⟨468998624144869748432819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20010607963514442599800277 468998624144869748432819)
                  ·
                    rfl

theorem cell20_1027543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_1027543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027543 prefixEnd_1027543 := by exact prefixLift 1027543
  have htrace : WordTrace (prefixWord ++ tailWord_1027543) baseStart_1027543 baseEnd_1027543 := by
    simpa [prefixWord, tailWord_1027543, baseEnd_1027543] using wordTrace_append hprefix tailTrace_1027543
  have hstable : (prefixWord ++ tailWord_1027543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027543).length < 2 ^ (prefixWord ++ tailWord_1027543).sum := by decide
  have hdescent : baseEnd_1027543 < baseStart_1027543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027570 : List Nat := [3, 2, 1, 4, 1, 3, 1, 5]
def baseStart_1027570 : Nat := 118140960795 + 1027570 * 2 ^ 59
def prefixEnd_1027570 : Nat := 4983230072969 + 3 ^ 40 * 1027570 * 2
def baseEnd_1027570 : Nat := 156336982560192551510903

theorem tailTrace_1027570 : CollatzResearch.WordTrace tailWord_1027570 prefixEnd_1027570 156336982560192551510903 := by
  unfold tailWord_1027570
  simp only [CollatzResearch.WordTrace]
  refine ⟨9369639221824214957310041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24985704591531239886160109 9369639221824214957310041)
  ·
    refine ⟨7027229416368161217982531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9369639221824214957310041 7027229416368161217982531)
    ·
      refine ⟨10540844124552241826973797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7027229416368161217982531 10540844124552241826973797)
      ·
        refine ⟨1976408273353545342557587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10540844124552241826973797 1976408273353545342557587)
        ·
          refine ⟨2964612410030318013836381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1976408273353545342557587 2964612410030318013836381)
          ·
            refine ⟨1111729653761369255188643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2964612410030318013836381 1111729653761369255188643)
            ·
              refine ⟨1667594480642053882782965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111729653761369255188643 1667594480642053882782965)
              ·
                refine ⟨156336982560192551510903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1667594480642053882782965 156336982560192551510903)
                ·
                  rfl

theorem cell20_1027570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_1027570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027570 prefixEnd_1027570 := by exact prefixLift 1027570
  have htrace : WordTrace (prefixWord ++ tailWord_1027570) baseStart_1027570 baseEnd_1027570 := by
    simpa [prefixWord, tailWord_1027570, baseEnd_1027570] using wordTrace_append hprefix tailTrace_1027570
  have hstable : (prefixWord ++ tailWord_1027570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027570).length < 2 ^ (prefixWord ++ tailWord_1027570).sum := by decide
  have hdescent : baseEnd_1027570 < baseStart_1027570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027612 : List Nat := [2, 2, 3, 1, 2, 1, 9]
def baseStart_1027612 : Nat := 118140960795 + 1027612 * 2 ^ 59
def prefixEnd_1027612 : Nat := 4983230072969 + 3 ^ 40 * 1027612 * 2
def baseEnd_1027612 : Nat := 52114457513890241681393

theorem tailTrace_1027612 : CollatzResearch.WordTrace tailWord_1027612 prefixEnd_1027612 52114457513890241681393 := by
  unfold tailWord_1027612
  simp only [CollatzResearch.WordTrace]
  refine ⟨18740044376572350501134545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24986725835429800668179393 18740044376572350501134545)
  ·
    refine ⟨14055033282429262875850909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18740044376572350501134545 14055033282429262875850909)
    ·
      refine ⟨5270637480910973578444091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14055033282429262875850909 5270637480910973578444091)
      ·
        refine ⟨7905956221366460367666137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5270637480910973578444091 7905956221366460367666137)
        ·
          refine ⟨5929467166024845275749603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7905956221366460367666137 5929467166024845275749603)
          ·
            refine ⟨8894200749037267913624405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5929467166024845275749603 8894200749037267913624405)
            ·
              refine ⟨52114457513890241681393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8894200749037267913624405 52114457513890241681393)
              ·
                rfl

theorem cell20_1027612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 9].length) (baseStart_1027612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027612 prefixEnd_1027612 := by exact prefixLift 1027612
  have htrace : WordTrace (prefixWord ++ tailWord_1027612) baseStart_1027612 baseEnd_1027612 := by
    simpa [prefixWord, tailWord_1027612, baseEnd_1027612] using wordTrace_append hprefix tailTrace_1027612
  have hstable : (prefixWord ++ tailWord_1027612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027612).length < 2 ^ (prefixWord ++ tailWord_1027612).sum := by decide
  have hdescent : baseEnd_1027612 < baseStart_1027612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027726 : List Nat := [4, 1, 1, 3, 1, 10]
def baseStart_1027726 : Nat := 118140960795 + 1027726 * 2 ^ 59
def prefixEnd_1027726 : Nat := 4983230072969 + 3 ^ 40 * 1027726 * 2
def baseEnd_1027726 : Nat := 17373412975234609086373

theorem tailTrace_1027726 : CollatzResearch.WordTrace tailWord_1027726 prefixEnd_1027726 17373412975234609086373 := by
  unfold tailWord_1027726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685530834341462308989879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24989497783154465647946021 4685530834341462308989879)
  ·
    refine ⟨7028296251512193463484819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4685530834341462308989879 7028296251512193463484819)
    ·
      refine ⟨10542444377268290195227229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7028296251512193463484819 10542444377268290195227229)
      ·
        refine ⟨3953416641475608823210211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10542444377268290195227229 3953416641475608823210211)
        ·
          refine ⟨5930124962213413234815317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3953416641475608823210211 5930124962213413234815317)
          ·
            refine ⟨17373412975234609086373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5930124962213413234815317 17373412975234609086373)
            ·
              rfl

theorem cell20_1027726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 10].length) (baseStart_1027726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027726 prefixEnd_1027726 := by exact prefixLift 1027726
  have htrace : WordTrace (prefixWord ++ tailWord_1027726) baseStart_1027726 baseEnd_1027726 := by
    simpa [prefixWord, tailWord_1027726, baseEnd_1027726] using wordTrace_append hprefix tailTrace_1027726
  have hstable : (prefixWord ++ tailWord_1027726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027726).length < 2 ^ (prefixWord ++ tailWord_1027726).sum := by decide
  have hdescent : baseEnd_1027726 < baseStart_1027726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027732 : List Nat := [2, 4, 2, 2, 2, 1, 1, 4, 2]
def baseStart_1027732 : Nat := 118140960795 + 1027732 * 2 ^ 59
def prefixEnd_1027732 : Nat := 4983230072969 + 3 ^ 40 * 1027732 * 2
def baseEnd_1027732 : Nat := 469084888894825091132047

theorem tailTrace_1027732 : CollatzResearch.WordTrace tailWord_1027732 prefixEnd_1027732 469084888894825091132047 := by
  unfold tailWord_1027732
  simp only [CollatzResearch.WordTrace]
  refine ⟨18742232756354980748318725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24989643675139974331091633 18742232756354980748318725)
  ·
    refine ⟨3514168641816558890309761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18742232756354980748318725 3514168641816558890309761)
    ·
      refine ⟨2635626481362419167732321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3514168641816558890309761 2635626481362419167732321)
      ·
        refine ⟨1976719861021814375799241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2635626481362419167732321 1976719861021814375799241)
        ·
          refine ⟨1482539895766360781849431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1976719861021814375799241 1482539895766360781849431)
          ·
            refine ⟨2223809843649541172774147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482539895766360781849431 2223809843649541172774147)
            ·
              refine ⟨3335714765474311759161221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223809843649541172774147 3335714765474311759161221)
              ·
                refine ⟨625446518526433454842729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3335714765474311759161221 625446518526433454842729)
                ·
                  refine ⟨469084888894825091132047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625446518526433454842729 469084888894825091132047)
                  ·
                    rfl

theorem cell20_1027732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_1027732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027732 prefixEnd_1027732 := by exact prefixLift 1027732
  have htrace : WordTrace (prefixWord ++ tailWord_1027732) baseStart_1027732 baseEnd_1027732 := by
    simpa [prefixWord, tailWord_1027732, baseEnd_1027732] using wordTrace_append hprefix tailTrace_1027732
  have hstable : (prefixWord ++ tailWord_1027732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027732).length < 2 ^ (prefixWord ++ tailWord_1027732).sum := by decide
  have hdescent : baseEnd_1027732 < baseStart_1027732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027733 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 5]
def baseStart_1027733 : Nat := 118140960795 + 1027733 * 2 ^ 59
def prefixEnd_1027733 : Nat := 4983230072969 + 3 ^ 40 * 1027733 * 2
def baseEnd_1027733 : Nat := 469085345322073532098709

theorem tailTrace_1027733 : CollatzResearch.WordTrace tailWord_1027733 prefixEnd_1027733 469085345322073532098709 := by
  unfold tailWord_1027733
  simp only [CollatzResearch.WordTrace]
  refine ⟨37484501985706338667423853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24989667990470892444949235 37484501985706338667423853)
  ·
    refine ⟨14056688244639877000283945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37484501985706338667423853 14056688244639877000283945)
    ·
      refine ⟨10542516183479907750212959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14056688244639877000283945 10542516183479907750212959)
      ·
        refine ⟨15813774275219861625319439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10542516183479907750212959 15813774275219861625319439)
        ·
          refine ⟨23720661412829792437979159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15813774275219861625319439 23720661412829792437979159)
          ·
            refine ⟨35580992119244688656968739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23720661412829792437979159 35580992119244688656968739)
            ·
              refine ⟨53371488178867032985453109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35580992119244688656968739 53371488178867032985453109)
              ·
                refine ⟨5003577016768784342386229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53371488178867032985453109 5003577016768784342386229)
                ·
                  refine ⟨469085345322073532098709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5003577016768784342386229 469085345322073532098709)
                  ·
                    rfl

theorem cell20_1027733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_1027733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027733 prefixEnd_1027733 := by exact prefixLift 1027733
  have htrace : WordTrace (prefixWord ++ tailWord_1027733) baseStart_1027733 baseEnd_1027733 := by
    simpa [prefixWord, tailWord_1027733, baseEnd_1027733] using wordTrace_append hprefix tailTrace_1027733
  have hstable : (prefixWord ++ tailWord_1027733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027733).length < 2 ^ (prefixWord ++ tailWord_1027733).sum := by decide
  have hdescent : baseEnd_1027733 < baseStart_1027733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027815 : List Nat := [1, 1, 5, 4, 1, 2, 2, 4]
def baseStart_1027815 : Nat := 118140960795 + 1027815 * 2 ^ 59
def prefixEnd_1027815 : Nat := 4983230072969 + 3 ^ 40 * 1027815 * 2
def baseEnd_1027815 : Nat := 156374257452148563788347

theorem tailTrace_1027815 : CollatzResearch.WordTrace tailWord_1027815 prefixEnd_1027815 156374257452148563788347 := by
  unfold tailWord_1027815
  simp only [CollatzResearch.WordTrace]
  refine ⟨37487492771409266671908899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24991661847606177781272599 37487492771409266671908899)
  ·
    refine ⟨56231239157113900007863349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37487492771409266671908899 56231239157113900007863349)
    ·
      refine ⟨5271678670979428125737189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56231239157113900007863349 5271678670979428125737189)
      ·
        refine ⟨988439750808642773575723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5271678670979428125737189 988439750808642773575723)
        ·
          refine ⟨1482659626212964160363585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988439750808642773575723 1482659626212964160363585)
          ·
            refine ⟨1111994719659723120272689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1482659626212964160363585 1111994719659723120272689)
            ·
              refine ⟨833996039744792340204517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1111994719659723120272689 833996039744792340204517)
              ·
                refine ⟨156374257452148563788347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 833996039744792340204517 156374257452148563788347)
                ·
                  rfl

theorem cell20_1027815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 4].length) (baseStart_1027815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027815 prefixEnd_1027815 := by exact prefixLift 1027815
  have htrace : WordTrace (prefixWord ++ tailWord_1027815) baseStart_1027815 baseEnd_1027815 := by
    simpa [prefixWord, tailWord_1027815, baseEnd_1027815] using wordTrace_append hprefix tailTrace_1027815
  have hstable : (prefixWord ++ tailWord_1027815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027815).length < 2 ^ (prefixWord ++ tailWord_1027815).sum := by decide
  have hdescent : baseEnd_1027815 < baseStart_1027815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027850 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 4]
def baseStart_1027850 : Nat := 118140960795 + 1027850 * 2 ^ 59
def prefixEnd_1027850 : Nat := 4983230072969 + 3 ^ 40 * 1027850 * 2
def baseEnd_1027850 : Nat := 469138747310141125198231

theorem tailTrace_1027850 : CollatzResearch.WordTrace tailWord_1027850 prefixEnd_1027850 469138747310141125198231 := by
  unfold tailWord_1027850
  simp only [CollatzResearch.WordTrace]
  refine ⟨9372192331570616912358251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24992512884188311766288669 9372192331570616912358251)
  ·
    refine ⟨14058288497355925368537377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9372192331570616912358251 14058288497355925368537377)
    ·
      refine ⟨10543716373016944026403033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14058288497355925368537377 10543716373016944026403033)
      ·
        refine ⟨7907787279762708019802275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10543716373016944026403033 7907787279762708019802275)
        ·
          refine ⟨11861680919644062029703413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7907787279762708019802275 11861680919644062029703413)
          ·
            refine ⟨1112032586216630815284695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11861680919644062029703413 1112032586216630815284695)
            ·
              refine ⟨1668048879324946222927043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112032586216630815284695 1668048879324946222927043)
              ·
                refine ⟨2502073318987419334390565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1668048879324946222927043 2502073318987419334390565)
                ·
                  refine ⟨469138747310141125198231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2502073318987419334390565 469138747310141125198231)
                  ·
                    rfl

theorem cell20_1027850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_1027850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027850 prefixEnd_1027850 := by exact prefixLift 1027850
  have htrace : WordTrace (prefixWord ++ tailWord_1027850) baseStart_1027850 baseEnd_1027850 := by
    simpa [prefixWord, tailWord_1027850, baseEnd_1027850] using wordTrace_append hprefix tailTrace_1027850
  have hstable : (prefixWord ++ tailWord_1027850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027850).length < 2 ^ (prefixWord ++ tailWord_1027850).sum := by decide
  have hdescent : baseEnd_1027850 < baseStart_1027850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027961 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 5]
def baseStart_1027961 : Nat := 118140960795 + 1027961 * 2 ^ 59
def prefixEnd_1027961 : Nat := 4983230072969 + 3 ^ 40 * 1027961 * 2
def baseEnd_1027961 : Nat := 469189410734718072497777

theorem tailTrace_1027961 : CollatzResearch.WordTrace tailWord_1027961 prefixEnd_1027961 469189410734718072497777 := by
  unfold tailWord_1027961
  simp only [CollatzResearch.WordTrace]
  refine ⟨37492817828880333606723737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24995211885920222404482491 37492817828880333606723737)
  ·
    refine ⟨28119613371660250205042803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37492817828880333606723737 28119613371660250205042803)
    ·
      refine ⟨42179420057490375307564205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28119613371660250205042803 42179420057490375307564205)
      ·
        refine ⟨15817282521558890740336577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42179420057490375307564205 15817282521558890740336577)
        ·
          refine ⟨11862961891169168055252433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15817282521558890740336577 11862961891169168055252433)
          ·
            refine ⟨8897221418376876041439325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11862961891169168055252433 8897221418376876041439325)
            ·
              refine ⟨3336458031891328515539747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8897221418376876041439325 3336458031891328515539747)
              ·
                refine ⟨5004687047836992773309621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3336458031891328515539747 5004687047836992773309621)
                ·
                  refine ⟨469189410734718072497777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5004687047836992773309621 469189410734718072497777)
                  ·
                    rfl

theorem cell20_1027961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_1027961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027961 prefixEnd_1027961 := by exact prefixLift 1027961
  have htrace : WordTrace (prefixWord ++ tailWord_1027961) baseStart_1027961 baseEnd_1027961 := by
    simpa [prefixWord, tailWord_1027961, baseEnd_1027961] using wordTrace_append hprefix tailTrace_1027961
  have hstable : (prefixWord ++ tailWord_1027961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027961).length < 2 ^ (prefixWord ++ tailWord_1027961).sum := by decide
  have hdescent : baseEnd_1027961 < baseStart_1027961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1027988 : List Nat := [2, 4, 2, 1, 1, 4, 2, 4]
def baseStart_1027988 : Nat := 118140960795 + 1027988 * 2 ^ 59
def prefixEnd_1027988 : Nat := 4983230072969 + 3 ^ 40 * 1027988 * 2
def baseEnd_1027988 : Nat := 156400578090141992865889

theorem tailTrace_1027988 : CollatzResearch.WordTrace tailWord_1027988 prefixEnd_1027988 156400578090141992865889 := by
  unfold tailWord_1027988
  simp only [CollatzResearch.WordTrace]
  refine ⟨18746901299891258608978309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24995868399855011478637745 18746901299891258608978309)
  ·
    refine ⟨3515043993729610989183433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18746901299891258608978309 3515043993729610989183433)
    ·
      refine ⟨2636282995297208241887575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3515043993729610989183433 2636282995297208241887575)
      ·
        refine ⟨3954424492945812362831363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2636282995297208241887575 3954424492945812362831363)
        ·
          refine ⟨5931636739418718544247045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3954424492945812362831363 5931636739418718544247045)
          ·
            refine ⟨1112181888641009727046321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5931636739418718544247045 1112181888641009727046321)
            ·
              refine ⟨834136416480757295284741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112181888641009727046321 834136416480757295284741)
              ·
                refine ⟨156400578090141992865889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 834136416480757295284741 156400578090141992865889)
                ·
                  rfl

theorem cell20_1027988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_1027988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1027988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1027988 prefixEnd_1027988 := by exact prefixLift 1027988
  have htrace : WordTrace (prefixWord ++ tailWord_1027988) baseStart_1027988 baseEnd_1027988 := by
    simpa [prefixWord, tailWord_1027988, baseEnd_1027988] using wordTrace_append hprefix tailTrace_1027988
  have hstable : (prefixWord ++ tailWord_1027988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1027988).length < 2 ^ (prefixWord ++ tailWord_1027988).sum := by decide
  have hdescent : baseEnd_1027988 < baseStart_1027988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1027988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028030 : List Nat := [4, 2, 1, 1, 1, 3, 1, 7]
def baseStart_1028030 : Nat := 118140960795 + 1028030 * 2 ^ 59
def prefixEnd_1028030 : Nat := 4983230072969 + 3 ^ 40 * 1028030 * 2
def baseEnd_1028030 : Nat := 156406968071620166399165

theorem tailTrace_1028030 : CollatzResearch.WordTrace tailWord_1028030 prefixEnd_1028030 156406968071620166399165 := by
  unfold tailWord_1028030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4686916808203794798873193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24996889643753572260657029 4686916808203794798873193)
  ·
    refine ⟨3515187606152846099154895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4686916808203794798873193 3515187606152846099154895)
    ·
      refine ⟨5272781409229269148732343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3515187606152846099154895 5272781409229269148732343)
      ·
        refine ⟨7909172113843903723098515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5272781409229269148732343 7909172113843903723098515)
        ·
          refine ⟨11863758170765855584647773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7909172113843903723098515 11863758170765855584647773)
          ·
            refine ⟨4448909314037195844242915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11863758170765855584647773 4448909314037195844242915)
            ·
              refine ⟨6673363971055793766364373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448909314037195844242915 6673363971055793766364373)
              ·
                refine ⟨156406968071620166399165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6673363971055793766364373 156406968071620166399165)
                ·
                  rfl

theorem cell20_1028030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_1028030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028030 prefixEnd_1028030 := by exact prefixLift 1028030
  have htrace : WordTrace (prefixWord ++ tailWord_1028030) baseStart_1028030 baseEnd_1028030 := by
    simpa [prefixWord, tailWord_1028030, baseEnd_1028030] using wordTrace_append hprefix tailTrace_1028030
  have hstable : (prefixWord ++ tailWord_1028030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028030).length < 2 ^ (prefixWord ++ tailWord_1028030).sum := by decide
  have hdescent : baseEnd_1028030 < baseStart_1028030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028071 : List Nat := [1, 1, 5, 2, 3, 1, 2, 2, 3]
def baseStart_1028071 : Nat := 118140960795 + 1028071 * 2 ^ 59
def prefixEnd_1028071 : Nat := 4983230072969 + 3 ^ 40 * 1028071 * 2
def baseEnd_1028071 : Nat := 469239617732046578830661

theorem tailTrace_1028071 : CollatzResearch.WordTrace tailWord_1028071 prefixEnd_1028071 469239617732046578830661 := by
  unfold tailWord_1028071
  simp only [CollatzResearch.WordTrace]
  refine ⟨37496829858481822393228067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24997886572321214928818711 37496829858481822393228067)
  ·
    refine ⟨56245244787722733589842101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37496829858481822393228067 56245244787722733589842101)
    ·
      refine ⟨5272991698849006274047697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56245244787722733589842101 5272991698849006274047697)
      ·
        refine ⟨3954743774136754705535773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5272991698849006274047697 3954743774136754705535773)
        ·
          refine ⟨1483028915301283014575915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3954743774136754705535773 1483028915301283014575915)
          ·
            refine ⟨2224543372951924521863873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483028915301283014575915 2224543372951924521863873)
            ·
              refine ⟨1668407529713943391397905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2224543372951924521863873 1668407529713943391397905)
              ·
                refine ⟨1251305647285457543548429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1668407529713943391397905 1251305647285457543548429)
                ·
                  refine ⟨469239617732046578830661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251305647285457543548429 469239617732046578830661)
                  ·
                    rfl

theorem cell20_1028071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 3].length) (baseStart_1028071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028071 prefixEnd_1028071 := by exact prefixLift 1028071
  have htrace : WordTrace (prefixWord ++ tailWord_1028071) baseStart_1028071 baseEnd_1028071 := by
    simpa [prefixWord, tailWord_1028071, baseEnd_1028071] using wordTrace_append hprefix tailTrace_1028071
  have hstable : (prefixWord ++ tailWord_1028071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028071).length < 2 ^ (prefixWord ++ tailWord_1028071).sum := by decide
  have hdescent : baseEnd_1028071 < baseStart_1028071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028120 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 6]
def baseStart_1028120 : Nat := 118140960795 + 1028120 * 2 ^ 59
def prefixEnd_1028120 : Nat := 4983230072969 + 3 ^ 40 * 1028120 * 2
def baseEnd_1028120 : Nat := 469261982667220186197127

theorem tailTrace_1028120 : CollatzResearch.WordTrace tailWord_1028120 prefixEnd_1028120 469261982667220186197127 := by
  unfold tailWord_1028120
  simp only [CollatzResearch.WordTrace]
  refine ⟨18749308517652151880880907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24999078023536202507841209 18749308517652151880880907)
  ·
    refine ⟨28123962776478227821321361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18749308517652151880880907 28123962776478227821321361)
    ·
      refine ⟨21092972082358670865991021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28123962776478227821321361 21092972082358670865991021)
      ·
        refine ⟨7909864530884501574746633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21092972082358670865991021 7909864530884501574746633)
        ·
          refine ⟨5932398398163376181059975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7909864530884501574746633 5932398398163376181059975)
          ·
            refine ⟨8898597597245064271589963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5932398398163376181059975 8898597597245064271589963)
            ·
              refine ⟨13347896395867596407384945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8898597597245064271589963 13347896395867596407384945)
              ·
                refine ⟨10010922296900697305538709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13347896395867596407384945 10010922296900697305538709)
                ·
                  refine ⟨469261982667220186197127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10010922296900697305538709 469261982667220186197127)
                  ·
                    rfl

theorem cell20_1028120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_1028120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028120 prefixEnd_1028120 := by exact prefixLift 1028120
  have htrace : WordTrace (prefixWord ++ tailWord_1028120) baseStart_1028120 baseEnd_1028120 := by
    simpa [prefixWord, tailWord_1028120, baseEnd_1028120] using wordTrace_append hprefix tailTrace_1028120
  have hstable : (prefixWord ++ tailWord_1028120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028120).length < 2 ^ (prefixWord ++ tailWord_1028120).sum := by decide
  have hdescent : baseEnd_1028120 < baseStart_1028120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028127 : List Nat := [1, 1, 2, 4, 1, 2, 9]
def baseStart_1028127 : Nat := 118140960795 + 1028127 * 2 ^ 59
def prefixEnd_1028127 : Nat := 4983230072969 + 3 ^ 40 * 1028127 * 2
def baseEnd_1028127 : Nat := 52140575295328808107085

theorem tailTrace_1028127 : CollatzResearch.WordTrace tailWord_1028127 prefixEnd_1028127 52140575295328808107085 := by
  unfold tailWord_1028127
  simp only [CollatzResearch.WordTrace]
  refine ⟨37498872346278943957266635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24999248230852629304844423 37498872346278943957266635)
  ·
    refine ⟨56248308519418415935899953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37498872346278943957266635 56248308519418415935899953)
    ·
      refine ⟨42186231389563811951924965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56248308519418415935899953 42186231389563811951924965)
      ·
        refine ⟨7909918385543214740985931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42186231389563811951924965 7909918385543214740985931)
        ·
          refine ⟨11864877578314822111478897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7909918385543214740985931 11864877578314822111478897)
          ·
            refine ⟨8898658183736116583609173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11864877578314822111478897 8898658183736116583609173)
            ·
              refine ⟨52140575295328808107085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8898658183736116583609173 52140575295328808107085)
              ·
                rfl

theorem cell20_1028127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 9].length) (baseStart_1028127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028127 prefixEnd_1028127 := by exact prefixLift 1028127
  have htrace : WordTrace (prefixWord ++ tailWord_1028127) baseStart_1028127 baseEnd_1028127 := by
    simpa [prefixWord, tailWord_1028127, baseEnd_1028127] using wordTrace_append hprefix tailTrace_1028127
  have hstable : (prefixWord ++ tailWord_1028127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028127).length < 2 ^ (prefixWord ++ tailWord_1028127).sum := by decide
  have hdescent : baseEnd_1028127 < baseStart_1028127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028151 : List Nat := [1, 1, 3, 1, 2, 2, 2, 5, 3]
def baseStart_1028151 : Nat := 118140960795 + 1028151 * 2 ^ 59
def prefixEnd_1028151 : Nat := 4983230072969 + 3 ^ 40 * 1028151 * 2
def baseEnd_1028151 : Nat := 469276131911921856163667

theorem tailTrace_1028151 : CollatzResearch.WordTrace tailWord_1028151 prefixEnd_1028151 469276131911921856163667 := by
  unfold tailWord_1028151
  simp only [CollatzResearch.WordTrace]
  refine ⟨37499747698191996056140307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24999831798794664037426871 37499747698191996056140307)
  ·
    refine ⟨56249621547287994084210461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37499747698191996056140307 56249621547287994084210461)
    ·
      refine ⟨21093608080232997781578923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56249621547287994084210461 21093608080232997781578923)
      ·
        refine ⟨31640412120349496672368385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21093608080232997781578923 31640412120349496672368385)
        ·
          refine ⟨23730309090262122504276289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31640412120349496672368385 23730309090262122504276289)
          ·
            refine ⟨17797731817696591878207217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23730309090262122504276289 17797731817696591878207217)
            ·
              refine ⟨13348298863272443908655413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17797731817696591878207217 13348298863272443908655413)
              ·
                refine ⟨1251403018431791616436445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13348298863272443908655413 1251403018431791616436445)
                ·
                  refine ⟨469276131911921856163667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251403018431791616436445 469276131911921856163667)
                  ·
                    rfl

theorem cell20_1028151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 3].length) (baseStart_1028151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028151 prefixEnd_1028151 := by exact prefixLift 1028151
  have htrace : WordTrace (prefixWord ++ tailWord_1028151) baseStart_1028151 baseEnd_1028151 := by
    simpa [prefixWord, tailWord_1028151, baseEnd_1028151] using wordTrace_append hprefix tailTrace_1028151
  have hstable : (prefixWord ++ tailWord_1028151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028151).length < 2 ^ (prefixWord ++ tailWord_1028151).sum := by decide
  have hdescent : baseEnd_1028151 < baseStart_1028151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028161 : List Nat := [1, 2, 5, 1, 2, 1, 4, 4]
def baseStart_1028161 : Nat := 118140960795 + 1028161 * 2 ^ 59
def prefixEnd_1028161 : Nat := 4983230072969 + 3 ^ 40 * 1028161 * 2
def baseEnd_1028161 : Nat := 156426898728135421943431

theorem tailTrace_1028161 : CollatzResearch.WordTrace tailWord_1028161 prefixEnd_1028161 156426898728135421943431 := by
  unfold tailWord_1028161
  simp only [CollatzResearch.WordTrace]
  refine ⟨37500112428155767764004337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25000074952103845176002891 37500112428155767764004337)
  ·
    refine ⟨28125084321116825823003253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37500112428155767764004337 28125084321116825823003253)
    ·
      refine ⟨2636726655104702420906555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28125084321116825823003253 2636726655104702420906555)
      ·
        refine ⟨3955089982657053631359833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2636726655104702420906555 3955089982657053631359833)
        ·
          refine ⟨2966317486992790223519875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3955089982657053631359833 2966317486992790223519875)
          ·
            refine ⟨4449476230489185335279813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2966317486992790223519875 4449476230489185335279813)
            ·
              refine ⟨834276793216722250364965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4449476230489185335279813 834276793216722250364965)
              ·
                refine ⟨156426898728135421943431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 834276793216722250364965 156426898728135421943431)
                ·
                  rfl

theorem cell20_1028161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 4].length) (baseStart_1028161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028161 prefixEnd_1028161 := by exact prefixLift 1028161
  have htrace : WordTrace (prefixWord ++ tailWord_1028161) baseStart_1028161 baseEnd_1028161 := by
    simpa [prefixWord, tailWord_1028161, baseEnd_1028161] using wordTrace_append hprefix tailTrace_1028161
  have hstable : (prefixWord ++ tailWord_1028161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028161).length < 2 ^ (prefixWord ++ tailWord_1028161).sum := by decide
  have hdescent : baseEnd_1028161 < baseStart_1028161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028202 : List Nat := [3, 1, 3, 2, 3, 2, 2, 1, 3]
def baseStart_1028202 : Nat := 118140960795 + 1028202 * 2 ^ 59
def prefixEnd_1028202 : Nat := 4983230072969 + 3 ^ 40 * 1028202 * 2
def baseEnd_1028202 : Nat := 469299409701592345463459

theorem tailTrace_1028202 : CollatzResearch.WordTrace tailWord_1028202 prefixEnd_1028202 469299409701592345463459 := by
  unfold tailWord_1028202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9375401955251807941561715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25001071880671487844164573 9375401955251807941561715)
  ·
    refine ⟨14063102932877711912342573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9375401955251807941561715 14063102932877711912342573)
    ·
      refine ⟨5273663599829141967128465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14063102932877711912342573 5273663599829141967128465)
      ·
        refine ⟨3955247699871856475346349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5273663599829141967128465 3955247699871856475346349)
        ·
          refine ⟨1483217887451946178254881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3955247699871856475346349 1483217887451946178254881)
          ·
            refine ⟨1112413415588959633691161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1483217887451946178254881 1112413415588959633691161)
            ·
              refine ⟨834310061691719725268371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112413415588959633691161 834310061691719725268371)
              ·
                refine ⟨1251465092537579587902557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834310061691719725268371 1251465092537579587902557)
                ·
                  refine ⟨469299409701592345463459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251465092537579587902557 469299409701592345463459)
                  ·
                    rfl

theorem cell20_1028202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_1028202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028202 prefixEnd_1028202 := by exact prefixLift 1028202
  have htrace : WordTrace (prefixWord ++ tailWord_1028202) baseStart_1028202 baseEnd_1028202 := by
    simpa [prefixWord, tailWord_1028202, baseEnd_1028202] using wordTrace_append hprefix tailTrace_1028202
  have hstable : (prefixWord ++ tailWord_1028202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028202).length < 2 ^ (prefixWord ++ tailWord_1028202).sum := by decide
  have hdescent : baseEnd_1028202 < baseStart_1028202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028206 : List Nat := [4, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_1028206 : Nat := 118140960795 + 1028206 * 2 ^ 59
def prefixEnd_1028206 : Nat := 4983230072969 + 3 ^ 40 * 1028206 * 2
def baseEnd_1028206 : Nat := 469301235410586109330109

theorem tailTrace_1028206 : CollatzResearch.WordTrace tailWord_1028206 prefixEnd_1028206 469301235410586109330109 := by
  unfold tailWord_1028206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4687719214124092556174059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25001169141995160299594981 4687719214124092556174059)
  ·
    refine ⟨7031578821186138834261089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4687719214124092556174059 7031578821186138834261089)
    ·
      refine ⟨5273684115889604125695817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7031578821186138834261089 5273684115889604125695817)
      ·
        refine ⟨3955263086917203094271863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5273684115889604125695817 3955263086917203094271863)
        ·
          refine ⟨5932894630375804641407795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3955263086917203094271863 5932894630375804641407795)
          ·
            refine ⟨8899341945563706962111693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5932894630375804641407795 8899341945563706962111693)
            ·
              refine ⟨3337253229586390110791885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8899341945563706962111693 3337253229586390110791885)
              ·
                refine ⟨1251469961094896291546957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3337253229586390110791885 1251469961094896291546957)
                ·
                  refine ⟨469301235410586109330109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251469961094896291546957 469301235410586109330109)
                  ·
                    rfl

theorem cell20_1028206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_1028206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028206 prefixEnd_1028206 := by exact prefixLift 1028206
  have htrace : WordTrace (prefixWord ++ tailWord_1028206) baseStart_1028206 baseEnd_1028206 := by
    simpa [prefixWord, tailWord_1028206, baseEnd_1028206] using wordTrace_append hprefix tailTrace_1028206
  have hstable : (prefixWord ++ tailWord_1028206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028206).length < 2 ^ (prefixWord ++ tailWord_1028206).sum := by decide
  have hdescent : baseEnd_1028206 < baseStart_1028206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028254 : List Nat := [4, 3, 1, 1, 3, 2, 1, 5]
def baseStart_1028254 : Nat := 118140960795 + 1028254 * 2 ^ 59
def prefixEnd_1028254 : Nat := 4983230072969 + 3 ^ 40 * 1028254 * 2
def baseEnd_1028254 : Nat := 156441047972837091909971

theorem tailTrace_1028254 : CollatzResearch.WordTrace tailWord_1028254 prefixEnd_1028254 156441047972837091909971 := by
  unfold tailWord_1028254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4687938052102355580892477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25002336277879229764759877 4687938052102355580892477)
  ·
    refine ⟨1757976769538383342834679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4687938052102355580892477 1757976769538383342834679)
    ·
      refine ⟨2636965154307575014252019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1757976769538383342834679 2636965154307575014252019)
      ·
        refine ⟨3955447731461362521378029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2636965154307575014252019 3955447731461362521378029)
        ·
          refine ⟨1483292899298010945516761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3955447731461362521378029 1483292899298010945516761)
          ·
            refine ⟨1112469674473508209137571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1483292899298010945516761 1112469674473508209137571)
            ·
              refine ⟨1668704511710262313706357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112469674473508209137571 1668704511710262313706357)
              ·
                refine ⟨156441047972837091909971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1668704511710262313706357 156441047972837091909971)
                ·
                  rfl

theorem cell20_1028254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_1028254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028254 prefixEnd_1028254 := by exact prefixLift 1028254
  have htrace : WordTrace (prefixWord ++ tailWord_1028254) baseStart_1028254 baseEnd_1028254 := by
    simpa [prefixWord, tailWord_1028254, baseEnd_1028254] using wordTrace_append hprefix tailTrace_1028254
  have hstable : (prefixWord ++ tailWord_1028254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028254).length < 2 ^ (prefixWord ++ tailWord_1028254).sum := by decide
  have hdescent : baseEnd_1028254 < baseStart_1028254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028306 : List Nat := [3, 2, 2, 2, 1, 2, 2, 4, 2]
def baseStart_1028306 : Nat := 118140960795 + 1028306 * 2 ^ 59
def prefixEnd_1028306 : Nat := 4983230072969 + 3 ^ 40 * 1028306 * 2
def baseEnd_1028306 : Nat := 469346878135430205996367

theorem tailTrace_1028306 : CollatzResearch.WordTrace tailWord_1028306 prefixEnd_1028306 469346878135430205996367 := by
  unfold tailWord_1028306
  simp only [CollatzResearch.WordTrace]
  refine ⟨9376350253157614382008193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25003600675086971685355181 9376350253157614382008193)
  ·
    refine ⟨7032262689868210786506145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9376350253157614382008193 7032262689868210786506145)
    ·
      refine ⟨5274197017401158089879609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7032262689868210786506145 5274197017401158089879609)
      ·
        refine ⟨3955647763050868567409707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5274197017401158089879609 3955647763050868567409707)
        ·
          refine ⟨5933471644576302851114561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3955647763050868567409707 5933471644576302851114561)
          ·
            refine ⟨4450103733432227138335921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5933471644576302851114561 4450103733432227138335921)
            ·
              refine ⟨3337577800074170353751941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4450103733432227138335921 3337577800074170353751941)
              ·
                refine ⟨625795837513906941328489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3337577800074170353751941 625795837513906941328489)
                ·
                  refine ⟨469346878135430205996367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625795837513906941328489 469346878135430205996367)
                  ·
                    rfl

theorem cell20_1028306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_1028306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028306 prefixEnd_1028306 := by exact prefixLift 1028306
  have htrace : WordTrace (prefixWord ++ tailWord_1028306) baseStart_1028306 baseEnd_1028306 := by
    simpa [prefixWord, tailWord_1028306, baseEnd_1028306] using wordTrace_append hprefix tailTrace_1028306
  have hstable : (prefixWord ++ tailWord_1028306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028306).length < 2 ^ (prefixWord ++ tailWord_1028306).sum := by decide
  have hdescent : baseEnd_1028306 < baseStart_1028306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028320 : List Nat := [2, 1, 1, 3, 1, 3, 5, 1, 3]
def baseStart_1028320 : Nat := 118140960795 + 1028320 * 2 ^ 59
def prefixEnd_1028320 : Nat := 4983230072969 + 3 ^ 40 * 1028320 * 2
def baseEnd_1028320 : Nat := 469353268116908379529643

theorem tailTrace_1028320 : CollatzResearch.WordTrace tailWord_1028320 prefixEnd_1028320 469353268116908379529643 := by
  unfold tailWord_1028320
  simp only [CollatzResearch.WordTrace]
  refine ⟨18752955817289868959521207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25003941089719825279361609 18752955817289868959521207)
  ·
    refine ⟨28129433725934803439281811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18752955817289868959521207 28129433725934803439281811)
    ·
      refine ⟨42194150588902205158922717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28129433725934803439281811 42194150588902205158922717)
      ·
        refine ⟨15822806470838326934596019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42194150588902205158922717 15822806470838326934596019)
        ·
          refine ⟨23734209706257490401894029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15822806470838326934596019 23734209706257490401894029)
          ·
            refine ⟨8900328639846558900710261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23734209706257490401894029 8900328639846558900710261)
            ·
              refine ⟨834405809985614896941587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8900328639846558900710261 834405809985614896941587)
              ·
                refine ⟨1251608714978422345412381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834405809985614896941587 1251608714978422345412381)
                ·
                  refine ⟨469353268116908379529643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251608714978422345412381 469353268116908379529643)
                  ·
                    rfl

theorem cell20_1028320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_1028320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028320 prefixEnd_1028320 := by exact prefixLift 1028320
  have htrace : WordTrace (prefixWord ++ tailWord_1028320) baseStart_1028320 baseEnd_1028320 := by
    simpa [prefixWord, tailWord_1028320, baseEnd_1028320] using wordTrace_append hprefix tailTrace_1028320
  have hstable : (prefixWord ++ tailWord_1028320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028320).length < 2 ^ (prefixWord ++ tailWord_1028320).sum := by decide
  have hdescent : baseEnd_1028320 < baseStart_1028320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028327 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 4]
def baseStart_1028327 : Nat := 118140960795 + 1028327 * 2 ^ 59
def prefixEnd_1028327 : Nat := 4983230072969 + 3 ^ 40 * 1028327 * 2
def baseEnd_1028327 : Nat := 469356463107647466296281

theorem tailTrace_1028327 : CollatzResearch.WordTrace tailWord_1028327 prefixEnd_1028327 469356463107647466296281 := by
  unfold tailWord_1028327
  simp only [CollatzResearch.WordTrace]
  refine ⟨37506166945554378114547235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25004111297036252076364823 37506166945554378114547235)
  ·
    refine ⟨56259250418331567171820853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37506166945554378114547235 56259250418331567171820853)
    ·
      refine ⟨5274304726718584422358205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56259250418331567171820853 5274304726718584422358205)
      ·
        refine ⟨1977864272519469158384327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5274304726718584422358205 1977864272519469158384327)
        ·
          refine ⟨2966796408779203737576491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1977864272519469158384327 2966796408779203737576491)
          ·
            refine ⟨4450194613168805606364737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2966796408779203737576491 4450194613168805606364737)
            ·
              refine ⟨3337645959876604204773553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4450194613168805606364737 3337645959876604204773553)
              ·
                refine ⟨2503234469907453153580165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3337645959876604204773553 2503234469907453153580165)
                ·
                  refine ⟨469356463107647466296281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2503234469907453153580165 469356463107647466296281)
                  ·
                    rfl

theorem cell20_1028327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_1028327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028327 prefixEnd_1028327 := by exact prefixLift 1028327
  have htrace : WordTrace (prefixWord ++ tailWord_1028327) baseStart_1028327 baseEnd_1028327 := by
    simpa [prefixWord, tailWord_1028327, baseEnd_1028327] using wordTrace_append hprefix tailTrace_1028327
  have hstable : (prefixWord ++ tailWord_1028327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028327).length < 2 ^ (prefixWord ++ tailWord_1028327).sum := by decide
  have hdescent : baseEnd_1028327 < baseStart_1028327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028375 : List Nat := [1, 1, 3, 4, 1, 4, 2, 1, 3]
def baseStart_1028375 : Nat := 118140960795 + 1028375 * 2 ^ 59
def prefixEnd_1028375 : Nat := 4983230072969 + 3 ^ 40 * 1028375 * 2
def baseEnd_1028375 : Nat := 469378371615572632696085

theorem tailTrace_1028375 : CollatzResearch.WordTrace tailWord_1028375 prefixEnd_1028375 469378371615572632696085 := by
  unfold tailWord_1028375
  simp only [CollatzResearch.WordTrace]
  refine ⟨37507917649380482312294579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25005278432920321541529719 37507917649380482312294579)
  ·
    refine ⟨56261876474070723468441869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37507917649380482312294579 56261876474070723468441869)
    ·
      refine ⟨21098203677776521300665701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56261876474070723468441869 21098203677776521300665701)
      ·
        refine ⟨3955913189583097743874819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21098203677776521300665701 3955913189583097743874819)
        ·
          refine ⟨5933869784374646615812229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3955913189583097743874819 5933869784374646615812229)
          ·
            refine ⟨1112600584570246240464793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5933869784374646615812229 1112600584570246240464793)
            ·
              refine ⟨834450438427684680348595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112600584570246240464793 834450438427684680348595)
              ·
                refine ⟨1251675657641527020522893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834450438427684680348595 1251675657641527020522893)
                ·
                  refine ⟨469378371615572632696085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251675657641527020522893 469378371615572632696085)
                  ·
                    rfl

theorem cell20_1028375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 3].length) (baseStart_1028375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028375 prefixEnd_1028375 := by exact prefixLift 1028375
  have htrace : WordTrace (prefixWord ++ tailWord_1028375) baseStart_1028375 baseEnd_1028375 := by
    simpa [prefixWord, tailWord_1028375, baseEnd_1028375] using wordTrace_append hprefix tailTrace_1028375
  have hstable : (prefixWord ++ tailWord_1028375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028375).length < 2 ^ (prefixWord ++ tailWord_1028375).sum := by decide
  have hdescent : baseEnd_1028375 < baseStart_1028375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028400 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 5]
def baseStart_1028400 : Nat := 118140960795 + 1028400 * 2 ^ 59
def prefixEnd_1028400 : Nat := 4983230072969 + 3 ^ 40 * 1028400 * 2
def baseEnd_1028400 : Nat := 469389782296783656862649

theorem tailTrace_1028400 : CollatzResearch.WordTrace tailWord_1028400 prefixEnd_1028400 469389782296783656862649 := by
  unfold tailWord_1028400
  simp only [CollatzResearch.WordTrace]
  refine ⟨18754414737144955790977327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25005886316193274387969769 18754414737144955790977327)
  ·
    refine ⟨28131622105717433686465991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18754414737144955790977327 28131622105717433686465991)
    ·
      refine ⟨42197433158576150529698987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28131622105717433686465991 42197433158576150529698987)
      ·
        refine ⟨63296149737864225794548481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42197433158576150529698987 63296149737864225794548481)
        ·
          refine ⟨47472112303398169345911361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63296149737864225794548481 47472112303398169345911361)
          ·
            refine ⟨35604084227548627009433521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47472112303398169345911361 35604084227548627009433521)
            ·
              refine ⟨26703063170661470257075141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35604084227548627009433521 26703063170661470257075141)
              ·
                refine ⟨5006824344499025673201589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26703063170661470257075141 5006824344499025673201589)
                ·
                  refine ⟨469389782296783656862649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5006824344499025673201589 469389782296783656862649)
                  ·
                    rfl

theorem cell20_1028400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_1028400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028400 prefixEnd_1028400 := by exact prefixLift 1028400
  have htrace : WordTrace (prefixWord ++ tailWord_1028400) baseStart_1028400 baseEnd_1028400 := by
    simpa [prefixWord, tailWord_1028400, baseEnd_1028400] using wordTrace_append hprefix tailTrace_1028400
  have hstable : (prefixWord ++ tailWord_1028400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028400).length < 2 ^ (prefixWord ++ tailWord_1028400).sum := by decide
  have hdescent : baseEnd_1028400 < baseStart_1028400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028403 : List Nat := [1, 1, 1, 2, 5, 1, 2, 5, 2]
def baseStart_1028403 : Nat := 118140960795 + 1028403 * 2 ^ 59
def prefixEnd_1028403 : Nat := 4983230072969 + 3 ^ 40 * 1028403 * 2
def baseEnd_1028403 : Nat := 469391151578528979762637

theorem tailTrace_1028403 : CollatzResearch.WordTrace tailWord_1028403 prefixEnd_1028403 469391151578528979762637 := by
  unfold tailWord_1028403
  simp only [CollatzResearch.WordTrace]
  refine ⟨37508938893279043094313863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25005959262186028729542575 37508938893279043094313863)
  ·
    refine ⟨56263408339918564641470795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37508938893279043094313863 56263408339918564641470795)
    ·
      refine ⟨84395112509877846962206193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56263408339918564641470795 84395112509877846962206193)
      ·
        refine ⟨63296334382408385221654645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84395112509877846962206193 63296334382408385221654645)
        ·
          refine ⟨5934031348350786114530123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63296334382408385221654645 5934031348350786114530123)
          ·
            refine ⟨8901047022526179171795185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5934031348350786114530123 8901047022526179171795185)
            ·
              refine ⟨6675785266894634378846389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8901047022526179171795185 6675785266894634378846389)
              ·
                refine ⟨625854868771371973016849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6675785266894634378846389 625854868771371973016849)
                ·
                  refine ⟨469391151578528979762637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625854868771371973016849 469391151578528979762637)
                  ·
                    rfl

theorem cell20_1028403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 2].length) (baseStart_1028403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028403 prefixEnd_1028403 := by exact prefixLift 1028403
  have htrace : WordTrace (prefixWord ++ tailWord_1028403) baseStart_1028403 baseEnd_1028403 := by
    simpa [prefixWord, tailWord_1028403, baseEnd_1028403] using wordTrace_append hprefix tailTrace_1028403
  have hstable : (prefixWord ++ tailWord_1028403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028403).length < 2 ^ (prefixWord ++ tailWord_1028403).sum := by decide
  have hdescent : baseEnd_1028403 < baseStart_1028403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028444 : List Nat := [2, 2, 4, 3, 1, 1, 3, 4]
def baseStart_1028444 : Nat := 118140960795 + 1028444 * 2 ^ 59
def prefixEnd_1028444 : Nat := 4983230072969 + 3 ^ 40 * 1028444 * 2
def baseEnd_1028444 : Nat := 156469955031905019798601

theorem tailTrace_1028444 : CollatzResearch.WordTrace tailWord_1028444 prefixEnd_1028444 156469955031905019798601 := by
  unfold tailWord_1028444
  simp only [CollatzResearch.WordTrace]
  refine ⟨18755217143065253548278193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25006956190753671397704257 18755217143065253548278193)
  ·
    refine ⟨14066412857298940161208645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18755217143065253548278193 14066412857298940161208645)
    ·
      refine ⟨2637452410743551280226621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14066412857298940161208645 2637452410743551280226621)
      ·
        refine ⟨989044654028831730084983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2637452410743551280226621 989044654028831730084983)
        ·
          refine ⟨1483566981043247595127475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989044654028831730084983 1483566981043247595127475)
          ·
            refine ⟨2225350471564871392691213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483566981043247595127475 2225350471564871392691213)
            ·
              refine ⟨834506426836826772259205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2225350471564871392691213 834506426836826772259205)
              ·
                refine ⟨156469955031905019798601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 834506426836826772259205 156469955031905019798601)
                ·
                  rfl

theorem cell20_1028444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_1028444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028444 prefixEnd_1028444 := by exact prefixLift 1028444
  have htrace : WordTrace (prefixWord ++ tailWord_1028444) baseStart_1028444 baseEnd_1028444 := by
    simpa [prefixWord, tailWord_1028444, baseEnd_1028444] using wordTrace_append hprefix tailTrace_1028444
  have hstable : (prefixWord ++ tailWord_1028444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028444).length < 2 ^ (prefixWord ++ tailWord_1028444).sum := by decide
  have hdescent : baseEnd_1028444 < baseStart_1028444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028458 : List Nat := [3, 1, 3, 3, 1, 1, 1, 5, 2]
def baseStart_1028458 : Nat := 118140960795 + 1028458 * 2 ^ 59
def prefixEnd_1028458 : Nat := 4983230072969 + 3 ^ 40 * 1028458 * 2
def baseEnd_1028458 : Nat := 469416255077193232929079

theorem tailTrace_1028458 : CollatzResearch.WordTrace tailWord_1028458 prefixEnd_1028458 469416255077193232929079 := by
  unfold tailWord_1028458
  simp only [CollatzResearch.WordTrace]
  refine ⟨9377736227019946871891507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25007296605386524991710685 9377736227019946871891507)
  ·
    refine ⟨14066604340529920307837261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9377736227019946871891507 14066604340529920307837261)
    ·
      refine ⟨5274976627698720115438973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14066604340529920307837261 5274976627698720115438973)
      ·
        refine ⟨1978116235387020043289615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5274976627698720115438973 1978116235387020043289615)
        ·
          refine ⟨2967174353080530064934423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1978116235387020043289615 2967174353080530064934423)
          ·
            refine ⟨4450761529620795097401635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967174353080530064934423 4450761529620795097401635)
            ·
              refine ⟨6676142294431192646102453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4450761529620795097401635 6676142294431192646102453)
              ·
                refine ⟨625888340102924310572105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6676142294431192646102453 625888340102924310572105)
                ·
                  refine ⟨469416255077193232929079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625888340102924310572105 469416255077193232929079)
                  ·
                    rfl

theorem cell20_1028458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_1028458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028458 prefixEnd_1028458 := by exact prefixLift 1028458
  have htrace : WordTrace (prefixWord ++ tailWord_1028458) baseStart_1028458 baseEnd_1028458 := by
    simpa [prefixWord, tailWord_1028458, baseEnd_1028458] using wordTrace_append hprefix tailTrace_1028458
  have hstable : (prefixWord ++ tailWord_1028458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028458).length < 2 ^ (prefixWord ++ tailWord_1028458).sum := by decide
  have hdescent : baseEnd_1028458 < baseStart_1028458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028510 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1028510 : Nat := 118140960795 + 1028510 * 2 ^ 59
def prefixEnd_1028510 : Nat := 4983230072969 + 3 ^ 40 * 1028510 * 2
def baseEnd_1028510 : Nat := 469439989294112163195533

theorem tailTrace_1028510 : CollatzResearch.WordTrace tailWord_1028510 prefixEnd_1028510 469439989294112163195533 := by
  unfold tailWord_1028510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4689105187986425046057373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25008561002594266912305989 4689105187986425046057373)
  ·
    refine ⟨1758414445494909392271515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4689105187986425046057373 1758414445494909392271515)
    ·
      refine ⟨2637621668242364088407273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1758414445494909392271515 2637621668242364088407273)
      ·
        refine ⟨1978216251181773066305455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2637621668242364088407273 1978216251181773066305455)
        ·
          refine ⟨2967324376772659599458183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1978216251181773066305455 2967324376772659599458183)
          ·
            refine ⟨4450986565158989399187275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967324376772659599458183 4450986565158989399187275)
            ·
              refine ⟨6676479847738484098780913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4450986565158989399187275 6676479847738484098780913)
              ·
                refine ⟨5007359885803863074085685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6676479847738484098780913 5007359885803863074085685)
                ·
                  refine ⟨469439989294112163195533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5007359885803863074085685 469439989294112163195533)
                  ·
                    rfl

theorem cell20_1028510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1028510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028510 prefixEnd_1028510 := by exact prefixLift 1028510
  have htrace : WordTrace (prefixWord ++ tailWord_1028510) baseStart_1028510 baseEnd_1028510 := by
    simpa [prefixWord, tailWord_1028510, baseEnd_1028510] using wordTrace_append hprefix tailTrace_1028510
  have hstable : (prefixWord ++ tailWord_1028510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028510).length < 2 ^ (prefixWord ++ tailWord_1028510).sum := by decide
  have hdescent : baseEnd_1028510 < baseStart_1028510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028521 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 6]
def baseStart_1028521 : Nat := 118140960795 + 1028521 * 2 ^ 59
def prefixEnd_1028521 : Nat := 4983230072969 + 3 ^ 40 * 1028521 * 2
def baseEnd_1028521 : Nat := 469445009993845013828821

theorem tailTrace_1028521 : CollatzResearch.WordTrace tailWord_1028521 prefixEnd_1028521 469445009993845013828821 := by
  unfold tailWord_1028521
  simp only [CollatzResearch.WordTrace]
  refine ⟨37513242706851549247109417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25008828471234366164739611 37513242706851549247109417)
  ·
    refine ⟨28134932030138661935332063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37513242706851549247109417 28134932030138661935332063)
    ·
      refine ⟨42202398045207992902998095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28134932030138661935332063 42202398045207992902998095)
      ·
        refine ⟨63303597067811989354497143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42202398045207992902998095 63303597067811989354497143)
        ·
          refine ⟨94955395601717984031745715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63303597067811989354497143 94955395601717984031745715)
          ·
            refine ⟨142433093402576976047618573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94955395601717984031745715 142433093402576976047618573)
            ·
              refine ⟨53412410025966366017856965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142433093402576976047618573 53412410025966366017856965)
              ·
                refine ⟨10014826879868693628348181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53412410025966366017856965 10014826879868693628348181)
                ·
                  refine ⟨469445009993845013828821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10014826879868693628348181 469445009993845013828821)
                  ·
                    rfl

theorem cell20_1028521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_1028521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028521 prefixEnd_1028521 := by exact prefixLift 1028521
  have htrace : WordTrace (prefixWord ++ tailWord_1028521) baseStart_1028521 baseEnd_1028521 := by
    simpa [prefixWord, tailWord_1028521, baseEnd_1028521] using wordTrace_append hprefix tailTrace_1028521
  have hstable : (prefixWord ++ tailWord_1028521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028521).length < 2 ^ (prefixWord ++ tailWord_1028521).sum := by decide
  have hdescent : baseEnd_1028521 < baseStart_1028521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028559 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 6]
def baseStart_1028559 : Nat := 118140960795 + 1028559 * 2 ^ 59
def prefixEnd_1028559 : Nat := 4983230072969 + 3 ^ 40 * 1028559 * 2
def baseEnd_1028559 : Nat := 469462354229285770561999

theorem tailTrace_1028559 : CollatzResearch.WordTrace tailWord_1028559 prefixEnd_1028559 469462354229285770561999 := by
  unfold tailWord_1028559
  simp only [CollatzResearch.WordTrace]
  refine ⟨37514628680713881736992731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25009752453809254491328487 37514628680713881736992731)
  ·
    refine ⟨56271943021070822605489097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37514628680713881736992731 56271943021070822605489097)
    ·
      refine ⟨42203957265803116954116823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56271943021070822605489097 42203957265803116954116823)
      ·
        refine ⟨63305935898704675431175235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42203957265803116954116823 63305935898704675431175235)
        ·
          refine ⟨94958903848057013146762853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63305935898704675431175235 94958903848057013146762853)
          ·
            refine ⟨17804794471510689965018035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94958903848057013146762853 17804794471510689965018035)
            ·
              refine ⟨26707191707266034947527053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17804794471510689965018035 26707191707266034947527053)
              ·
                refine ⟨10015196890224763105322645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26707191707266034947527053 10015196890224763105322645)
                ·
                  refine ⟨469462354229285770561999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10015196890224763105322645 469462354229285770561999)
                  ·
                    rfl

theorem cell20_1028559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_1028559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028559 prefixEnd_1028559 := by exact prefixLift 1028559
  have htrace : WordTrace (prefixWord ++ tailWord_1028559) baseStart_1028559 baseEnd_1028559 := by
    simpa [prefixWord, tailWord_1028559, baseEnd_1028559] using wordTrace_append hprefix tailTrace_1028559
  have hstable : (prefixWord ++ tailWord_1028559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028559).length < 2 ^ (prefixWord ++ tailWord_1028559).sum := by decide
  have hdescent : baseEnd_1028559 < baseStart_1028559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028586 : List Nat := [3, 1, 3, 1, 3, 2, 2, 2, 3]
def baseStart_1028586 : Nat := 118140960795 + 1028586 * 2 ^ 59
def prefixEnd_1028586 : Nat := 4983230072969 + 3 ^ 40 * 1028586 * 2
def baseEnd_1028586 : Nat := 469474677764993676661889

theorem tailTrace_1028586 : CollatzResearch.WordTrace tailWord_1028586 prefixEnd_1028586 469474677764993676661889 := by
  unfold tailWord_1028586
  simp only [CollatzResearch.WordTrace]
  refine ⟨9378903362904016337056403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25010408967744043565483741 9378903362904016337056403)
  ·
    refine ⟨14068355044356024505584605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9378903362904016337056403 14068355044356024505584605)
    ·
      refine ⟨5275633141633509189594227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14068355044356024505584605 5275633141633509189594227)
      ·
        refine ⟨7913449712450263784391341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5275633141633509189594227 7913449712450263784391341)
        ·
          refine ⟨2967543642168848919146753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7913449712450263784391341 2967543642168848919146753)
          ·
            refine ⟨2225657731626636689360065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2967543642168848919146753 2225657731626636689360065)
            ·
              refine ⟨1669243298719977517020049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2225657731626636689360065 1669243298719977517020049)
              ·
                refine ⟨1251932474039983137765037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1669243298719977517020049 1251932474039983137765037)
                ·
                  refine ⟨469474677764993676661889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251932474039983137765037 469474677764993676661889)
                  ·
                    rfl

theorem cell20_1028586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_1028586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028586 prefixEnd_1028586 := by exact prefixLift 1028586
  have htrace : WordTrace (prefixWord ++ tailWord_1028586) baseStart_1028586 baseEnd_1028586 := by
    simpa [prefixWord, tailWord_1028586, baseEnd_1028586] using wordTrace_append hprefix tailTrace_1028586
  have hstable : (prefixWord ++ tailWord_1028586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028586).length < 2 ^ (prefixWord ++ tailWord_1028586).sum := by decide
  have hdescent : baseEnd_1028586 < baseStart_1028586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028589 : List Nat := [1, 5, 1, 3, 1, 1, 4, 2, 2]
def baseStart_1028589 : Nat := 118140960795 + 1028589 * 2 ^ 59
def prefixEnd_1028589 : Nat := 4983230072969 + 3 ^ 40 * 1028589 * 2
def baseEnd_1028589 : Nat := 469476047046738999561877

theorem tailTrace_1028589 : CollatzResearch.WordTrace tailWord_1028589 prefixEnd_1028589 469476047046738999561877 := by
  unfold tailWord_1028589
  simp only [CollatzResearch.WordTrace]
  refine ⟨37515722870605196860584821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25010481913736797907056547 37515722870605196860584821)
  ·
    refine ⟨3517099019119237205679827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37515722870605196860584821 3517099019119237205679827)
    ·
      refine ⟨5275648528678855808519741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3517099019119237205679827 5275648528678855808519741)
      ·
        refine ⟨1978368198254570928194903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5275648528678855808519741 1978368198254570928194903)
        ·
          refine ⟨2967552297381856392292355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1978368198254570928194903 2967552297381856392292355)
          ·
            refine ⟨4451328446072784588438533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967552297381856392292355 4451328446072784588438533)
            ·
              refine ⟨834624083638647110332225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4451328446072784588438533 834624083638647110332225)
              ·
                refine ⟨625968062728985332749169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 834624083638647110332225 625968062728985332749169)
                ·
                  refine ⟨469476047046738999561877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625968062728985332749169 469476047046738999561877)
                  ·
                    rfl

theorem cell20_1028589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_1028589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028589 prefixEnd_1028589 := by exact prefixLift 1028589
  have htrace : WordTrace (prefixWord ++ tailWord_1028589) baseStart_1028589 baseEnd_1028589 := by
    simpa [prefixWord, tailWord_1028589, baseEnd_1028589] using wordTrace_append hprefix tailTrace_1028589
  have hstable : (prefixWord ++ tailWord_1028589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028589).length < 2 ^ (prefixWord ++ tailWord_1028589).sum := by decide
  have hdescent : baseEnd_1028589 < baseStart_1028589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028593 : List Nat := [1, 2, 2, 2, 3, 1, 3, 4, 2]
def baseStart_1028593 : Nat := 118140960795 + 1028593 * 2 ^ 59
def prefixEnd_1028593 : Nat := 4983230072969 + 3 ^ 40 * 1028593 * 2
def baseEnd_1028593 : Nat := 469477872755732763428527

theorem tailTrace_1028593 : CollatzResearch.WordTrace tailWord_1028593 prefixEnd_1028593 469477872755732763428527 := by
  unfold tailWord_1028593
  simp only [CollatzResearch.WordTrace]
  refine ⟨37515868762590705543730433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25010579175060470362486955 37515868762590705543730433)
  ·
    refine ⟨28136901571943029157797825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37515868762590705543730433 28136901571943029157797825)
    ·
      refine ⟨21102676178957271868348369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28136901571943029157797825 21102676178957271868348369)
      ·
        refine ⟨15827007134217953901261277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21102676178957271868348369 15827007134217953901261277)
        ·
          refine ⟨5935127675331732712972979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15827007134217953901261277 5935127675331732712972979)
          ·
            refine ⟨8902691512997599069459469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5935127675331732712972979 8902691512997599069459469)
            ·
              refine ⟨3338509317374099651047301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8902691512997599069459469 3338509317374099651047301)
              ·
                refine ⟨625970497007643684571369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3338509317374099651047301 625970497007643684571369)
                ·
                  refine ⟨469477872755732763428527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625970497007643684571369 469477872755732763428527)
                  ·
                    rfl

theorem cell20_1028593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 2].length) (baseStart_1028593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028593 prefixEnd_1028593 := by exact prefixLift 1028593
  have htrace : WordTrace (prefixWord ++ tailWord_1028593) baseStart_1028593 baseEnd_1028593 := by
    simpa [prefixWord, tailWord_1028593, baseEnd_1028593] using wordTrace_append hprefix tailTrace_1028593
  have hstable : (prefixWord ++ tailWord_1028593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028593).length < 2 ^ (prefixWord ++ tailWord_1028593).sum := by decide
  have hdescent : baseEnd_1028593 < baseStart_1028593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028610 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1028610 : Nat := 118140960795 + 1028610 * 2 ^ 59
def prefixEnd_1028610 : Nat := 4983230072969 + 3 ^ 40 * 1028610 * 2
def baseEnd_1028610 : Nat := 469485632018956259861791

theorem tailTrace_1028610 : CollatzResearch.WordTrace tailWord_1028610 prefixEnd_1028610 469485632018956259861791 := by
  unfold tailWord_1028610
  simp only [CollatzResearch.WordTrace]
  refine ⟨9379122200882279361774821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25010992535686078298066189 9379122200882279361774821)
  ·
    refine ⟨1758585412665427380332779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9379122200882279361774821 1758585412665427380332779)
    ·
      refine ⟨2637878118998141070499169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1758585412665427380332779 2637878118998141070499169)
      ·
        refine ⟨1978408589248605802874377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2637878118998141070499169 1978408589248605802874377)
        ·
          refine ⟨1483806441936454352155783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1978408589248605802874377 1483806441936454352155783)
          ·
            refine ⟨2225709662904681528233675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483806441936454352155783 2225709662904681528233675)
            ·
              refine ⟨3338564494357022292350513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2225709662904681528233675 3338564494357022292350513)
              ·
                refine ⟨2503923370767766719262885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3338564494357022292350513 2503923370767766719262885)
                ·
                  refine ⟨469485632018956259861791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2503923370767766719262885 469485632018956259861791)
                  ·
                    rfl

theorem cell20_1028610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1028610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028610 prefixEnd_1028610 := by exact prefixLift 1028610
  have htrace : WordTrace (prefixWord ++ tailWord_1028610) baseStart_1028610 baseEnd_1028610 := by
    simpa [prefixWord, tailWord_1028610, baseEnd_1028610] using wordTrace_append hprefix tailTrace_1028610
  have hstable : (prefixWord ++ tailWord_1028610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028610).length < 2 ^ (prefixWord ++ tailWord_1028610).sum := by decide
  have hdescent : baseEnd_1028610 < baseStart_1028610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028645 : List Nat := [1, 3, 1, 2, 2, 1, 5, 2, 3]
def baseStart_1028645 : Nat := 118140960795 + 1028645 * 2 ^ 59
def prefixEnd_1028645 : Nat := 4983230072969 + 3 ^ 40 * 1028645 * 2
def baseEnd_1028645 : Nat := 469501606972651693694981

theorem tailTrace_1028645 : CollatzResearch.WordTrace tailWord_1028645 prefixEnd_1028645 469501606972651693694981 := by
  unfold tailWord_1028645
  simp only [CollatzResearch.WordTrace]
  refine ⟨37517765358402318424623389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25011843572268212283082259 37517765358402318424623389)
  ·
    refine ⟨14069162009400869409233771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37517765358402318424623389 14069162009400869409233771)
    ·
      refine ⟨21103743014101304113850657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14069162009400869409233771 21103743014101304113850657)
      ·
        refine ⟨15827807260575978085387993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21103743014101304113850657 15827807260575978085387993)
        ·
          refine ⟨11870855445431983564040995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15827807260575978085387993 11870855445431983564040995)
          ·
            refine ⟨17806283168147975346061493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11870855445431983564040995 17806283168147975346061493)
            ·
              refine ⟨1669339047013872688693265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17806283168147975346061493 1669339047013872688693265)
              ·
                refine ⟨1252004285260404516519949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1669339047013872688693265 1252004285260404516519949)
                ·
                  refine ⟨469501606972651693694981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1252004285260404516519949 469501606972651693694981)
                  ·
                    rfl

theorem cell20_1028645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_1028645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028645 prefixEnd_1028645 := by exact prefixLift 1028645
  have htrace : WordTrace (prefixWord ++ tailWord_1028645) baseStart_1028645 baseEnd_1028645 := by
    simpa [prefixWord, tailWord_1028645, baseEnd_1028645] using wordTrace_append hprefix tailTrace_1028645
  have hstable : (prefixWord ++ tailWord_1028645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028645).length < 2 ^ (prefixWord ++ tailWord_1028645).sum := by decide
  have hdescent : baseEnd_1028645 < baseStart_1028645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028648 : List Nat := [2, 1, 5, 2, 1, 1, 2, 4, 2]
def baseStart_1028648 : Nat := 118140960795 + 1028648 * 2 ^ 59
def prefixEnd_1028648 : Nat := 4983230072969 + 3 ^ 40 * 1028648 * 2
def baseEnd_1028648 : Nat := 469502976254397016594969

theorem tailTrace_1028648 : CollatzResearch.WordTrace tailWord_1028648 prefixEnd_1028648 469502976254397016594969 := by
  unfold tailWord_1028648
  simp only [CollatzResearch.WordTrace]
  refine ⟨18758937388695724968491299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25011916518260966624655065 18758937388695724968491299)
  ·
    refine ⟨28138406083043587452736949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18758937388695724968491299 28138406083043587452736949)
    ·
      refine ⟨2637975570285336323694089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28138406083043587452736949 2637975570285336323694089)
      ·
        refine ⟨1978481677714002242770567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2637975570285336323694089 1978481677714002242770567)
        ·
          refine ⟨2967722516571003364155851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1978481677714002242770567 2967722516571003364155851)
          ·
            refine ⟨4451583774856505046233777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967722516571003364155851 4451583774856505046233777)
            ·
              refine ⟨3338687831142378784675333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4451583774856505046233777 3338687831142378784675333)
              ·
                refine ⟨626003968339196022126625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3338687831142378784675333 626003968339196022126625)
                ·
                  refine ⟨469502976254397016594969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626003968339196022126625 469502976254397016594969)
                  ·
                    rfl

theorem cell20_1028648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 2].length) (baseStart_1028648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028648 prefixEnd_1028648 := by exact prefixLift 1028648
  have htrace : WordTrace (prefixWord ++ tailWord_1028648) baseStart_1028648 baseEnd_1028648 := by
    simpa [prefixWord, tailWord_1028648, baseEnd_1028648] using wordTrace_append hprefix tailTrace_1028648
  have hstable : (prefixWord ++ tailWord_1028648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028648).length < 2 ^ (prefixWord ++ tailWord_1028648).sum := by decide
  have hdescent : baseEnd_1028648 < baseStart_1028648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028704 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 5]
def baseStart_1028704 : Nat := 118140960795 + 1028704 * 2 ^ 59
def prefixEnd_1028704 : Nat := 4983230072969 + 3 ^ 40 * 1028704 * 2
def baseEnd_1028704 : Nat := 469528536180309710728073

theorem tailTrace_1028704 : CollatzResearch.WordTrace tailWord_1028704 prefixEnd_1028704 469528536180309710728073 := by
  unfold tailWord_1028704
  simp only [CollatzResearch.WordTrace]
  refine ⟨18759958632594285750510583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25013278176792381000680777 18759958632594285750510583)
  ·
    refine ⟨28139937948891428625765875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18759958632594285750510583 28139937948891428625765875)
    ·
      refine ⟨42209906923337142938648813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28139937948891428625765875 42209906923337142938648813)
      ·
        refine ⟨15828715096251428601993305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42209906923337142938648813 15828715096251428601993305)
        ·
          refine ⟨11871536322188571451494979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15828715096251428601993305 11871536322188571451494979)
          ·
            refine ⟨17807304483282857177242469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11871536322188571451494979 17807304483282857177242469)
            ·
              refine ⟨3338869590615535720732963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17807304483282857177242469 3338869590615535720732963)
              ·
                refine ⟨5008304385923303581099445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3338869590615535720732963 5008304385923303581099445)
                ·
                  refine ⟨469528536180309710728073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5008304385923303581099445 469528536180309710728073)
                  ·
                    rfl

theorem cell20_1028704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_1028704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028704 prefixEnd_1028704 := by exact prefixLift 1028704
  have htrace : WordTrace (prefixWord ++ tailWord_1028704) baseStart_1028704 baseEnd_1028704 := by
    simpa [prefixWord, tailWord_1028704, baseEnd_1028704] using wordTrace_append hprefix tailTrace_1028704
  have hstable : (prefixWord ++ tailWord_1028704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028704).length < 2 ^ (prefixWord ++ tailWord_1028704).sum := by decide
  have hdescent : baseEnd_1028704 < baseStart_1028704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028717 : List Nat := [1, 5, 1, 1, 3, 3, 2, 1, 3]
def baseStart_1028717 : Nat := 118140960795 + 1028717 * 2 ^ 59
def prefixEnd_1028717 : Nat := 4983230072969 + 3 ^ 40 * 1028717 * 2
def baseEnd_1028717 : Nat := 469534469734539443294687

theorem tailTrace_1028717 : CollatzResearch.WordTrace tailWord_1028717 prefixEnd_1028717 469534469734539443294687 := by
  unfold tailWord_1028717
  simp only [CollatzResearch.WordTrace]
  refine ⟨37520391414141474721244405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25013594276094316480829603 37520391414141474721244405)
  ·
    refine ⟨3517536695075763255116663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37520391414141474721244405 3517536695075763255116663)
    ·
      refine ⟨5276305042613644882674995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3517536695075763255116663 5276305042613644882674995)
      ·
        refine ⟨7914457563920467324012493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5276305042613644882674995 7914457563920467324012493)
        ·
          refine ⟨2967921586470175246504685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7914457563920467324012493 2967921586470175246504685)
          ·
            refine ⟨1112970594926315717439257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2967921586470175246504685 1112970594926315717439257)
            ·
              refine ⟨834727946194736788079443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112970594926315717439257 834727946194736788079443)
              ·
                refine ⟨1252091919292105182119165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834727946194736788079443 1252091919292105182119165)
                ·
                  refine ⟨469534469734539443294687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1252091919292105182119165 469534469734539443294687)
                  ·
                    rfl

theorem cell20_1028717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_1028717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028717 prefixEnd_1028717 := by exact prefixLift 1028717
  have htrace : WordTrace (prefixWord ++ tailWord_1028717) baseStart_1028717 baseEnd_1028717 := by
    simpa [prefixWord, tailWord_1028717, baseEnd_1028717] using wordTrace_append hprefix tailTrace_1028717
  have hstable : (prefixWord ++ tailWord_1028717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028717).length < 2 ^ (prefixWord ++ tailWord_1028717).sum := by decide
  have hdescent : baseEnd_1028717 < baseStart_1028717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028759 : List Nat := [1, 1, 3, 3, 2, 1, 4, 2, 3]
def baseStart_1028759 : Nat := 118140960795 + 1028759 * 2 ^ 59
def prefixEnd_1028759 : Nat := 4983230072969 + 3 ^ 40 * 1028759 * 2
def baseEnd_1028759 : Nat := 469553639678973963894515

theorem tailTrace_1028759 : CollatzResearch.WordTrace tailWord_1028759 prefixEnd_1028759 469553639678973963894515 := by
  unfold tailWord_1028759
  simp only [CollatzResearch.WordTrace]
  refine ⟨37521923279989315894273331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25014615519992877262848887 37521923279989315894273331)
  ·
    refine ⟨56282884919983973841409997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37521923279989315894273331 56282884919983973841409997)
    ·
      refine ⟨21106081844993990190528749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56282884919983973841409997 21106081844993990190528749)
      ·
        refine ⟨7914780691872746321448281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21106081844993990190528749 7914780691872746321448281)
        ·
          refine ⟨5936085518904559741086211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7914780691872746321448281 5936085518904559741086211)
          ·
            refine ⟨8904128278356839611629317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5936085518904559741086211 8904128278356839611629317)
            ·
              refine ⟨1669524052191907427180497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8904128278356839611629317 1669524052191907427180497)
              ·
                refine ⟨1252143039143930570385373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1669524052191907427180497 1252143039143930570385373)
                ·
                  refine ⟨469553639678973963894515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1252143039143930570385373 469553639678973963894515)
                  ·
                    rfl

theorem cell20_1028759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 3].length) (baseStart_1028759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028759 prefixEnd_1028759 := by exact prefixLift 1028759
  have htrace : WordTrace (prefixWord ++ tailWord_1028759) baseStart_1028759 baseEnd_1028759 := by
    simpa [prefixWord, tailWord_1028759, baseEnd_1028759] using wordTrace_append hprefix tailTrace_1028759
  have hstable : (prefixWord ++ tailWord_1028759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028759).length < 2 ^ (prefixWord ++ tailWord_1028759).sum := by decide
  have hdescent : baseEnd_1028759 < baseStart_1028759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028769 : List Nat := [1, 2, 3, 3, 4, 1, 1, 5]
def baseStart_1028769 : Nat := 118140960795 + 1028769 * 2 ^ 59
def prefixEnd_1028769 : Nat := 4983230072969 + 3 ^ 40 * 1028769 * 2
def baseEnd_1028769 : Nat := 156519401317152791187047

theorem tailTrace_1028769 : CollatzResearch.WordTrace tailWord_1028769 prefixEnd_1028769 156519401317152791187047 := by
  unfold tailWord_1028769
  simp only [CollatzResearch.WordTrace]
  refine ⟨37522288009953087602137361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25014858673302058401424907 37522288009953087602137361)
  ·
    refine ⟨28141716007464815701603021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37522288009953087602137361 28141716007464815701603021)
    ·
      refine ⟨10553143502799305888101133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28141716007464815701603021 10553143502799305888101133)
      ·
        refine ⟨3957428813549739708037925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10553143502799305888101133 3957428813549739708037925)
        ·
          refine ⟨742017902540576195257111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3957428813549739708037925 742017902540576195257111)
          ·
            refine ⟨1113026853810864292885667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742017902540576195257111 1113026853810864292885667)
            ·
              refine ⟨1669540280716296439328501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1113026853810864292885667 1669540280716296439328501)
              ·
                refine ⟨156519401317152791187047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1669540280716296439328501 156519401317152791187047)
                ·
                  rfl

theorem cell20_1028769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 5].length) (baseStart_1028769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028769 prefixEnd_1028769 := by exact prefixLift 1028769
  have htrace : WordTrace (prefixWord ++ tailWord_1028769) baseStart_1028769 baseEnd_1028769 := by
    simpa [prefixWord, tailWord_1028769, baseEnd_1028769] using wordTrace_append hprefix tailTrace_1028769
  have hstable : (prefixWord ++ tailWord_1028769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028769).length < 2 ^ (prefixWord ++ tailWord_1028769).sum := by decide
  have hdescent : baseEnd_1028769 < baseStart_1028769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028787 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 6]
def baseStart_1028787 : Nat := 118140960795 + 1028787 * 2 ^ 59
def prefixEnd_1028787 : Nat := 4983230072969 + 3 ^ 40 * 1028787 * 2
def baseEnd_1028787 : Nat := 469566419641930310961067

theorem tailTrace_1028787 : CollatzResearch.WordTrace tailWord_1028787 prefixEnd_1028787 469566419641930310961067 := by
  unfold tailWord_1028787
  simp only [CollatzResearch.WordTrace]
  refine ⟨37522944523887876676292615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25015296349258584450861743 37522944523887876676292615)
  ·
    refine ⟨56284416785831815014438923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37522944523887876676292615 56284416785831815014438923)
    ·
      refine ⟨84426625178747722521658385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56284416785831815014438923 84426625178747722521658385)
      ·
        refine ⟨63319968884060791891243789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84426625178747722521658385 63319968884060791891243789)
        ·
          refine ⟨23744988331522796959216421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63319968884060791891243789 23744988331522796959216421)
          ·
            refine ⟨4452185312160524429853079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23744988331522796959216421 4452185312160524429853079)
            ·
              refine ⟨6678277968240786644779619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4452185312160524429853079 6678277968240786644779619)
              ·
                refine ⟨10017416952361179967169429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6678277968240786644779619 10017416952361179967169429)
                ·
                  refine ⟨469566419641930310961067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10017416952361179967169429 469566419641930310961067)
                  ·
                    rfl

theorem cell20_1028787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_1028787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028787 prefixEnd_1028787 := by exact prefixLift 1028787
  have htrace : WordTrace (prefixWord ++ tailWord_1028787) baseStart_1028787 baseEnd_1028787 := by
    simpa [prefixWord, tailWord_1028787, baseEnd_1028787] using wordTrace_append hprefix tailTrace_1028787
  have hstable : (prefixWord ++ tailWord_1028787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028787).length < 2 ^ (prefixWord ++ tailWord_1028787).sum := by decide
  have hdescent : baseEnd_1028787 < baseStart_1028787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028814 : List Nat := [4, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_1028814 : Nat := 118140960795 + 1028814 * 2 ^ 59
def prefixEnd_1028814 : Nat := 4983230072969 + 3 ^ 40 * 1028814 * 2
def baseEnd_1028814 : Nat := 469578743177638217060957

theorem tailTrace_1028814 : CollatzResearch.WordTrace tailWord_1028814 prefixEnd_1028814 469578743177638217060957 := by
  unfold tailWord_1028814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4690491161848757535940687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25015952863193373525016997 4690491161848757535940687)
  ·
    refine ⟨7035736742773136303911031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4690491161848757535940687 7035736742773136303911031)
    ·
      refine ⟨10553605114159704455866547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7035736742773136303911031 10553605114159704455866547)
      ·
        refine ⟨15830407671239556683799821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10553605114159704455866547 15830407671239556683799821)
        ·
          refine ⟨5936402876714833756424933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15830407671239556683799821 5936402876714833756424933)
          ·
            refine ⟨1113075539384031329329675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5936402876714833756424933 1113075539384031329329675)
            ·
              refine ⟨1669613309076046993994513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1113075539384031329329675 1669613309076046993994513)
              ·
                refine ⟨1252209981807035245495885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1669613309076046993994513 1252209981807035245495885)
                ·
                  refine ⟨469578743177638217060957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1252209981807035245495885 469578743177638217060957)
                  ·
                    rfl

theorem cell20_1028814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_1028814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028814 prefixEnd_1028814 := by exact prefixLift 1028814
  have htrace : WordTrace (prefixWord ++ tailWord_1028814) baseStart_1028814 baseEnd_1028814 := by
    simpa [prefixWord, tailWord_1028814, baseEnd_1028814] using wordTrace_append hprefix tailTrace_1028814
  have hstable : (prefixWord ++ tailWord_1028814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028814).length < 2 ^ (prefixWord ++ tailWord_1028814).sum := by decide
  have hdescent : baseEnd_1028814 < baseStart_1028814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028832 : List Nat := [2, 1, 1, 3, 1, 2, 1, 9]
def baseStart_1028832 : Nat := 118140960795 + 1028832 * 2 ^ 59
def prefixEnd_1028832 : Nat := 4983230072969 + 3 ^ 40 * 1028832 * 2
def baseEnd_1028832 : Nat := 156528986289370051486961

theorem tailTrace_1028832 : CollatzResearch.WordTrace tailWord_1028832 prefixEnd_1028832 156528986289370051486961 := by
  unfold tailWord_1028832
  simp only [CollatzResearch.WordTrace]
  refine ⟨18762292904362424680840375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25016390539149899574453833 18762292904362424680840375)
  ·
    refine ⟨28143439356543637021260563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18762292904362424680840375 28143439356543637021260563)
    ·
      refine ⟨42215159034815455531890845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28143439356543637021260563 42215159034815455531890845)
      ·
        refine ⟨15830684638055795824459067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42215159034815455531890845 15830684638055795824459067)
        ·
          refine ⟨23746026957083693736688601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15830684638055795824459067 23746026957083693736688601)
          ·
            refine ⟨17809520217812770302516451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23746026957083693736688601 17809520217812770302516451)
            ·
              refine ⟨26714280326719155453774677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17809520217812770302516451 26714280326719155453774677)
              ·
                refine ⟨156528986289370051486961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26714280326719155453774677 156528986289370051486961)
                ·
                  rfl

theorem cell20_1028832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_1028832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028832 prefixEnd_1028832 := by exact prefixLift 1028832
  have htrace : WordTrace (prefixWord ++ tailWord_1028832) baseStart_1028832 baseEnd_1028832 := by
    simpa [prefixWord, tailWord_1028832, baseEnd_1028832] using wordTrace_append hprefix tailTrace_1028832
  have hstable : (prefixWord ++ tailWord_1028832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028832).length < 2 ^ (prefixWord ++ tailWord_1028832).sum := by decide
  have hdescent : baseEnd_1028832 < baseStart_1028832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028866 : List Nat := [3, 4, 1, 1, 1, 4, 6]
def baseStart_1028866 : Nat := 118140960795 + 1028866 * 2 ^ 59
def prefixEnd_1028866 : Nat := 4983230072969 + 3 ^ 40 * 1028866 * 2
def baseEnd_1028866 : Nat := 52178053043839683036379

theorem tailTrace_1028866 : CollatzResearch.WordTrace tailWord_1028866 prefixEnd_1028866 52178053043839683036379 := by
  unfold tailWord_1028866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9381456472650418292104613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25017217260401115445612301 9381456472650418292104613)
  ·
    refine ⟨1759023088621953429769615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9381456472650418292104613 1759023088621953429769615)
    ·
      refine ⟨2638534632932930144654423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1759023088621953429769615 2638534632932930144654423)
      ·
        refine ⟨3957801949399395216981635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2638534632932930144654423 3957801949399395216981635)
        ·
          refine ⟨5936702924099092825472453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3957801949399395216981635 5936702924099092825472453)
          ·
            refine ⟨1113131798268579904776085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5936702924099092825472453 1113131798268579904776085)
            ·
              refine ⟨52178053043839683036379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1113131798268579904776085 52178053043839683036379)
              ·
                rfl

theorem cell20_1028866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 6].length) (baseStart_1028866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028866 prefixEnd_1028866 := by exact prefixLift 1028866
  have htrace : WordTrace (prefixWord ++ tailWord_1028866) baseStart_1028866 baseEnd_1028866 := by
    simpa [prefixWord, tailWord_1028866, baseEnd_1028866] using wordTrace_append hprefix tailTrace_1028866
  have hstable : (prefixWord ++ tailWord_1028866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028866).length < 2 ^ (prefixWord ++ tailWord_1028866).sum := by decide
  have hdescent : baseEnd_1028866 < baseStart_1028866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028901 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 6]
def baseStart_1028901 : Nat := 118140960795 + 1028901 * 2 ^ 59
def prefixEnd_1028901 : Nat := 4983230072969 + 3 ^ 40 * 1028901 * 2
def baseEnd_1028901 : Nat := 469618452348252581160601

theorem tailTrace_1028901 : CollatzResearch.WordTrace tailWord_1028901 prefixEnd_1028901 469618452348252581160601 := by
  unfold tailWord_1028901
  simp only [CollatzResearch.WordTrace]
  refine ⟨37527102445474874145942557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25018068296983249430628371 37527102445474874145942557)
  ·
    refine ⟨14072663417053077804728459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37527102445474874145942557 14072663417053077804728459)
    ·
      refine ⟨21108995125579616707092689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14072663417053077804728459 21108995125579616707092689)
      ·
        refine ⟨15831746344184712530319517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21108995125579616707092689 15831746344184712530319517)
        ·
          refine ⟨5936904879069267198869819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15831746344184712530319517 5936904879069267198869819)
          ·
            refine ⟨8905357318603900798304729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5936904879069267198869819 8905357318603900798304729)
            ·
              refine ⟨6679017988952925598728547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8905357318603900798304729 6679017988952925598728547)
              ·
                refine ⟨10018526983429388398092821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6679017988952925598728547 10018526983429388398092821)
                ·
                  refine ⟨469618452348252581160601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10018526983429388398092821 469618452348252581160601)
                  ·
                    rfl

theorem cell20_1028901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_1028901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028901 prefixEnd_1028901 := by exact prefixLift 1028901
  have htrace : WordTrace (prefixWord ++ tailWord_1028901) baseStart_1028901 baseEnd_1028901 := by
    simpa [prefixWord, tailWord_1028901, baseEnd_1028901] using wordTrace_append hprefix tailTrace_1028901
  have hstable : (prefixWord ++ tailWord_1028901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028901).length < 2 ^ (prefixWord ++ tailWord_1028901).sum := by decide
  have hdescent : baseEnd_1028901 < baseStart_1028901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028908 : List Nat := [2, 2, 1, 1, 1, 4, 1, 8]
def baseStart_1028908 : Nat := 118140960795 + 1028908 * 2 ^ 59
def prefixEnd_1028908 : Nat := 4983230072969 + 3 ^ 40 * 1028908 * 2
def baseEnd_1028908 : Nat := 156540549112997222642413

theorem tailTrace_1028908 : CollatzResearch.WordTrace tailWord_1028908 prefixEnd_1028908 156540549112997222642413 := by
  unfold tailWord_1028908
  simp only [CollatzResearch.WordTrace]
  refine ⟨18763678878224757170723689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25018238504299676227631585 18763678878224757170723689)
  ·
    refine ⟨14072759158668567878042767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18763678878224757170723689 14072759158668567878042767)
    ·
      refine ⟨21109138738002851817064151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14072759158668567878042767 21109138738002851817064151)
      ·
        refine ⟨31663708107004277725596227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21109138738002851817064151 31663708107004277725596227)
        ·
          refine ⟨47495562160506416588394341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31663708107004277725596227 47495562160506416588394341)
          ·
            refine ⟨8905417905094953110323939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47495562160506416588394341 8905417905094953110323939)
            ·
              refine ⟨13358126857642429665485909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8905417905094953110323939 13358126857642429665485909)
              ·
                refine ⟨156540549112997222642413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13358126857642429665485909 156540549112997222642413)
                ·
                  rfl

theorem cell20_1028908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_1028908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028908 prefixEnd_1028908 := by exact prefixLift 1028908
  have htrace : WordTrace (prefixWord ++ tailWord_1028908) baseStart_1028908 baseEnd_1028908 := by
    simpa [prefixWord, tailWord_1028908, baseEnd_1028908] using wordTrace_append hprefix tailTrace_1028908
  have hstable : (prefixWord ++ tailWord_1028908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028908).length < 2 ^ (prefixWord ++ tailWord_1028908).sum := by decide
  have hdescent : baseEnd_1028908 < baseStart_1028908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028925 : List Nat := [1, 4, 1, 4, 2, 8]
def baseStart_1028925 : Nat := 118140960795 + 1028925 * 2 ^ 59
def prefixEnd_1028925 : Nat := 4983230072969 + 3 ^ 40 * 1028925 * 2
def baseEnd_1028925 : Nat := 17393681726007969050389

theorem tailTrace_1028925 : CollatzResearch.WordTrace tailWord_1028925 prefixEnd_1028925 17393681726007969050389 := by
  unfold tailWord_1028925
  simp only [CollatzResearch.WordTrace]
  refine ⟨37527977797387926244816229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25018651864925284163210819 37527977797387926244816229)
  ·
    refine ⟨7036495837010236170903043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37527977797387926244816229 7036495837010236170903043)
    ·
      refine ⟨10554743755515354256354565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7036495837010236170903043 10554743755515354256354565)
      ·
        refine ⟨1979014454159128923066481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10554743755515354256354565 1979014454159128923066481)
        ·
          refine ⟨1484260840619346692299861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1979014454159128923066481 1484260840619346692299861)
          ·
            refine ⟨17393681726007969050389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1484260840619346692299861 17393681726007969050389)
            ·
              rfl

theorem cell20_1028925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 8].length) (baseStart_1028925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028925 prefixEnd_1028925 := by exact prefixLift 1028925
  have htrace : WordTrace (prefixWord ++ tailWord_1028925) baseStart_1028925 baseEnd_1028925 := by
    simpa [prefixWord, tailWord_1028925, baseEnd_1028925] using wordTrace_append hprefix tailTrace_1028925
  have hstable : (prefixWord ++ tailWord_1028925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028925).length < 2 ^ (prefixWord ++ tailWord_1028925).sum := by decide
  have hdescent : baseEnd_1028925 < baseStart_1028925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028956 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 6]
def baseStart_1028956 : Nat := 118140960795 + 1028956 * 2 ^ 59
def prefixEnd_1028956 : Nat := 4983230072969 + 3 ^ 40 * 1028956 * 2
def baseEnd_1028956 : Nat := 469643555846916834327043

theorem tailTrace_1028956 : CollatzResearch.WordTrace tailWord_1028956 prefixEnd_1028956 469643555846916834327043 := by
  unfold tailWord_1028956
  simp only [CollatzResearch.WordTrace]
  refine ⟨18764554230137809269597361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25019405640183745692796481 18764554230137809269597361)
  ·
    refine ⟨14073415672603356952198021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18764554230137809269597361 14073415672603356952198021)
    ·
      refine ⟨2638765438613129428537129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14073415672603356952198021 2638765438613129428537129)
      ·
        refine ⟨1979074078959847071402847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2638765438613129428537129 1979074078959847071402847)
        ·
          refine ⟨2968611118439770607104271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979074078959847071402847 2968611118439770607104271)
          ·
            refine ⟨4452916677659655910656407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968611118439770607104271 4452916677659655910656407)
            ·
              refine ⟨6679375016489483865984611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4452916677659655910656407 6679375016489483865984611)
              ·
                refine ⟨10019062524734225798976917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6679375016489483865984611 10019062524734225798976917)
                ·
                  refine ⟨469643555846916834327043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10019062524734225798976917 469643555846916834327043)
                  ·
                    rfl

theorem cell20_1028956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_1028956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028956 prefixEnd_1028956 := by exact prefixLift 1028956
  have htrace : WordTrace (prefixWord ++ tailWord_1028956) baseStart_1028956 baseEnd_1028956 := by
    simpa [prefixWord, tailWord_1028956, baseEnd_1028956] using wordTrace_append hprefix tailTrace_1028956
  have hstable : (prefixWord ++ tailWord_1028956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028956).length < 2 ^ (prefixWord ++ tailWord_1028956).sum := by decide
  have hdescent : baseEnd_1028956 < baseStart_1028956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028990 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_1028990 : Nat := 118140960795 + 1028990 * 2 ^ 59
def prefixEnd_1028990 : Nat := 4983230072969 + 3 ^ 40 * 1028990 * 2
def baseEnd_1028990 : Nat := 469659074373363827193571

theorem tailTrace_1028990 : CollatzResearch.WordTrace tailWord_1028990 prefixEnd_1028990 469659074373363827193571 := by
  unfold tailWord_1028990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4691293567769055293241553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25020232361434961563954949 4691293567769055293241553)
  ·
    refine ⟨3518470175826791469931165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4691293567769055293241553 3518470175826791469931165)
    ·
      refine ⟨1319426315935046801224187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3518470175826791469931165 1319426315935046801224187)
      ·
        refine ⟨1979139473902570201836281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1319426315935046801224187 1979139473902570201836281)
        ·
          refine ⟨1484354605426927651377211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1979139473902570201836281 1484354605426927651377211)
          ·
            refine ⟨2226531908140391477065817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1484354605426927651377211 2226531908140391477065817)
            ·
              refine ⟨1669898931105293607799363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2226531908140391477065817 1669898931105293607799363)
              ·
                refine ⟨2504848396657940411699045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669898931105293607799363 2504848396657940411699045)
                ·
                  refine ⟨469659074373363827193571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2504848396657940411699045 469659074373363827193571)
                  ·
                    rfl

theorem cell20_1028990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_1028990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1028990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1028990 prefixEnd_1028990 := by exact prefixLift 1028990
  have htrace : WordTrace (prefixWord ++ tailWord_1028990) baseStart_1028990 baseEnd_1028990 := by
    simpa [prefixWord, tailWord_1028990, baseEnd_1028990] using wordTrace_append hprefix tailTrace_1028990
  have hstable : (prefixWord ++ tailWord_1028990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028990).length < 2 ^ (prefixWord ++ tailWord_1028990).sum := by decide
  have hdescent : baseEnd_1028990 < baseStart_1028990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029014 : List Nat := [5, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1029014 : Nat := 118140960795 + 1029014 * 2 ^ 59
def prefixEnd_1029014 : Nat := 4983230072969 + 3 ^ 40 * 1029014 * 2
def baseEnd_1029014 : Nat := 156556676209108803464491

theorem tailTrace_1029014 : CollatzResearch.WordTrace tailWord_1029014 prefixEnd_1029014 156556676209108803464491 := by
  unfold tailWord_1029014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2345701493379093402800381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25020815929376996296537397 2345701493379093402800381)
  ·
    refine ⟨879638060017160026050143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2345701493379093402800381 879638060017160026050143)
    ·
      refine ⟨1319457090025740039075215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 879638060017160026050143 1319457090025740039075215)
      ·
        refine ⟨1979185635038610058612823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1319457090025740039075215 1979185635038610058612823)
        ·
          refine ⟨2968778452557915087919235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979185635038610058612823 2968778452557915087919235)
          ·
            refine ⟨4453167678836872631878853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968778452557915087919235 4453167678836872631878853)
            ·
              refine ⟨834968939781913618477285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4453167678836872631878853 834968939781913618477285)
              ·
                refine ⟨156556676209108803464491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 834968939781913618477285 156556676209108803464491)
                ·
                  rfl

theorem cell20_1029014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1029014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029014 prefixEnd_1029014 := by exact prefixLift 1029014
  have htrace : WordTrace (prefixWord ++ tailWord_1029014) baseStart_1029014 baseEnd_1029014 := by
    simpa [prefixWord, tailWord_1029014, baseEnd_1029014] using wordTrace_append hprefix tailTrace_1029014
  have hstable : (prefixWord ++ tailWord_1029014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029014).length < 2 ^ (prefixWord ++ tailWord_1029014).sum := by decide
  have hdescent : baseEnd_1029014 < baseStart_1029014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029015 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 4]
def baseStart_1029015 : Nat := 118140960795 + 1029015 * 2 ^ 59
def prefixEnd_1029015 : Nat := 4983230072969 + 3 ^ 40 * 1029015 * 2
def baseEnd_1029015 : Nat := 469670485054574851360135

theorem tailTrace_1029015 : CollatzResearch.WordTrace tailWord_1029015 prefixEnd_1029015 469670485054574851360135 := by
  unfold tailWord_1029015
  simp only [CollatzResearch.WordTrace]
  refine ⟨37531260367061871615592499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25020840244707914410394999 37531260367061871615592499)
  ·
    refine ⟨56296890550592807423388749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37531260367061871615592499 56296890550592807423388749)
    ·
      refine ⟨21111333956472302783770781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56296890550592807423388749 21111333956472302783770781)
      ·
        refine ⟨7916750233677113543914043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21111333956472302783770781 7916750233677113543914043)
        ·
          refine ⟨11875125350515670315871065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7916750233677113543914043 11875125350515670315871065)
          ·
            refine ⟨8906344012886752736903299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11875125350515670315871065 8906344012886752736903299)
            ·
              refine ⟨13359516019330129105354949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8906344012886752736903299 13359516019330129105354949)
              ·
                refine ⟨2504909253624399207254053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13359516019330129105354949 2504909253624399207254053)
                ·
                  refine ⟨469670485054574851360135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2504909253624399207254053 469670485054574851360135)
                  ·
                    rfl

theorem cell20_1029015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_1029015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029015 prefixEnd_1029015 := by exact prefixLift 1029015
  have htrace : WordTrace (prefixWord ++ tailWord_1029015) baseStart_1029015 baseEnd_1029015 := by
    simpa [prefixWord, tailWord_1029015, baseEnd_1029015] using wordTrace_append hprefix tailTrace_1029015
  have hstable : (prefixWord ++ tailWord_1029015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029015).length < 2 ^ (prefixWord ++ tailWord_1029015).sum := by decide
  have hdescent : baseEnd_1029015 < baseStart_1029015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029063 : List Nat := [1, 1, 4, 1, 1, 2, 6, 1, 3]
def baseStart_1029063 : Nat := 118140960795 + 1029063 * 2 ^ 59
def prefixEnd_1029063 : Nat := 4983230072969 + 3 ^ 40 * 1029063 * 2
def baseEnd_1029063 : Nat := 469692393562500017759939

theorem tailTrace_1029063 : CollatzResearch.WordTrace tailWord_1029063 prefixEnd_1029063 469692393562500017759939 := by
  unfold tailWord_1029063
  simp only [CollatzResearch.WordTrace]
  refine ⟨37533011070887975813339843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25022007380591983875559895 37533011070887975813339843)
  ·
    refine ⟨56299516606331963720009765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37533011070887975813339843 56299516606331963720009765)
    ·
      refine ⟨10556159363687243197501831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56299516606331963720009765 10556159363687243197501831)
      ·
        refine ⟨15834239045530864796252747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10556159363687243197501831 15834239045530864796252747)
        ·
          refine ⟨23751358568296297194379121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15834239045530864796252747 23751358568296297194379121)
          ·
            refine ⟨17813518926222222895784341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23751358568296297194379121 17813518926222222895784341)
            ·
              refine ⟨835008699666666698239891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17813518926222222895784341 835008699666666698239891)
              ·
                refine ⟨1252513049500000047359837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 835008699666666698239891 1252513049500000047359837)
                ·
                  refine ⟨469692393562500017759939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1252513049500000047359837 469692393562500017759939)
                  ·
                    rfl

theorem cell20_1029063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 3].length) (baseStart_1029063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029063 prefixEnd_1029063 := by exact prefixLift 1029063
  have htrace : WordTrace (prefixWord ++ tailWord_1029063) baseStart_1029063 baseEnd_1029063 := by
    simpa [prefixWord, tailWord_1029063, baseEnd_1029063] using wordTrace_append hprefix tailTrace_1029063
  have hstable : (prefixWord ++ tailWord_1029063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029063).length < 2 ^ (prefixWord ++ tailWord_1029063).sum := by decide
  have hdescent : baseEnd_1029063 < baseStart_1029063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029098 : List Nat := [3, 1, 3, 1, 2, 10]
def baseStart_1029098 : Nat := 118140960795 + 1029098 * 2 ^ 59
def prefixEnd_1029098 : Nat := 4983230072969 + 3 ^ 40 * 1029098 * 2
def baseEnd_1029098 : Nat := 17396606241340572281227

theorem tailTrace_1029098 : CollatzResearch.WordTrace tailWord_1029098 prefixEnd_1029098 17396606241340572281227 := by
  unfold tailWord_1029098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9383571906440294197715987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25022858417174117860575965 9383571906440294197715987)
  ·
    refine ⟨14075357859660441296573981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9383571906440294197715987 14075357859660441296573981)
    ·
      refine ⟨5278259197372665486215243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14075357859660441296573981 5278259197372665486215243)
      ·
        refine ⟨7917388796058998229322865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5278259197372665486215243 7917388796058998229322865)
        ·
          refine ⟨5938041597044248671992149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7917388796058998229322865 5938041597044248671992149)
          ·
            refine ⟨17396606241340572281227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5938041597044248671992149 17396606241340572281227)
            ·
              rfl

theorem cell20_1029098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 10].length) (baseStart_1029098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029098 prefixEnd_1029098 := by exact prefixLift 1029098
  have htrace : WordTrace (prefixWord ++ tailWord_1029098) baseStart_1029098 baseEnd_1029098 := by
    simpa [prefixWord, tailWord_1029098, baseEnd_1029098] using wordTrace_append hprefix tailTrace_1029098
  have hstable : (prefixWord ++ tailWord_1029098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029098).length < 2 ^ (prefixWord ++ tailWord_1029098).sum := by decide
  have hdescent : baseEnd_1029098 < baseStart_1029098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029138 : List Nat := [3, 2, 5, 1, 1, 1, 2, 3, 2]
def baseStart_1029138 : Nat := 118140960795 + 1029138 * 2 ^ 59
def prefixEnd_1029138 : Nat := 4983230072969 + 3 ^ 40 * 1029138 * 2
def baseEnd_1029138 : Nat := 469726625606133090259633

theorem tailTrace_1029138 : CollatzResearch.WordTrace tailWord_1029138 prefixEnd_1029138 469726625606133090259633 := by
  unfold tailWord_1029138
  simp only [CollatzResearch.WordTrace]
  refine ⟨9383936636404065905580017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25023831030410842414880045 9383936636404065905580017)
  ·
    refine ⟨7037952477303049429185013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9383936636404065905580017 7037952477303049429185013)
    ·
      refine ⟨659808044747160883986095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7037952477303049429185013 659808044747160883986095)
      ·
        refine ⟨989712067120741325979143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659808044747160883986095 989712067120741325979143)
        ·
          refine ⟨1484568100681111988968715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989712067120741325979143 1484568100681111988968715)
          ·
            refine ⟨2226852151021667983453073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1484568100681111988968715 2226852151021667983453073)
            ·
              refine ⟨1670139113266250987589805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2226852151021667983453073 1670139113266250987589805)
              ·
                refine ⟨626302167474844120346177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1670139113266250987589805 626302167474844120346177)
                ·
                  refine ⟨469726625606133090259633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626302167474844120346177 469726625606133090259633)
                  ·
                    rfl

theorem cell20_1029138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_1029138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029138 prefixEnd_1029138 := by exact prefixLift 1029138
  have htrace : WordTrace (prefixWord ++ tailWord_1029138) baseStart_1029138 baseEnd_1029138 := by
    simpa [prefixWord, tailWord_1029138, baseEnd_1029138] using wordTrace_append hprefix tailTrace_1029138
  have hstable : (prefixWord ++ tailWord_1029138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029138).length < 2 ^ (prefixWord ++ tailWord_1029138).sum := by decide
  have hdescent : baseEnd_1029138 < baseStart_1029138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029156 : List Nat := [2, 3, 1, 4, 1, 3, 1, 2, 3]
def baseStart_1029156 : Nat := 118140960795 + 1029156 * 2 ^ 59
def prefixEnd_1029156 : Nat := 4983230072969 + 3 ^ 40 * 1029156 * 2
def baseEnd_1029156 : Nat := 469734841296605027659559

theorem tailTrace_1029156 : CollatzResearch.WordTrace tailWord_1029156 prefixEnd_1029156 469734841296605027659559 := by
  unfold tailWord_1029156
  simp only [CollatzResearch.WordTrace]
  refine ⟨18768201529775526348237661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25024268706367368464316881 18768201529775526348237661)
  ·
    refine ⟨7038075573665822380589123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18768201529775526348237661 7038075573665822380589123)
    ·
      refine ⟨10557113360498733570883685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7038075573665822380589123 10557113360498733570883685)
      ·
        refine ⟨1979458755093512544540691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10557113360498733570883685 1979458755093512544540691)
        ·
          refine ⟨2969188132640268816811037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979458755093512544540691 2969188132640268816811037)
          ·
            refine ⟨1113445549740100806304139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2969188132640268816811037 1113445549740100806304139)
            ·
              refine ⟨1670168324610151209456209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1113445549740100806304139 1670168324610151209456209)
              ·
                refine ⟨1252626243457613407092157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670168324610151209456209 1252626243457613407092157)
                ·
                  refine ⟨469734841296605027659559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1252626243457613407092157 469734841296605027659559)
                  ·
                    rfl

theorem cell20_1029156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_1029156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029156 prefixEnd_1029156 := by exact prefixLift 1029156
  have htrace : WordTrace (prefixWord ++ tailWord_1029156) baseStart_1029156 baseEnd_1029156 := by
    simpa [prefixWord, tailWord_1029156, baseEnd_1029156] using wordTrace_append hprefix tailTrace_1029156
  have hstable : (prefixWord ++ tailWord_1029156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029156).length < 2 ^ (prefixWord ++ tailWord_1029156).sum := by decide
  have hdescent : baseEnd_1029156 < baseStart_1029156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029191 : List Nat := [1, 1, 4, 1, 3, 2, 4, 4]
def baseStart_1029191 : Nat := 118140960795 + 1029191 * 2 ^ 59
def prefixEnd_1029191 : Nat := 4983230072969 + 3 ^ 40 * 1029191 * 2
def baseEnd_1029191 : Nat := 156583605416766820497583

theorem tailTrace_1029191 : CollatzResearch.WordTrace tailWord_1029191 prefixEnd_1029191 156583605416766820497583 := by
  unfold tailWord_1029191
  simp only [CollatzResearch.WordTrace]
  refine ⟨37537679614424253673999427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25025119742949502449332951 37537679614424253673999427)
  ·
    refine ⟨56306519421636380510999141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37537679614424253673999427 56306519421636380510999141)
    ·
      refine ⟨10557472391556821345812339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56306519421636380510999141 10557472391556821345812339)
      ·
        refine ⟨15836208587335232018718509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10557472391556821345812339 15836208587335232018718509)
        ·
          refine ⟨5938578220250712007019441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15836208587335232018718509 5938578220250712007019441)
          ·
            refine ⟨4453933665188034005264581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5938578220250712007019441 4453933665188034005264581)
            ·
              refine ⟨835112562222756375987109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4453933665188034005264581 835112562222756375987109)
              ·
                refine ⟨156583605416766820497583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 835112562222756375987109 156583605416766820497583)
                ·
                  rfl

theorem cell20_1029191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 4].length) (baseStart_1029191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029191 prefixEnd_1029191 := by exact prefixLift 1029191
  have htrace : WordTrace (prefixWord ++ tailWord_1029191) baseStart_1029191 baseEnd_1029191 := by
    simpa [prefixWord, tailWord_1029191, baseEnd_1029191] using wordTrace_append hprefix tailTrace_1029191
  have hstable : (prefixWord ++ tailWord_1029191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029191).length < 2 ^ (prefixWord ++ tailWord_1029191).sum := by decide
  have hdescent : baseEnd_1029191 < baseStart_1029191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029214 : List Nat := [4, 4, 1, 1, 1, 2, 3, 2, 2]
def baseStart_1029214 : Nat := 118140960795 + 1029214 * 2 ^ 59
def prefixEnd_1029214 : Nat := 4983230072969 + 3 ^ 40 * 1029214 * 2
def baseEnd_1029214 : Nat := 469761314077014603725989

theorem tailTrace_1029214 : CollatzResearch.WordTrace tailWord_1029214 prefixEnd_1029214 469761314077014603725989 := by
  unfold tailWord_1029214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4692314811667616075260837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25025678995560619068057797 4692314811667616075260837)
  ·
    refine ⟨879809027187678014111407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4692314811667616075260837 879809027187678014111407)
    ·
      refine ⟨1319713540781517021167111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 879809027187678014111407 1319713540781517021167111)
      ·
        refine ⟨1979570311172275531750667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1319713540781517021167111 1979570311172275531750667)
        ·
          refine ⟨2969355466758413297626001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979570311172275531750667 2969355466758413297626001)
          ·
            refine ⟨2227016600068809973219501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2969355466758413297626001 2227016600068809973219501)
            ·
              refine ⟨835131225025803739957313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2227016600068809973219501 835131225025803739957313)
              ·
                refine ⟨626348418769352804967985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 835131225025803739957313 626348418769352804967985)
                ·
                  refine ⟨469761314077014603725989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626348418769352804967985 469761314077014603725989)
                  ·
                    rfl

theorem cell20_1029214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_1029214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029214 prefixEnd_1029214 := by exact prefixLift 1029214
  have htrace : WordTrace (prefixWord ++ tailWord_1029214) baseStart_1029214 baseEnd_1029214 := by
    simpa [prefixWord, tailWord_1029214, baseEnd_1029214] using wordTrace_append hprefix tailTrace_1029214
  have hstable : (prefixWord ++ tailWord_1029214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029214).length < 2 ^ (prefixWord ++ tailWord_1029214).sum := by decide
  have hdescent : baseEnd_1029214 < baseStart_1029214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029229 : List Nat := [1, 5, 1, 1, 2, 3, 2, 5]
def baseStart_1029229 : Nat := 118140960795 + 1029229 * 2 ^ 59
def prefixEnd_1029229 : Nat := 4983230072969 + 3 ^ 40 * 1029229 * 2
def baseEnd_1029229 : Nat := 156589386828580406075309

theorem tailTrace_1029229 : CollatzResearch.WordTrace tailWord_1029229 prefixEnd_1029229 156589386828580406075309 := by
  unfold tailWord_1029229
  simp only [CollatzResearch.WordTrace]
  refine ⟨37539065588286586163882741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25026043725524390775921827 37539065588286586163882741)
  ·
    refine ⟨3519287398901867452864007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37539065588286586163882741 3519287398901867452864007)
    ·
      refine ⟨5278931098352801179296011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3519287398901867452864007 5278931098352801179296011)
      ·
        refine ⟨7918396647529201768944017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5278931098352801179296011 7918396647529201768944017)
        ·
          refine ⟨5938797485646901326708013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7918396647529201768944017 5938797485646901326708013)
          ·
            refine ⟨2227049057117587997515505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5938797485646901326708013 2227049057117587997515505)
            ·
              refine ⟨1670286792838190998136629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227049057117587997515505 1670286792838190998136629)
              ·
                refine ⟨156589386828580406075309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1670286792838190998136629 156589386828580406075309)
                ·
                  rfl

theorem cell20_1029229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 5].length) (baseStart_1029229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029229 prefixEnd_1029229 := by exact prefixLift 1029229
  have htrace : WordTrace (prefixWord ++ tailWord_1029229) baseStart_1029229 baseEnd_1029229 := by
    simpa [prefixWord, tailWord_1029229, baseEnd_1029229] using wordTrace_append hprefix tailTrace_1029229
  have hstable : (prefixWord ++ tailWord_1029229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029229).length < 2 ^ (prefixWord ++ tailWord_1029229).sum := by decide
  have hdescent : baseEnd_1029229 < baseStart_1029229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029264 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 8]
def baseStart_1029264 : Nat := 118140960795 + 1029264 * 2 ^ 59
def prefixEnd_1029264 : Nat := 4983230072969 + 3 ^ 40 * 1029264 * 2
def baseEnd_1029264 : Nat := 469784135439436652059117

theorem tailTrace_1029264 : CollatzResearch.WordTrace tailWord_1029264 prefixEnd_1029264 469784135439436652059117 := by
  unfold tailWord_1029264
  simp only [CollatzResearch.WordTrace]
  refine ⟨18770171071579893570703423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25026894762106524760937897 18770171071579893570703423)
  ·
    refine ⟨28155256607369840356055135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18770171071579893570703423 28155256607369840356055135)
    ·
      refine ⟨42232884911054760534082703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28155256607369840356055135 42232884911054760534082703)
      ·
        refine ⟨63349327366582140801124055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42232884911054760534082703 63349327366582140801124055)
        ·
          refine ⟨95023991049873211201686083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63349327366582140801124055 95023991049873211201686083)
          ·
            refine ⟨142535986574809816802529125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95023991049873211201686083 142535986574809816802529125)
            ·
              refine ⟨26725497482776840650474211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142535986574809816802529125 26725497482776840650474211)
              ·
                refine ⟨40088246224165260975711317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26725497482776840650474211 40088246224165260975711317)
                ·
                  refine ⟨469784135439436652059117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40088246224165260975711317 469784135439436652059117)
                  ·
                    rfl

theorem cell20_1029264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_1029264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029264 prefixEnd_1029264 := by exact prefixLift 1029264
  have htrace : WordTrace (prefixWord ++ tailWord_1029264) baseStart_1029264 baseEnd_1029264 := by
    simpa [prefixWord, tailWord_1029264, baseEnd_1029264] using wordTrace_append hprefix tailTrace_1029264
  have hstable : (prefixWord ++ tailWord_1029264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029264).length < 2 ^ (prefixWord ++ tailWord_1029264).sum := by decide
  have hdescent : baseEnd_1029264 < baseStart_1029264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
